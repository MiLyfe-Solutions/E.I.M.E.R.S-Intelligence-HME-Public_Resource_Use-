import V185TrunkScan22Chunk112

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1013129 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_1013129 : Nat := 118140960795 + 1013129 * 2 ^ 59
def prefixEnd_1013129 : Nat := 4983230072969 + 3 ^ 40 * 1013129 * 2
def baseEnd_1013129 : Nat := 346814761339381241218807

theorem tailTrace_1013129 : CollatzResearch.WordTrace tailWord_1013129 prefixEnd_1013129 346814761339381241218807 := by
  unfold tailWord_1013129
  simp only [CollatzResearch.WordTrace]
  refine ⟨36951850346614136502794441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24634566897742757668529627 36951850346614136502794441)
  ·
    refine ⟨27713887759960602377095831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36951850346614136502794441 27713887759960602377095831)
    ·
      refine ⟨41570831639940903565643747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27713887759960602377095831 41570831639940903565643747)
      ·
        refine ⟨62356247459911355348465621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41570831639940903565643747 62356247459911355348465621)
        ·
          refine ⟨1461474549841672390979663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62356247459911355348465621 1461474549841672390979663)
          ·
            refine ⟨2192211824762508586469495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461474549841672390979663 2192211824762508586469495)
            ·
              refine ⟨3288317737143762879704243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192211824762508586469495 3288317737143762879704243)
              ·
                refine ⟨4932476605715644319556365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288317737143762879704243 4932476605715644319556365)
                ·
                  refine ⟨1849678727143366619833637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4932476605715644319556365 1849678727143366619833637)
                  ·
                    refine ⟨346814761339381241218807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1849678727143366619833637 346814761339381241218807)
                    ·
                      rfl

theorem cell22_1013129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_1013129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013129 prefixEnd_1013129 := by exact prefixLift 1013129
  have htrace : WordTrace (prefixWord ++ tailWord_1013129) baseStart_1013129 baseEnd_1013129 := by
    simpa [prefixWord, tailWord_1013129, baseEnd_1013129] using wordTrace_append hprefix tailTrace_1013129
  have hstable : (prefixWord ++ tailWord_1013129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013129).length < 2 ^ (prefixWord ++ tailWord_1013129).sum := by decide
  have hdescent : baseEnd_1013129 < baseStart_1013129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013146 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_1013146 : Nat := 118140960795 + 1013146 * 2 ^ 59
def prefixEnd_1013146 : Nat := 4983230072969 + 3 ^ 40 * 1013146 * 2
def baseEnd_1013146 : Nat := 346820580786798863543755

theorem tailTrace_1013146 : CollatzResearch.WordTrace tailWord_1013146 prefixEnd_1013146 346820580786798863543755 := by
  unfold tailWord_1013146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238117596888137101540823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24634980258368365604108861 9238117596888137101540823)
  ·
    refine ⟨13857176395332205652311235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9238117596888137101540823 13857176395332205652311235)
    ·
      refine ⟨20785764592998308478466853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857176395332205652311235 20785764592998308478466853)
      ·
        refine ⟨3897330861187182839712535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20785764592998308478466853 3897330861187182839712535)
        ·
          refine ⟨5845996291780774259568803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897330861187182839712535 5845996291780774259568803)
          ·
            refine ⟨8768994437671161389353205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5845996291780774259568803 8768994437671161389353205)
            ·
              refine ⟨822093228531671380251863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8768994437671161389353205 822093228531671380251863)
              ·
                refine ⟨1233139842797507070377795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822093228531671380251863 1233139842797507070377795)
                ·
                  refine ⟨1849709764196260605566693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233139842797507070377795 1849709764196260605566693)
                  ·
                    refine ⟨346820580786798863543755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1849709764196260605566693 346820580786798863543755)
                    ·
                      rfl

theorem cell22_1013146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_1013146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013146 prefixEnd_1013146 := by exact prefixLift 1013146
  have htrace : WordTrace (prefixWord ++ tailWord_1013146) baseStart_1013146 baseEnd_1013146 := by
    simpa [prefixWord, tailWord_1013146, baseEnd_1013146] using wordTrace_append hprefix tailTrace_1013146
  have hstable : (prefixWord ++ tailWord_1013146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013146).length < 2 ^ (prefixWord ++ tailWord_1013146).sum := by decide
  have hdescent : baseEnd_1013146 < baseStart_1013146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013157 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_1013157 : Nat := 118140960795 + 1013157 * 2 ^ 59
def prefixEnd_1013157 : Nat := 4983230072969 + 3 ^ 40 * 1013157 * 2
def baseEnd_1013157 : Nat := 346824346311598501518721

theorem tailTrace_1013157 : CollatzResearch.WordTrace tailWord_1013157 prefixEnd_1013157 346824346311598501518721 := by
  unfold tailWord_1013157
  simp only [CollatzResearch.WordTrace]
  refine ⟨36952871590512697284813725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24635247727008464856542483 36952871590512697284813725)
  ·
    refine ⟨13857326846442261481805147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36952871590512697284813725 13857326846442261481805147)
    ·
      refine ⟨20785990269663392222707721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857326846442261481805147 20785990269663392222707721)
      ·
        refine ⟨15589492702247544167030791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20785990269663392222707721 15589492702247544167030791)
        ·
          refine ⟨23384239053371316250546187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589492702247544167030791 23384239053371316250546187)
          ·
            refine ⟨35076358580056974375819281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23384239053371316250546187 35076358580056974375819281)
            ·
              refine ⟨26307268935042730781864461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35076358580056974375819281 26307268935042730781864461)
              ·
                refine ⟨9865225850641024043199173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26307268935042730781864461 9865225850641024043199173)
                ·
                  refine ⟨1849729846995192008099845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9865225850641024043199173 1849729846995192008099845)
                  ·
                    refine ⟨346824346311598501518721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1849729846995192008099845 346824346311598501518721)
                    ·
                      rfl

theorem cell22_1013157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_1013157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013157 prefixEnd_1013157 := by exact prefixLift 1013157
  have htrace : WordTrace (prefixWord ++ tailWord_1013157) baseStart_1013157 baseEnd_1013157 := by
    simpa [prefixWord, tailWord_1013157, baseEnd_1013157] using wordTrace_append hprefix tailTrace_1013157
  have hstable : (prefixWord ++ tailWord_1013157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013157).length < 2 ^ (prefixWord ++ tailWord_1013157).sum := by decide
  have hdescent : baseEnd_1013157 < baseStart_1013157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013221 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 3, 3]
def baseStart_1013221 : Nat := 118140960795 + 1013221 * 2 ^ 59
def prefixEnd_1013221 : Nat := 4983230072969 + 3 ^ 40 * 1013221 * 2
def baseEnd_1013221 : Nat := 346846254819523667918525

theorem tailTrace_1013221 : CollatzResearch.WordTrace tailWord_1013221 prefixEnd_1013221 346846254819523667918525 := by
  unfold tailWord_1013221
  simp only [CollatzResearch.WordTrace]
  refine ⟨36955205862280836215143517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24636803908187224143429011 36955205862280836215143517)
  ·
    refine ⟨13858202198355313580678819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36955205862280836215143517 13858202198355313580678819)
    ·
      refine ⟨20787303297532970371018229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13858202198355313580678819 20787303297532970371018229)
      ·
        refine ⟨1948809684143715972282959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20787303297532970371018229 1948809684143715972282959)
        ·
          refine ⟨2923214526215573958424439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948809684143715972282959 2923214526215573958424439)
          ·
            refine ⟨4384821789323360937636659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923214526215573958424439 4384821789323360937636659)
            ·
              refine ⟨6577232683985041406454989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4384821789323360937636659 6577232683985041406454989)
              ·
                refine ⟨2466462256494390527420621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6577232683985041406454989 2466462256494390527420621)
                ·
                  refine ⟨924923346185396447782733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2466462256494390527420621 924923346185396447782733)
                  ·
                    refine ⟨346846254819523667918525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924923346185396447782733 346846254819523667918525)
                    ·
                      rfl

theorem cell22_1013221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_1013221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013221 prefixEnd_1013221 := by exact prefixLift 1013221
  have htrace : WordTrace (prefixWord ++ tailWord_1013221) baseStart_1013221 baseEnd_1013221 := by
    simpa [prefixWord, tailWord_1013221, baseEnd_1013221] using wordTrace_append hprefix tailTrace_1013221
  have hstable : (prefixWord ++ tailWord_1013221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013221).length < 2 ^ (prefixWord ++ tailWord_1013221).sum := by decide
  have hdescent : baseEnd_1013221 < baseStart_1013221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013255 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 1, 3]
def baseStart_1013255 : Nat := 118140960795 + 1013255 * 2 ^ 59
def prefixEnd_1013255 : Nat := 4983230072969 + 3 ^ 40 * 1013255 * 2
def baseEnd_1013255 : Nat := 346857893714358912568421

theorem tailTrace_1013255 : CollatzResearch.WordTrace tailWord_1013255 prefixEnd_1013255 346857893714358912568421 := by
  unfold tailWord_1013255
  simp only [CollatzResearch.WordTrace]
  refine ⟨36956445944157660021881219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24637630629438440014587479 36956445944157660021881219)
  ·
    refine ⟨55434668916236490032821829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36956445944157660021881219 55434668916236490032821829)
    ·
      refine ⟨10394000421794341881154093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55434668916236490032821829 10394000421794341881154093)
      ·
        refine ⟨3897750158172878205432785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10394000421794341881154093 3897750158172878205432785)
        ·
          refine ⟨2923312618629658654074589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3897750158172878205432785 2923312618629658654074589)
          ·
            refine ⟨1096242231986121995277971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2923312618629658654074589 1096242231986121995277971)
            ·
              refine ⟨1644363347979182992916957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096242231986121995277971 1644363347979182992916957)
              ·
                refine ⟨616636255492193622343859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1644363347979182992916957 616636255492193622343859)
                ·
                  refine ⟨924954383238290433515789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616636255492193622343859 924954383238290433515789)
                  ·
                    refine ⟨346857893714358912568421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 924954383238290433515789 346857893714358912568421)
                    ·
                      rfl

theorem cell22_1013255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_1013255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013255 prefixEnd_1013255 := by exact prefixLift 1013255
  have htrace : WordTrace (prefixWord ++ tailWord_1013255) baseStart_1013255 baseEnd_1013255 := by
    simpa [prefixWord, tailWord_1013255, baseEnd_1013255] using wordTrace_append hprefix tailTrace_1013255
  have hstable : (prefixWord ++ tailWord_1013255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013255).length < 2 ^ (prefixWord ++ tailWord_1013255).sum := by decide
  have hdescent : baseEnd_1013255 < baseStart_1013255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013279 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 6]
def baseStart_1013279 : Nat := 118140960795 + 1013279 * 2 ^ 59
def prefixEnd_1013279 : Nat := 4983230072969 + 3 ^ 40 * 1013279 * 2
def baseEnd_1013279 : Nat := 115622036468276949989449

theorem tailTrace_1013279 : CollatzResearch.WordTrace tailWord_1013279 prefixEnd_1013279 115622036468276949989449 := by
  unfold tailWord_1013279
  simp only [CollatzResearch.WordTrace]
  refine ⟨36957321296070712120754891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24638214197380474747169927 36957321296070712120754891)
  ·
    refine ⟨55435981944106068181132337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36957321296070712120754891 55435981944106068181132337)
    ·
      refine ⟨41576986458079551135849253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55435981944106068181132337 41576986458079551135849253)
      ·
        refine ⟨7795684960889915837971735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41576986458079551135849253 7795684960889915837971735)
        ·
          refine ⟨11693527441334873756957603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7795684960889915837971735 11693527441334873756957603)
          ·
            refine ⟨17540291162002310635436405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693527441334873756957603 17540291162002310635436405)
            ·
              refine ⟨1644402296437716622072163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17540291162002310635436405 1644402296437716622072163)
              ·
                refine ⟨2466603444656574933108245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644402296437716622072163 2466603444656574933108245)
                ·
                  refine ⟨115622036468276949989449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2466603444656574933108245 115622036468276949989449)
                  ·
                    rfl

theorem cell22_1013279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 6].length) (baseStart_1013279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013279 prefixEnd_1013279 := by exact prefixLift 1013279
  have htrace : WordTrace (prefixWord ++ tailWord_1013279) baseStart_1013279 baseEnd_1013279 := by
    simpa [prefixWord, tailWord_1013279, baseEnd_1013279] using wordTrace_append hprefix tailTrace_1013279
  have hstable : (prefixWord ++ tailWord_1013279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013279).length < 2 ^ (prefixWord ++ tailWord_1013279).sum := by decide
  have hdescent : baseEnd_1013279 < baseStart_1013279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013330 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_1013330 : Nat := 118140960795 + 1013330 * 2 ^ 59
def prefixEnd_1013330 : Nat := 4983230072969 + 3 ^ 40 * 1013330 * 2
def baseEnd_1013330 : Nat := 115627855915694572314397

theorem tailTrace_1013330 : CollatzResearch.WordTrace tailWord_1013330 prefixEnd_1013330 115627855915694572314397 := by
  unfold tailWord_1013330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239795354721486957715361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24639454279257298553907629 9239795354721486957715361)
  ·
    refine ⟨6929846516041115218286521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9239795354721486957715361 6929846516041115218286521)
    ·
      refine ⟨5197384887030836413714891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6929846516041115218286521 5197384887030836413714891)
      ·
        refine ⟨7796077330546254620572337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197384887030836413714891 7796077330546254620572337)
        ·
          refine ⟨5847057997909690965429253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7796077330546254620572337 5847057997909690965429253)
          ·
            refine ⟨1096323374608067056017985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5847057997909690965429253 1096323374608067056017985)
            ·
              refine ⟨822242530956050292013489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096323374608067056017985 822242530956050292013489)
              ·
                refine ⟨616681898217037719010117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822242530956050292013489 616681898217037719010117)
                ·
                  refine ⟨115627855915694572314397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616681898217037719010117 115627855915694572314397)
                  ·
                    rfl

theorem cell22_1013330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_1013330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013330 prefixEnd_1013330 := by exact prefixLift 1013330
  have htrace : WordTrace (prefixWord ++ tailWord_1013330) baseStart_1013330 baseEnd_1013330 := by
    simpa [prefixWord, tailWord_1013330, baseEnd_1013330] using wordTrace_append hprefix tailTrace_1013330
  have hstable : (prefixWord ++ tailWord_1013330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013330).length < 2 ^ (prefixWord ++ tailWord_1013330).sum := by decide
  have hdescent : baseEnd_1013330 < baseStart_1013330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013358 : List Nat := [4, 1, 2, 2, 3, 1, 3, 6]
def baseStart_1013358 : Nat := 118140960795 + 1013358 * 2 ^ 59
def prefixEnd_1013358 : Nat := 4983230072969 + 3 ^ 40 * 1013358 * 2
def baseEnd_1013358 : Nat := 38543683635477886360345

theorem tailTrace_1013358 : CollatzResearch.WordTrace tailWord_1013358 prefixEnd_1013358 38543683635477886360345 := by
  unfold tailWord_1013358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620025332848063576610091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24640135108523005741920485 4620025332848063576610091)
  ·
    refine ⟨6930037999272095364915137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620025332848063576610091 6930037999272095364915137)
    ·
      refine ⟨5197528499454071523686353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6930037999272095364915137 5197528499454071523686353)
      ·
        refine ⟨3898146374590553642764765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5197528499454071523686353 3898146374590553642764765)
        ·
          refine ⟨1461804890471457616036787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3898146374590553642764765 1461804890471457616036787)
          ·
            refine ⟨2192707335707186424055181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461804890471457616036787 2192707335707186424055181)
            ·
              refine ⟨822265250890194909020693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2192707335707186424055181 822265250890194909020693)
              ·
                refine ⟨38543683635477886360345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 822265250890194909020693 38543683635477886360345)
                ·
                  rfl

theorem cell22_1013358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_1013358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013358 prefixEnd_1013358 := by exact prefixLift 1013358
  have htrace : WordTrace (prefixWord ++ tailWord_1013358) baseStart_1013358 baseEnd_1013358 := by
    simpa [prefixWord, tailWord_1013358, baseEnd_1013358] using wordTrace_append hprefix tailTrace_1013358
  have hstable : (prefixWord ++ tailWord_1013358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013358).length < 2 ^ (prefixWord ++ tailWord_1013358).sum := by decide
  have hdescent : baseEnd_1013358 < baseStart_1013358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013369 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 7]
def baseStart_1013369 : Nat := 118140960795 + 1013369 * 2 ^ 59
def prefixEnd_1013369 : Nat := 4983230072969 + 3 ^ 40 * 1013369 * 2
def baseEnd_1013369 : Nat := 115632306081366871739357

theorem tailTrace_1013369 : CollatzResearch.WordTrace tailWord_1013369 prefixEnd_1013369 115632306081366871739357 := by
  unfold tailWord_1013369
  simp only [CollatzResearch.WordTrace]
  refine ⟨36960603865744657491531161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24640402577163104994354107 36960603865744657491531161)
  ·
    refine ⟨27720452899308493118648371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36960603865744657491531161 27720452899308493118648371)
    ·
      refine ⟨41580679348962739677972557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27720452899308493118648371 41580679348962739677972557)
      ·
        refine ⟨15592754755861027379239709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41580679348962739677972557 15592754755861027379239709)
        ·
          refine ⟨5847283033447885267214891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15592754755861027379239709 5847283033447885267214891)
          ·
            refine ⟨8770924550171827900822337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847283033447885267214891 8770924550171827900822337)
            ·
              refine ⟨6578193412628870925616753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770924550171827900822337 6578193412628870925616753)
              ·
                refine ⟨4933645059471653194212565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578193412628870925616753 4933645059471653194212565)
                ·
                  refine ⟨115632306081366871739357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4933645059471653194212565 115632306081366871739357)
                  ·
                    rfl

theorem cell22_1013369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_1013369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013369 prefixEnd_1013369 := by exact prefixLift 1013369
  have htrace : WordTrace (prefixWord ++ tailWord_1013369) baseStart_1013369 baseEnd_1013369 := by
    simpa [prefixWord, tailWord_1013369, baseEnd_1013369] using wordTrace_append hprefix tailTrace_1013369
  have hstable : (prefixWord ++ tailWord_1013369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013369).length < 2 ^ (prefixWord ++ tailWord_1013369).sum := by decide
  have hdescent : baseEnd_1013369 < baseStart_1013369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013386 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_1013386 : Nat := 118140960795 + 1013386 * 2 ^ 59
def prefixEnd_1013386 : Nat := 4983230072969 + 3 ^ 40 * 1013386 * 2
def baseEnd_1013386 : Nat := 115634245897172745847673

theorem tailTrace_1013386 : CollatzResearch.WordTrace tailWord_1013386 prefixEnd_1013386 115634245897172745847673 := by
  unfold tailWord_1013386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240305976670767348725003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24640815937788712929933341 9240305976670767348725003)
  ·
    refine ⟨13860458965006151023087505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9240305976670767348725003 13860458965006151023087505)
    ·
      refine ⟨10395344223754613267315629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13860458965006151023087505 10395344223754613267315629)
      ·
        refine ⟨3898254083907979975243361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10395344223754613267315629 3898254083907979975243361)
        ·
          refine ⟨2923690562930984981432521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3898254083907979975243361 2923690562930984981432521)
          ·
            refine ⟨2192767922198238736074391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2923690562930984981432521 2192767922198238736074391)
            ·
              refine ⟨3289151883297358104111587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192767922198238736074391 3289151883297358104111587)
              ·
                refine ⟨4933727824946037156167381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289151883297358104111587 4933727824946037156167381)
                ·
                  refine ⟨115634245897172745847673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4933727824946037156167381 115634245897172745847673)
                  ·
                    rfl

theorem cell22_1013386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_1013386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013386 prefixEnd_1013386 := by exact prefixLift 1013386
  have htrace : WordTrace (prefixWord ++ tailWord_1013386) baseStart_1013386 baseEnd_1013386 := by
    simpa [prefixWord, tailWord_1013386, baseEnd_1013386] using wordTrace_append hprefix tailTrace_1013386
  have hstable : (prefixWord ++ tailWord_1013386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013386).length < 2 ^ (prefixWord ++ tailWord_1013386).sum := by decide
  have hdescent : baseEnd_1013386 < baseStart_1013386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013390 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_1013390 : Nat := 118140960795 + 1013390 * 2 ^ 59
def prefixEnd_1013390 : Nat := 4983230072969 + 3 ^ 40 * 1013390 * 2
def baseEnd_1013390 : Nat := 346904106973263560443007

theorem tailTrace_1013390 : CollatzResearch.WordTrace tailWord_1013390 prefixEnd_1013390 346904106973263560443007 := by
  unfold tailWord_1013390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620171224833572259755703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24640913199112385385363749 4620171224833572259755703)
  ·
    refine ⟨6930256837250358389633555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620171224833572259755703 6930256837250358389633555)
    ·
      refine ⟨10395385255875537584450333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930256837250358389633555 10395385255875537584450333)
      ·
        refine ⟨3898269470953326594168875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10395385255875537584450333 3898269470953326594168875)
        ·
          refine ⟨5847404206429989891253313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898269470953326594168875 5847404206429989891253313)
          ·
            refine ⟨4385553154822492418439985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847404206429989891253313 4385553154822492418439985)
            ·
              refine ⟨3289164866116869313829989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4385553154822492418439985 3289164866116869313829989)
              ·
                refine ⟨616718412396912996343123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3289164866116869313829989 616718412396912996343123)
                ·
                  refine ⟨925077618595369494514685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616718412396912996343123 925077618595369494514685)
                  ·
                    refine ⟨346904106973263560443007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925077618595369494514685 346904106973263560443007)
                    ·
                      rfl

theorem cell22_1013390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_1013390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013390 prefixEnd_1013390 := by exact prefixLift 1013390
  have htrace : WordTrace (prefixWord ++ tailWord_1013390) baseStart_1013390 baseEnd_1013390 := by
    simpa [prefixWord, tailWord_1013390, baseEnd_1013390] using wordTrace_append hprefix tailTrace_1013390
  have hstable : (prefixWord ++ tailWord_1013390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013390).length < 2 ^ (prefixWord ++ tailWord_1013390).sum := by decide
  have hdescent : baseEnd_1013390 < baseStart_1013390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013463 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 2, 3]
def baseStart_1013463 : Nat := 118140960795 + 1013463 * 2 ^ 59
def prefixEnd_1013463 : Nat := 4983230072969 + 3 ^ 40 * 1013463 * 2
def baseEnd_1013463 : Nat := 346929096365115703367783

theorem tailTrace_1013463 : CollatzResearch.WordTrace tailWord_1013463 prefixEnd_1013463 346929096365115703367783 := by
  unfold tailWord_1013463
  simp only [CollatzResearch.WordTrace]
  refine ⟨36964032327404111545453043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24642688218269407696968695 36964032327404111545453043)
  ·
    refine ⟨55446048491106167318179565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36964032327404111545453043 55446048491106167318179565)
    ·
      refine ⟨20792268184164812744317337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55446048491106167318179565 20792268184164812744317337)
      ·
        refine ⟨15594201138123609558238003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20792268184164812744317337 15594201138123609558238003)
        ·
          refine ⟨23391301707185414337357005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15594201138123609558238003 23391301707185414337357005)
          ·
            refine ⟨8771738140194530376508877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23391301707185414337357005 8771738140194530376508877)
            ·
              refine ⟨3289401802572948891190829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8771738140194530376508877 3289401802572948891190829)
              ·
                refine ⟨1233525675964855834196561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3289401802572948891190829 1233525675964855834196561)
                ·
                  refine ⟨925144256973641875647421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1233525675964855834196561 925144256973641875647421)
                  ·
                    refine ⟨346929096365115703367783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925144256973641875647421 346929096365115703367783)
                    ·
                      rfl

theorem cell22_1013463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_1013463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013463 prefixEnd_1013463 := by exact prefixLift 1013463
  have htrace : WordTrace (prefixWord ++ tailWord_1013463) baseStart_1013463 baseEnd_1013463 := by
    simpa [prefixWord, tailWord_1013463, baseEnd_1013463] using wordTrace_append hprefix tailTrace_1013463
  have hstable : (prefixWord ++ tailWord_1013463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013463).length < 2 ^ (prefixWord ++ tailWord_1013463).sum := by decide
  have hdescent : baseEnd_1013463 < baseStart_1013463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013536 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_1013536 : Nat := 118140960795 + 1013536 * 2 ^ 59
def prefixEnd_1013536 : Nat := 4983230072969 + 3 ^ 40 * 1013536 * 2
def baseEnd_1013536 : Nat := 346954085756967846292559

theorem tailTrace_1013536 : CollatzResearch.WordTrace tailWord_1013536 prefixEnd_1013536 346954085756967846292559 := by
  unfold tailWord_1013536
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483347428069822506430231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24644463237426430008573641 18483347428069822506430231)
  ·
    refine ⟨27725021142104733759645347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18483347428069822506430231 27725021142104733759645347)
    ·
      refine ⟨41587531713157100639468021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27725021142104733759645347 41587531713157100639468021)
      ·
        refine ⟨3898831098108478184950127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41587531713157100639468021 3898831098108478184950127)
        ·
          refine ⟨5848246647162717277425191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898831098108478184950127 5848246647162717277425191)
          ·
            refine ⟨8772369970744075916137787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848246647162717277425191 8772369970744075916137787)
            ·
              refine ⟨13158554956116113874206681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772369970744075916137787 13158554956116113874206681)
              ·
                refine ⟨9868916217087085405655011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158554956116113874206681 9868916217087085405655011)
                ·
                  refine ⟨14803374325630628108482517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9868916217087085405655011 14803374325630628108482517)
                  ·
                    refine ⟨346954085756967846292559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14803374325630628108482517 346954085756967846292559)
                    ·
                      rfl

theorem cell22_1013536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_1013536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013536 prefixEnd_1013536 := by exact prefixLift 1013536
  have htrace : WordTrace (prefixWord ++ tailWord_1013536) baseStart_1013536 baseEnd_1013536 := by
    simpa [prefixWord, tailWord_1013536, baseEnd_1013536] using wordTrace_append hprefix tailTrace_1013536
  have hstable : (prefixWord ++ tailWord_1013536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013536).length < 2 ^ (prefixWord ++ tailWord_1013536).sum := by decide
  have hdescent : baseEnd_1013536 < baseStart_1013536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013555 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 5]
def baseStart_1013555 : Nat := 118140960795 + 1013555 * 2 ^ 59
def prefixEnd_1013555 : Nat := 4983230072969 + 3 ^ 40 * 1013555 * 2
def baseEnd_1013555 : Nat := 115653529948419376689167

theorem tailTrace_1013555 : CollatzResearch.WordTrace tailWord_1013555 prefixEnd_1013555 115653529948419376689167 := by
  unfold tailWord_1013555
  simp only [CollatzResearch.WordTrace]
  refine ⟨36967387843070811257802119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24644925228713874171868079 36967387843070811257802119)
  ·
    refine ⟨55451081764606216886703179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36967387843070811257802119 55451081764606216886703179)
    ·
      refine ⟨83176622646909325330054769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55451081764606216886703179 83176622646909325330054769)
      ·
        refine ⟨62382466985181993997541077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83176622646909325330054769 62382466985181993997541077)
        ·
          refine ⟨1462089069965202984317369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62382466985181993997541077 1462089069965202984317369)
          ·
            refine ⟨1096566802473902238238027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462089069965202984317369 1096566802473902238238027)
            ·
              refine ⟨1644850203710853357357041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096566802473902238238027 1644850203710853357357041)
              ·
                refine ⟨1233637652783140018017781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644850203710853357357041 1233637652783140018017781)
                ·
                  refine ⟨115653529948419376689167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1233637652783140018017781 115653529948419376689167)
                  ·
                    rfl

theorem cell22_1013555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 5].length) (baseStart_1013555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013555 prefixEnd_1013555 := by exact prefixLift 1013555
  have htrace : WordTrace (prefixWord ++ tailWord_1013555) baseStart_1013555 baseEnd_1013555 := by
    simpa [prefixWord, tailWord_1013555, baseEnd_1013555] using wordTrace_append hprefix tailTrace_1013555
  have hstable : (prefixWord ++ tailWord_1013555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013555).length < 2 ^ (prefixWord ++ tailWord_1013555).sum := by decide
  have hdescent : baseEnd_1013555 < baseStart_1013555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013585 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_1013585 : Nat := 118140960795 + 1013585 * 2 ^ 59
def prefixEnd_1013585 : Nat := 4983230072969 + 3 ^ 40 * 1013585 * 2
def baseEnd_1013585 : Nat := 346970859458348051817409

theorem tailTrace_1013585 : CollatzResearch.WordTrace tailWord_1013585 prefixEnd_1013585 346970859458348051817409 := by
  unfold tailWord_1013585
  simp only [CollatzResearch.WordTrace]
  refine ⟨36968482032962126381394209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24645654688641417587596139 36968482032962126381394209)
  ·
    refine ⟨27726361524721594786045657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36968482032962126381394209 27726361524721594786045657)
    ·
      refine ⟨20794771143541196089534243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27726361524721594786045657 20794771143541196089534243)
      ·
        refine ⟨31192156715311794134301365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20794771143541196089534243 31192156715311794134301365)
        ·
          refine ⟨2924264692060480700090753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31192156715311794134301365 2924264692060480700090753)
          ·
            refine ⟨2193198519045360525068065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924264692060480700090753 2193198519045360525068065)
            ·
              refine ⟨1644898889284020393801049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193198519045360525068065 1644898889284020393801049)
              ·
                refine ⟨1233674166963015295350787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1644898889284020393801049 1233674166963015295350787)
                ·
                  refine ⟨1850511250444522943026181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233674166963015295350787 1850511250444522943026181)
                  ·
                    refine ⟨346970859458348051817409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1850511250444522943026181 346970859458348051817409)
                    ·
                      rfl

theorem cell22_1013585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_1013585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013585 prefixEnd_1013585 := by exact prefixLift 1013585
  have htrace : WordTrace (prefixWord ++ tailWord_1013585) baseStart_1013585 baseEnd_1013585 := by
    simpa [prefixWord, tailWord_1013585, baseEnd_1013585] using wordTrace_append hprefix tailTrace_1013585
  have hstable : (prefixWord ++ tailWord_1013585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013585).length < 2 ^ (prefixWord ++ tailWord_1013585).sum := by decide
  have hdescent : baseEnd_1013585 < baseStart_1013585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013600 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 4]
def baseStart_1013600 : Nat := 118140960795 + 1013600 * 2 ^ 59
def prefixEnd_1013600 : Nat := 4983230072969 + 3 ^ 40 * 1013600 * 2
def baseEnd_1013600 : Nat := 115658664754964337564121

theorem tailTrace_1013600 : CollatzResearch.WordTrace tailWord_1013600 prefixEnd_1013600 115658664754964337564121 := by
  unfold tailWord_1013600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484514563953891971595127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24646019418605189295460169 18484514563953891971595127)
  ·
    refine ⟨27726771845930837957392691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18484514563953891971595127 27726771845930837957392691)
    ·
      refine ⟨41590157768896256936089037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27726771845930837957392691 41590157768896256936089037)
      ·
        refine ⟨15596309163336096351033389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41590157768896256936089037 15596309163336096351033389)
        ·
          refine ⟨5848615936251036131637521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15596309163336096351033389 5848615936251036131637521)
          ·
            refine ⟨4386461952188277098728141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5848615936251036131637521 4386461952188277098728141)
            ·
              refine ⟨1644923232070603912023053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4386461952188277098728141 1644923232070603912023053)
              ·
                refine ⟨616846212026476467008645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1644923232070603912023053 616846212026476467008645)
                ·
                  refine ⟨115658664754964337564121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 616846212026476467008645 115658664754964337564121)
                  ·
                    rfl

theorem cell22_1013600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_1013600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013600 prefixEnd_1013600 := by exact prefixLift 1013600
  have htrace : WordTrace (prefixWord ++ tailWord_1013600) baseStart_1013600 baseEnd_1013600 := by
    simpa [prefixWord, tailWord_1013600, baseEnd_1013600] using wordTrace_append hprefix tailTrace_1013600
  have hstable : (prefixWord ++ tailWord_1013600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013600).length < 2 ^ (prefixWord ++ tailWord_1013600).sum := by decide
  have hdescent : baseEnd_1013600 < baseStart_1013600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013613 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1013613 : Nat := 118140960795 + 1013613 * 2 ^ 59
def prefixEnd_1013613 : Nat := 4983230072969 + 3 ^ 40 * 1013613 * 2
def baseEnd_1013613 : Nat := 346980444430565312117323

theorem tailTrace_1013613 : CollatzResearch.WordTrace tailWord_1013613 prefixEnd_1013613 346980444430565312117323 := by
  unfold tailWord_1013613
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969503276860687163413493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24646335517907124775608995 36969503276860687163413493)
  ·
    refine ⟨3465890932205689421570015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36969503276860687163413493 3465890932205689421570015)
    ·
      refine ⟨5198836398308534132355023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465890932205689421570015 5198836398308534132355023)
      ·
        refine ⟨7798254597462801198532535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198836398308534132355023 7798254597462801198532535)
        ·
          refine ⟨11697381896194201797798803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798254597462801198532535 11697381896194201797798803)
          ·
            refine ⟨17546072844291302696698205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697381896194201797798803 17546072844291302696698205)
            ·
              refine ⟨6579777316609238511261827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17546072844291302696698205 6579777316609238511261827)
              ·
                refine ⟨9869665974913857766892741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579777316609238511261827 9869665974913857766892741)
                ·
                  refine ⟨1850562370296348331292389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9869665974913857766892741 1850562370296348331292389)
                  ·
                    refine ⟨346980444430565312117323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1850562370296348331292389 346980444430565312117323)
                    ·
                      rfl

theorem cell22_1013613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1013613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013613 prefixEnd_1013613 := by exact prefixLift 1013613
  have htrace : WordTrace (prefixWord ++ tailWord_1013613) baseStart_1013613 baseEnd_1013613 := by
    simpa [prefixWord, tailWord_1013613, baseEnd_1013613] using wordTrace_append hprefix tailTrace_1013613
  have hstable : (prefixWord ++ tailWord_1013613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013613).length < 2 ^ (prefixWord ++ tailWord_1013613).sum := by decide
  have hdescent : baseEnd_1013613 < baseStart_1013613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013643 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 5, 3]
def baseStart_1013643 : Nat := 118140960795 + 1013643 * 2 ^ 59
def prefixEnd_1013643 : Nat := 4983230072969 + 3 ^ 40 * 1013643 * 2
def baseEnd_1013643 : Nat := 346990714043655233867231

theorem tailTrace_1013643 : CollatzResearch.WordTrace tailWord_1013643 prefixEnd_1013643 346990714043655233867231 := by
  unfold tailWord_1013643
  simp only [CollatzResearch.WordTrace]
  refine ⟨36970597466752002287005583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24647064977834668191337055 36970597466752002287005583)
  ·
    refine ⟨55455896200128003430508375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36970597466752002287005583 55455896200128003430508375)
    ·
      refine ⟨83183844300192005145762563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55455896200128003430508375 83183844300192005145762563)
      ·
        refine ⟨124775766450288007718643845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83183844300192005145762563 124775766450288007718643845)
        ·
          refine ⟨23395456209429001447245721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124775766450288007718643845 23395456209429001447245721)
          ·
            refine ⟨17546592157071751085434291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23395456209429001447245721 17546592157071751085434291)
            ·
              refine ⟨26319888235607626628151437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17546592157071751085434291 26319888235607626628151437)
              ·
                refine ⟨9869958088352859985556789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26319888235607626628151437 9869958088352859985556789)
                ·
                  refine ⟨925308570783080623645949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9869958088352859985556789 925308570783080623645949)
                  ·
                    refine ⟨346990714043655233867231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925308570783080623645949 346990714043655233867231)
                    ·
                      rfl

theorem cell22_1013643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 3].length) (baseStart_1013643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013643 prefixEnd_1013643 := by exact prefixLift 1013643
  have htrace : WordTrace (prefixWord ++ tailWord_1013643) baseStart_1013643 baseEnd_1013643 := by
    simpa [prefixWord, tailWord_1013643, baseEnd_1013643] using wordTrace_append hprefix tailTrace_1013643
  have hstable : (prefixWord ++ tailWord_1013643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013643).length < 2 ^ (prefixWord ++ tailWord_1013643).sum := by decide
  have hdescent : baseEnd_1013643 < baseStart_1013643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013662 : List Nat := [4, 3, 1, 3, 2, 9]
def baseStart_1013662 : Nat := 118140960795 + 1013662 * 2 ^ 59
def prefixEnd_1013662 : Nat := 4983230072969 + 3 ^ 40 * 1013662 * 2
def baseEnd_1013662 : Nat := 4283916273233895279533

theorem tailTrace_1013662 : CollatzResearch.WordTrace tailWord_1013662 prefixEnd_1013662 4283916273233895279533 := by
  unfold tailWord_1013662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621411306710396066493405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24647526969122112354631493 4621411306710396066493405)
  ·
    refine ⟨1733029240016398524935027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4621411306710396066493405 1733029240016398524935027)
    ·
      refine ⟨2599543860024597787402541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733029240016398524935027 2599543860024597787402541)
      ·
        refine ⟨974828947509224170275953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2599543860024597787402541 974828947509224170275953)
        ·
          refine ⟨731121710631918127706965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974828947509224170275953 731121710631918127706965)
          ·
            refine ⟨4283916273233895279533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 731121710631918127706965 4283916273233895279533)
            ·
              rfl

theorem cell22_1013662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 9].length) (baseStart_1013662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013662 prefixEnd_1013662 := by exact prefixLift 1013662
  have htrace : WordTrace (prefixWord ++ tailWord_1013662) baseStart_1013662 baseEnd_1013662 := by
    simpa [prefixWord, tailWord_1013662, baseEnd_1013662] using wordTrace_append hprefix tailTrace_1013662
  have hstable : (prefixWord ++ tailWord_1013662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013662).length < 2 ^ (prefixWord ++ tailWord_1013662).sum := by decide
  have hdescent : baseEnd_1013662 < baseStart_1013662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013688 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1013688 : Nat := 118140960795 + 1013688 * 2 ^ 59
def prefixEnd_1013688 : Nat := 4983230072969 + 3 ^ 40 * 1013688 * 2
def baseEnd_1013688 : Nat := 347006118463290116492093

theorem tailTrace_1013688 : CollatzResearch.WordTrace tailWord_1013688 prefixEnd_1013688 347006118463290116492093 := by
  unfold tailWord_1013688
  simp only [CollatzResearch.WordTrace]
  refine ⟨18486119375794487486196859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24648159167725983314929145 18486119375794487486196859)
  ·
    refine ⟨27729179063691731229295289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18486119375794487486196859 27729179063691731229295289)
    ·
      refine ⟨20796884297768798421971467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27729179063691731229295289 20796884297768798421971467)
      ·
        refine ⟨31195326446653197632957201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20796884297768798421971467 31195326446653197632957201)
        ·
          refine ⟨23396494834989898224717901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31195326446653197632957201 23396494834989898224717901)
          ·
            refine ⟨8773685563121211834269213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23396494834989898224717901 8773685563121211834269213)
            ·
              refine ⟨3290132086170454437850955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8773685563121211834269213 3290132086170454437850955)
              ·
                refine ⟨4935198129255681656776433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290132086170454437850955 4935198129255681656776433)
                ·
                  refine ⟨3701398596941761242582325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4935198129255681656776433 3701398596941761242582325)
                  ·
                    refine ⟨347006118463290116492093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3701398596941761242582325 347006118463290116492093)
                    ·
                      rfl

theorem cell22_1013688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1013688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013688 prefixEnd_1013688 := by exact prefixLift 1013688
  have htrace : WordTrace (prefixWord ++ tailWord_1013688) baseStart_1013688 baseEnd_1013688 := by
    simpa [prefixWord, tailWord_1013688, baseEnd_1013688] using wordTrace_append hprefix tailTrace_1013688
  have hstable : (prefixWord ++ tailWord_1013688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013688).length < 2 ^ (prefixWord ++ tailWord_1013688).sum := by decide
  have hdescent : baseEnd_1013688 < baseStart_1013688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013720 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_1013720 : Nat := 118140960795 + 1013720 * 2 ^ 59
def prefixEnd_1013720 : Nat := 4983230072969 + 3 ^ 40 * 1013720 * 2
def baseEnd_1013720 : Nat := 347017072717252699691995

theorem tailTrace_1013720 : CollatzResearch.WordTrace tailWord_1013720 prefixEnd_1013720 347017072717252699691995 := by
  unfold tailWord_1013720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18486702943736522218779307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24648937258315362958372409 18486702943736522218779307)
  ·
    refine ⟨27730054415604783328168961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18486702943736522218779307 27730054415604783328168961)
    ·
      refine ⟨20797540811703587496126721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27730054415604783328168961 20797540811703587496126721)
      ·
        refine ⟨15598155608777690622095041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20797540811703587496126721 15598155608777690622095041)
        ·
          refine ⟨11698616706583267966571281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15598155608777690622095041 11698616706583267966571281)
          ·
            refine ⟨8773962529937450974928461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11698616706583267966571281 8773962529937450974928461)
            ·
              refine ⟨3290235948726544115598173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8773962529937450974928461 3290235948726544115598173)
              ·
                refine ⟨1233838480772454043349315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3290235948726544115598173 1233838480772454043349315)
                ·
                  refine ⟨1850757721158681065023973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233838480772454043349315 1850757721158681065023973)
                  ·
                    refine ⟨347017072717252699691995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1850757721158681065023973 347017072717252699691995)
                    ·
                      rfl

theorem cell22_1013720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_1013720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013720 prefixEnd_1013720 := by exact prefixLift 1013720
  have htrace : WordTrace (prefixWord ++ tailWord_1013720) baseStart_1013720 baseEnd_1013720 := by
    simpa [prefixWord, tailWord_1013720, baseEnd_1013720] using wordTrace_append hprefix tailTrace_1013720
  have hstable : (prefixWord ++ tailWord_1013720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013720).length < 2 ^ (prefixWord ++ tailWord_1013720).sum := by decide
  have hdescent : baseEnd_1013720 < baseStart_1013720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013724 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 7]
def baseStart_1013724 : Nat := 118140960795 + 1013724 * 2 ^ 59
def prefixEnd_1013724 : Nat := 4983230072969 + 3 ^ 40 * 1013724 * 2
def baseEnd_1013724 : Nat := 115672813999666007530661

theorem tailTrace_1013724 : CollatzResearch.WordTrace tailWord_1013724 prefixEnd_1013724 115672813999666007530661 := by
  unfold tailWord_1013724
  simp only [CollatzResearch.WordTrace]
  refine ⟨18486775889729276560352113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24649034519639035413802817 18486775889729276560352113)
  ·
    refine ⟨13865081917296957420264085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18486775889729276560352113 13865081917296957420264085)
    ·
      refine ⟨649925714873294879074879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13865081917296957420264085 649925714873294879074879)
      ·
        refine ⟨974888572309942318612319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649925714873294879074879 974888572309942318612319)
        ·
          refine ⟨1462332858464913477918479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974888572309942318612319 1462332858464913477918479)
          ·
            refine ⟨2193499287697370216877719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462332858464913477918479 2193499287697370216877719)
            ·
              refine ⟨3290248931546055325316579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193499287697370216877719 3290248931546055325316579)
              ·
                refine ⟨4935373397319082987974869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290248931546055325316579 4935373397319082987974869)
                ·
                  refine ⟨115672813999666007530661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4935373397319082987974869 115672813999666007530661)
                  ·
                    rfl

theorem cell22_1013724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_1013724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013724 prefixEnd_1013724 := by exact prefixLift 1013724
  have htrace : WordTrace (prefixWord ++ tailWord_1013724) baseStart_1013724 baseEnd_1013724 := by
    simpa [prefixWord, tailWord_1013724, baseEnd_1013724] using wordTrace_append hprefix tailTrace_1013724
  have hstable : (prefixWord ++ tailWord_1013724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013724).length < 2 ^ (prefixWord ++ tailWord_1013724).sum := by decide
  have hdescent : baseEnd_1013724 < baseStart_1013724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013889 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1013889 : Nat := 118140960795 + 1013889 * 2 ^ 59
def prefixEnd_1013889 : Nat := 4983230072969 + 3 ^ 40 * 1013889 * 2
def baseEnd_1013889 : Nat := 347074924870992592216477

theorem tailTrace_1013889 : CollatzResearch.WordTrace tailWord_1013889 prefixEnd_1013889 347074924870992592216477 := by
  unfold tailWord_1013889
  simp only [CollatzResearch.WordTrace]
  refine ⟨36979569823860786300460721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24653046549240524200307147 36979569823860786300460721)
  ·
    refine ⟨27734677367895589725345541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36979569823860786300460721 27734677367895589725345541)
    ·
      refine ⟨5200252006480423073502289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27734677367895589725345541 5200252006480423073502289)
      ·
        refine ⟨3900189004860317305126717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5200252006480423073502289 3900189004860317305126717)
        ·
          refine ⟨1462570876822618989422519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3900189004860317305126717 1462570876822618989422519)
          ·
            refine ⟨2193856315233928484133779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462570876822618989422519 2193856315233928484133779)
            ·
              refine ⟨3290784472850892726200669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193856315233928484133779 3290784472850892726200669)
              ·
                refine ⟨1234044177319084772325251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3290784472850892726200669 1234044177319084772325251)
                ·
                  refine ⟨1851066265978627158487877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234044177319084772325251 1851066265978627158487877)
                  ·
                    refine ⟨347074924870992592216477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1851066265978627158487877 347074924870992592216477)
                    ·
                      rfl

theorem cell22_1013889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1013889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013889 prefixEnd_1013889 := by exact prefixLift 1013889
  have htrace : WordTrace (prefixWord ++ tailWord_1013889) baseStart_1013889 baseEnd_1013889 := by
    simpa [prefixWord, tailWord_1013889, baseEnd_1013889] using wordTrace_append hprefix tailTrace_1013889
  have hstable : (prefixWord ++ tailWord_1013889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013889).length < 2 ^ (prefixWord ++ tailWord_1013889).sum := by decide
  have hdescent : baseEnd_1013889 < baseStart_1013889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013919 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 1, 5]
def baseStart_1013919 : Nat := 118140960795 + 1013919 * 2 ^ 59
def prefixEnd_1013919 : Nat := 4983230072969 + 3 ^ 40 * 1013919 * 2
def baseEnd_1013919 : Nat := 347085194484082513966385

theorem tailTrace_1013919 : CollatzResearch.WordTrace tailWord_1013919 prefixEnd_1013919 347085194484082513966385 := by
  unfold tailWord_1013919
  simp only [CollatzResearch.WordTrace]
  refine ⟨36980664013752101424052811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24653776009168067616035207 36980664013752101424052811)
  ·
    refine ⟨55470996020628152136079217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36980664013752101424052811 55470996020628152136079217)
    ·
      refine ⟨41603247015471114102059413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55470996020628152136079217 41603247015471114102059413)
      ·
        refine ⟨1950152203850208473534035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41603247015471114102059413 1950152203850208473534035)
        ·
          refine ⟨2925228305775312710301053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950152203850208473534035 2925228305775312710301053)
          ·
            refine ⟨1096960614665742266362895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2925228305775312710301053 1096960614665742266362895)
            ·
              refine ⟨1645440921998613399544343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096960614665742266362895 1645440921998613399544343)
              ·
                refine ⟨2468161382997920099316515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645440921998613399544343 2468161382997920099316515)
                ·
                  refine ⟨3702242074496880148974773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468161382997920099316515 3702242074496880148974773)
                  ·
                    refine ⟨347085194484082513966385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3702242074496880148974773 347085194484082513966385)
                    ·
                      rfl

theorem cell22_1013919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_1013919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013919 prefixEnd_1013919 := by exact prefixLift 1013919
  have htrace : WordTrace (prefixWord ++ tailWord_1013919) baseStart_1013919 baseEnd_1013919 := by
    simpa [prefixWord, tailWord_1013919, baseEnd_1013919] using wordTrace_append hprefix tailTrace_1013919
  have hstable : (prefixWord ++ tailWord_1013919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013919).length < 2 ^ (prefixWord ++ tailWord_1013919).sum := by decide
  have hdescent : baseEnd_1013919 < baseStart_1013919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1013975 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1013975 : Nat := 118140960795 + 1013975 * 2 ^ 59
def prefixEnd_1013975 : Nat := 4983230072969 + 3 ^ 40 * 1013975 * 2
def baseEnd_1013975 : Nat := 347104364428517034566213

theorem tailTrace_1013975 : CollatzResearch.WordTrace tailWord_1013975 prefixEnd_1013975 347104364428517034566213 := by
  unfold tailWord_1013975
  simp only [CollatzResearch.WordTrace]
  refine ⟨36982706501549222988091379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24655137667699481992060919 36982706501549222988091379)
  ·
    refine ⟨55474059752323834482137069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36982706501549222988091379 55474059752323834482137069)
    ·
      refine ⟨20802772407121437930801401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55474059752323834482137069 20802772407121437930801401)
      ·
        refine ⟨15602079305341078448101051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20802772407121437930801401 15602079305341078448101051)
        ·
          refine ⟨23403118958011617672151577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15602079305341078448101051 23403118958011617672151577)
          ·
            refine ⟨17552339218508713254113683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23403118958011617672151577 17552339218508713254113683)
            ·
              refine ⟨26328508827763069881170525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17552339218508713254113683 26328508827763069881170525)
              ·
                refine ⟨9873190810411151205438947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26328508827763069881170525 9873190810411151205438947)
                ·
                  refine ⟨14809786215616726808158421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873190810411151205438947 14809786215616726808158421)
                  ·
                    refine ⟨347104364428517034566213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14809786215616726808158421 347104364428517034566213)
                    ·
                      rfl

theorem cell22_1013975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1013975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1013975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1013975 prefixEnd_1013975 := by exact prefixLift 1013975
  have htrace : WordTrace (prefixWord ++ tailWord_1013975) baseStart_1013975 baseEnd_1013975 := by
    simpa [prefixWord, tailWord_1013975, baseEnd_1013975] using wordTrace_append hprefix tailTrace_1013975
  have hstable : (prefixWord ++ tailWord_1013975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1013975).length < 2 ^ (prefixWord ++ tailWord_1013975).sum := by decide
  have hdescent : baseEnd_1013975 < baseStart_1013975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1013975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014037 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1014037 : Nat := 118140960795 + 1014037 * 2 ^ 59
def prefixEnd_1014037 : Nat := 4983230072969 + 3 ^ 40 * 1014037 * 2
def baseEnd_1014037 : Nat := 347125588295569539516023

theorem tailTrace_1014037 : CollatzResearch.WordTrace tailWord_1014037 prefixEnd_1014037 347125588295569539516023 := by
  unfold tailWord_1014037
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984967827324607576848365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24656645218216405051232243 36984967827324607576848365)
  ·
    refine ⟨13869362935246727841318137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36984967827324607576848365 13869362935246727841318137)
    ·
      refine ⟨10402022201435045880988603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13869362935246727841318137 10402022201435045880988603)
      ·
        refine ⟨15603033302152568821482905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10402022201435045880988603 15603033302152568821482905)
        ·
          refine ⟨11702274976614426616112179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15603033302152568821482905 11702274976614426616112179)
          ·
            refine ⟨17553412464921639924168269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11702274976614426616112179 17553412464921639924168269)
            ·
              refine ⟨6582529674345614971563101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17553412464921639924168269 6582529674345614971563101)
              ·
                refine ⟨2468448627879605614336163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6582529674345614971563101 2468448627879605614336163)
                ·
                  refine ⟨3702672941819408421504245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468448627879605614336163 3702672941819408421504245)
                  ·
                    refine ⟨347125588295569539516023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3702672941819408421504245 347125588295569539516023)
                    ·
                      rfl

theorem cell22_1014037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1014037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014037 prefixEnd_1014037 := by exact prefixLift 1014037
  have htrace : WordTrace (prefixWord ++ tailWord_1014037) baseStart_1014037 baseEnd_1014037 := by
    simpa [prefixWord, tailWord_1014037, baseEnd_1014037] using wordTrace_append hprefix tailTrace_1014037
  have hstable : (prefixWord ++ tailWord_1014037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014037).length < 2 ^ (prefixWord ++ tailWord_1014037).sum := by decide
  have hdescent : baseEnd_1014037 < baseStart_1014037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014101 : List Nat := [1, 3, 2, 2, 4, 2, 2, 6]
def baseStart_1014101 : Nat := 118140960795 + 1014101 * 2 ^ 59
def prefixEnd_1014101 : Nat := 4983230072969 + 3 ^ 40 * 1014101 * 2
def baseEnd_1014101 : Nat := 38571944089277189546203

theorem tailTrace_1014101 : CollatzResearch.WordTrace tailWord_1014101 prefixEnd_1014101 38571944089277189546203 := by
  unfold tailWord_1014101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987302099092746507178157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24658201399395164338118771 36987302099092746507178157)
  ·
    refine ⟨13870238287159779940191809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36987302099092746507178157 13870238287159779940191809)
    ·
      refine ⟨10402678715369834955143857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13870238287159779940191809 10402678715369834955143857)
      ·
        refine ⟨7802009036527376216357893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10402678715369834955143857 7802009036527376216357893)
        ·
          refine ⟨1462876694348883040567105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7802009036527376216357893 1462876694348883040567105)
          ·
            refine ⟨1097157520761662280425329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462876694348883040567105 1097157520761662280425329)
            ·
              refine ⟨822868140571246710318997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097157520761662280425329 822868140571246710318997)
              ·
                refine ⟨38571944089277189546203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 822868140571246710318997 38571944089277189546203)
                ·
                  rfl

theorem cell22_1014101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 6].length) (baseStart_1014101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014101 prefixEnd_1014101 := by exact prefixLift 1014101
  have htrace : WordTrace (prefixWord ++ tailWord_1014101) baseStart_1014101 baseEnd_1014101 := by
    simpa [prefixWord, tailWord_1014101, baseEnd_1014101] using wordTrace_append hprefix tailTrace_1014101
  have hstable : (prefixWord ++ tailWord_1014101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014101).length < 2 ^ (prefixWord ++ tailWord_1014101).sum := by decide
  have hdescent : baseEnd_1014101 < baseStart_1014101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014127 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_1014127 : Nat := 118140960795 + 1014127 * 2 ^ 59
def prefixEnd_1014127 : Nat := 4983230072969 + 3 ^ 40 * 1014127 * 2
def baseEnd_1014127 : Nat := 347156397134839304765747

theorem tailTrace_1014127 : CollatzResearch.WordTrace tailWord_1014127 prefixEnd_1014127 347156397134839304765747 := by
  unfold tailWord_1014127
  simp only [CollatzResearch.WordTrace]
  refine ⟨36988250396998552947624635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24658833597999035298416423 36988250396998552947624635)
  ·
    refine ⟨55482375595497829421436953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36988250396998552947624635 55482375595497829421436953)
    ·
      refine ⟨41611781696623372066077715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55482375595497829421436953 41611781696623372066077715)
      ·
        refine ⟨62417672544935058099116573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41611781696623372066077715 62417672544935058099116573)
        ·
          refine ⟨23406627204350646787168715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62417672544935058099116573 23406627204350646787168715)
          ·
            refine ⟨35109940806525970180753073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23406627204350646787168715 35109940806525970180753073)
            ·
              refine ⟨26332455604894477635564805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35109940806525970180753073 26332455604894477635564805)
              ·
                refine ⟨4937335425917714556668401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26332455604894477635564805 4937335425917714556668401)
                ·
                  refine ⟨3703001569438285917501301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937335425917714556668401 3703001569438285917501301)
                  ·
                    refine ⟨347156397134839304765747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3703001569438285917501301 347156397134839304765747)
                    ·
                      rfl

theorem cell22_1014127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_1014127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014127 prefixEnd_1014127 := by exact prefixLift 1014127
  have htrace : WordTrace (prefixWord ++ tailWord_1014127) baseStart_1014127 baseEnd_1014127 := by
    simpa [prefixWord, tailWord_1014127, baseEnd_1014127] using wordTrace_append hprefix tailTrace_1014127
  have hstable : (prefixWord ++ tailWord_1014127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014127).length < 2 ^ (prefixWord ++ tailWord_1014127).sum := by decide
  have hdescent : baseEnd_1014127 < baseStart_1014127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014133 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 3, 3]
def baseStart_1014133 : Nat := 118140960795 + 1014133 * 2 ^ 59
def prefixEnd_1014133 : Nat := 4983230072969 + 3 ^ 40 * 1014133 * 2
def baseEnd_1014133 : Nat := 347158451057457289115729

theorem tailTrace_1014133 : CollatzResearch.WordTrace tailWord_1014133 prefixEnd_1014133 347158451057457289115729 := by
  unfold tailWord_1014133
  simp only [CollatzResearch.WordTrace]
  refine ⟨36988469234976815972343053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24658979489984543981562035 36988469234976815972343053)
  ·
    refine ⟨13870675963116305989628645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36988469234976815972343053 13870675963116305989628645)
    ·
      refine ⟨2600751743084307373055371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13870675963116305989628645 2600751743084307373055371)
      ·
        refine ⟨3901127614626461059583057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600751743084307373055371 3901127614626461059583057)
        ·
          refine ⟨2925845710969845794687293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3901127614626461059583057 2925845710969845794687293)
          ·
            refine ⟨1097192141613692173007735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2925845710969845794687293 1097192141613692173007735)
            ·
              refine ⟨1645788212420538259511603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097192141613692173007735 1645788212420538259511603)
              ·
                refine ⟨2468682318630807389267405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645788212420538259511603 2468682318630807389267405)
                ·
                  refine ⟨925755869486552770975277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2468682318630807389267405 925755869486552770975277)
                  ·
                    refine ⟨347158451057457289115729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925755869486552770975277 347158451057457289115729)
                    ·
                      rfl

theorem cell22_1014133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_1014133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014133 prefixEnd_1014133 := by exact prefixLift 1014133
  have htrace : WordTrace (prefixWord ++ tailWord_1014133) baseStart_1014133 baseEnd_1014133 := by
    simpa [prefixWord, tailWord_1014133, baseEnd_1014133] using wordTrace_append hprefix tailTrace_1014133
  have hstable : (prefixWord ++ tailWord_1014133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014133).length < 2 ^ (prefixWord ++ tailWord_1014133).sum := by decide
  have hdescent : baseEnd_1014133 < baseStart_1014133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014251 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 3, 3]
def baseStart_1014251 : Nat := 118140960795 + 1014251 * 2 ^ 59
def prefixEnd_1014251 : Nat := 4983230072969 + 3 ^ 40 * 1014251 * 2
def baseEnd_1014251 : Nat := 347198844868944314665367

theorem tailTrace_1014251 : CollatzResearch.WordTrace tailWord_1014251 prefixEnd_1014251 347198844868944314665367 := by
  unfold tailWord_1014251
  simp only [CollatzResearch.WordTrace]
  refine ⟨36992773048549322125138607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24661848699032881416759071 36992773048549322125138607)
  ·
    refine ⟨55489159572823983187707911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36992773048549322125138607 55489159572823983187707911)
    ·
      refine ⟨83233739359235974781561867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55489159572823983187707911 83233739359235974781561867)
      ·
        refine ⟨124850609038853962172342801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83233739359235974781561867 124850609038853962172342801)
        ·
          refine ⟨93637956779140471629257101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124850609038853962172342801 93637956779140471629257101)
          ·
            refine ⟨35114233792177676860971413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93637956779140471629257101 35114233792177676860971413)
            ·
              refine ⟨1645979709008328602858035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35114233792177676860971413 1645979709008328602858035)
              ·
                refine ⟨2468969563512492904287053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645979709008328602858035 2468969563512492904287053)
                ·
                  refine ⟨925863586317184839107645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2468969563512492904287053 925863586317184839107645)
                  ·
                    refine ⟨347198844868944314665367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 925863586317184839107645 347198844868944314665367)
                    ·
                      rfl

theorem cell22_1014251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 3].length) (baseStart_1014251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014251 prefixEnd_1014251 := by exact prefixLift 1014251
  have htrace : WordTrace (prefixWord ++ tailWord_1014251) baseStart_1014251 baseEnd_1014251 := by
    simpa [prefixWord, tailWord_1014251, baseEnd_1014251] using wordTrace_append hprefix tailTrace_1014251
  have hstable : (prefixWord ++ tailWord_1014251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014251).length < 2 ^ (prefixWord ++ tailWord_1014251).sum := by decide
  have hdescent : baseEnd_1014251 < baseStart_1014251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014339 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_1014339 : Nat := 118140960795 + 1014339 * 2 ^ 59
def prefixEnd_1014339 : Nat := 4983230072969 + 3 ^ 40 * 1014339 * 2
def baseEnd_1014339 : Nat := 347228969067341418465097

theorem tailTrace_1014339 : CollatzResearch.WordTrace tailWord_1014339 prefixEnd_1014339 347228969067341418465097 := by
  unfold tailWord_1014339
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995982672230513154342071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24663988448153675436228047 36995982672230513154342071)
  ·
    refine ⟨55493974008345769731513107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36995982672230513154342071 55493974008345769731513107)
    ·
      refine ⟨83240961012518654597269661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55493974008345769731513107 83240961012518654597269661)
      ·
        refine ⟨31215360379694495473976123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83240961012518654597269661 31215360379694495473976123)
        ·
          refine ⟨46823040569541743210964185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31215360379694495473976123 46823040569541743210964185)
          ·
            refine ⟨35117280427156307408223139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46823040569541743210964185 35117280427156307408223139)
            ·
              refine ⟨52675920640734461112334709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35117280427156307408223139 52675920640734461112334709)
              ·
                refine ⟨4938367560068855729281379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52675920640734461112334709 4938367560068855729281379)
                ·
                  refine ⟨7407551340103283593922069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938367560068855729281379 7407551340103283593922069)
                  ·
                    refine ⟨347228969067341418465097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7407551340103283593922069 347228969067341418465097)
                    ·
                      rfl

theorem cell22_1014339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_1014339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014339 prefixEnd_1014339 := by exact prefixLift 1014339
  have htrace : WordTrace (prefixWord ++ tailWord_1014339) baseStart_1014339 baseEnd_1014339 := by
    simpa [prefixWord, tailWord_1014339, baseEnd_1014339] using wordTrace_append hprefix tailTrace_1014339
  have hstable : (prefixWord ++ tailWord_1014339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014339).length < 2 ^ (prefixWord ++ tailWord_1014339).sum := by decide
  have hdescent : baseEnd_1014339 < baseStart_1014339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014341 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_1014341 : Nat := 118140960795 + 1014341 * 2 ^ 59
def prefixEnd_1014341 : Nat := 4983230072969 + 3 ^ 40 * 1014341 * 2
def baseEnd_1014341 : Nat := 347229653708214079915091

theorem tailTrace_1014341 : CollatzResearch.WordTrace tailWord_1014341 prefixEnd_1014341 347229653708214079915091 := by
  unfold tailWord_1014341
  simp only [CollatzResearch.WordTrace]
  refine ⟨36996055618223267495914877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24664037078815511663943251 36996055618223267495914877)
  ·
    refine ⟨13873520856833725310968079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36996055618223267495914877 13873520856833725310968079)
    ·
      refine ⟨20810281285250587966452119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13873520856833725310968079 20810281285250587966452119)
      ·
        refine ⟨31215421927875881949678179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20810281285250587966452119 31215421927875881949678179)
        ·
          refine ⟨46823132891813822924517269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31215421927875881949678179 46823132891813822924517269)
          ·
            refine ⟨2194834354303772949586747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46823132891813822924517269 2194834354303772949586747)
            ·
              refine ⟨3292251531455659424380121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2194834354303772949586747 3292251531455659424380121)
              ·
                refine ⟨2469188648591744568285091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292251531455659424380121 2469188648591744568285091)
                ·
                  refine ⟨3703782972887616852427637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469188648591744568285091 3703782972887616852427637)
                  ·
                    refine ⟨347229653708214079915091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3703782972887616852427637 347229653708214079915091)
                    ·
                      rfl

theorem cell22_1014341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_1014341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014341 prefixEnd_1014341 := by exact prefixLift 1014341
  have htrace : WordTrace (prefixWord ++ tailWord_1014341) baseStart_1014341 baseEnd_1014341 := by
    simpa [prefixWord, tailWord_1014341, baseEnd_1014341] using wordTrace_append hprefix tailTrace_1014341
  have hstable : (prefixWord ++ tailWord_1014341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014341).length < 2 ^ (prefixWord ++ tailWord_1014341).sum := by decide
  have hdescent : baseEnd_1014341 < baseStart_1014341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014420 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1014420 : Nat := 118140960795 + 1014420 * 2 ^ 59
def prefixEnd_1014420 : Nat := 4983230072969 + 3 ^ 40 * 1014420 * 2
def baseEnd_1014420 : Nat := 347256697022684207189849

theorem tailTrace_1014420 : CollatzResearch.WordTrace tailWord_1014420 prefixEnd_1014420 347256697022684207189849 := by
  unfold tailWord_1014420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18499468492468531994020357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24665957989958042658693809 18499468492468531994020357)
  ·
    refine ⟨3468650342337849748878817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18499468492468531994020357 3468650342337849748878817)
    ·
      refine ⟨2601487756753387311659113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3468650342337849748878817 2601487756753387311659113)
      ·
        refine ⟨1951115817565040483744335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2601487756753387311659113 1951115817565040483744335)
        ·
          refine ⟨2926673726347560725616503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951115817565040483744335 2926673726347560725616503)
          ·
            refine ⟨4390010589521341088424755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926673726347560725616503 4390010589521341088424755)
            ·
              refine ⟨6585015884282011632637133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390010589521341088424755 6585015884282011632637133)
              ·
                refine ⟨2469380956605754362238925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6585015884282011632637133 2469380956605754362238925)
                ·
                  refine ⟨926017858727157885839597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2469380956605754362238925 926017858727157885839597)
                  ·
                    refine ⟨347256697022684207189849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926017858727157885839597 347256697022684207189849)
                    ·
                      rfl

theorem cell22_1014420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1014420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014420 prefixEnd_1014420 := by exact prefixLift 1014420
  have htrace : WordTrace (prefixWord ++ tailWord_1014420) baseStart_1014420 baseEnd_1014420 := by
    simpa [prefixWord, tailWord_1014420, baseEnd_1014420] using wordTrace_append hprefix tailTrace_1014420
  have hstable : (prefixWord ++ tailWord_1014420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014420).length < 2 ^ (prefixWord ++ tailWord_1014420).sum := by decide
  have hdescent : baseEnd_1014420 < baseStart_1014420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014463 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 1, 4]
def baseStart_1014463 : Nat := 118140960795 + 1014463 * 2 ^ 59
def prefixEnd_1014463 : Nat := 4983230072969 + 3 ^ 40 * 1014463 * 2
def baseEnd_1014463 : Nat := 347271416801446428364717

theorem tailTrace_1014463 : CollatzResearch.WordTrace tailWord_1014463 prefixEnd_1014463 347271416801446428364717 := by
  unfold tailWord_1014463
  simp only [CollatzResearch.WordTrace]
  refine ⟨37000505323781282331856043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24667003549187521554570695 37000505323781282331856043)
  ·
    refine ⟨55500757985671923497784065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37000505323781282331856043 55500757985671923497784065)
    ·
      refine ⟨41625568489253942623338049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55500757985671923497784065 41625568489253942623338049)
      ·
        refine ⟨31219176366940456967503537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41625568489253942623338049 31219176366940456967503537)
        ·
          refine ⟨23414382275205342725627653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31219176366940456967503537 23414382275205342725627653)
          ·
            refine ⟨4390196676601001761055185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23414382275205342725627653 4390196676601001761055185)
            ·
              refine ⟨3292647507450751320791389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390196676601001761055185 3292647507450751320791389)
              ·
                refine ⟨1234742815294031745296771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3292647507450751320791389 1234742815294031745296771)
                ·
                  refine ⟨1852114222941047617945157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234742815294031745296771 1852114222941047617945157)
                  ·
                    refine ⟨347271416801446428364717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852114222941047617945157 347271416801446428364717)
                    ·
                      rfl

theorem cell22_1014463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_1014463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014463 prefixEnd_1014463 := by exact prefixLift 1014463
  have htrace : WordTrace (prefixWord ++ tailWord_1014463) baseStart_1014463 baseEnd_1014463 := by
    simpa [prefixWord, tailWord_1014463, baseEnd_1014463] using wordTrace_append hprefix tailTrace_1014463
  have hstable : (prefixWord ++ tailWord_1014463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014463).length < 2 ^ (prefixWord ++ tailWord_1014463).sum := by decide
  have hdescent : baseEnd_1014463 < baseStart_1014463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014478 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1014478 : Nat := 118140960795 + 1014478 * 2 ^ 59
def prefixEnd_1014478 : Nat := 4983230072969 + 3 ^ 40 * 1014478 * 2
def baseEnd_1014478 : Nat := 115758850535997129746557

theorem tailTrace_1014478 : CollatzResearch.WordTrace tailWord_1014478 prefixEnd_1014478 115758850535997129746557 := by
  unfold tailWord_1014478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4625131552340867486706511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24667368279151293262434725 4625131552340867486706511)
  ·
    refine ⟨6937697328511301230059767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4625131552340867486706511 6937697328511301230059767)
    ·
      refine ⟨10406545992766951845089651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6937697328511301230059767 10406545992766951845089651)
      ·
        refine ⟨15609818989150427767634477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10406545992766951845089651 15609818989150427767634477)
        ·
          refine ⟨5853682120931410412862929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15609818989150427767634477 5853682120931410412862929)
          ·
            refine ⟨4390261590698557809647197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5853682120931410412862929 4390261590698557809647197)
            ·
              refine ⟨1646348096511959178617699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4390261590698557809647197 1646348096511959178617699)
              ·
                refine ⟨2469522144767938767926549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646348096511959178617699 2469522144767938767926549)
                ·
                  refine ⟨115758850535997129746557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2469522144767938767926549 115758850535997129746557)
                  ·
                    rfl

theorem cell22_1014478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1014478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014478 prefixEnd_1014478 := by exact prefixLift 1014478
  have htrace : WordTrace (prefixWord ++ tailWord_1014478) baseStart_1014478 baseEnd_1014478 := by
    simpa [prefixWord, tailWord_1014478, baseEnd_1014478] using wordTrace_append hprefix tailTrace_1014478
  have hstable : (prefixWord ++ tailWord_1014478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014478).length < 2 ^ (prefixWord ++ tailWord_1014478).sum := by decide
  have hdescent : baseEnd_1014478 < baseStart_1014478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014484 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1014484 : Nat := 118140960795 + 1014484 * 2 ^ 59
def prefixEnd_1014484 : Nat := 4983230072969 + 3 ^ 40 * 1014484 * 2
def baseEnd_1014484 : Nat := 115759535176869791196551

theorem tailTrace_1014484 : CollatzResearch.WordTrace tailWord_1014484 prefixEnd_1014484 115759535176869791196551 := by
  unfold tailWord_1014484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500635628352601459185253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24667514171136801945580337 18500635628352601459185253)
  ·
    refine ⟨3468869180316112773597235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18500635628352601459185253 3468869180316112773597235)
    ·
      refine ⟨5203303770474169160395853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3468869180316112773597235 5203303770474169160395853)
      ·
        refine ⟨1951238913927813435148445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5203303770474169160395853 1951238913927813435148445)
        ·
          refine ⟨731714592722930038180667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1951238913927813435148445 731714592722930038180667)
          ·
            refine ⟨1097571889084395057271001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731714592722930038180667 1097571889084395057271001)
            ·
              refine ⟨823178916813296292953251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097571889084395057271001 823178916813296292953251)
              ·
                refine ⟨1234768375219944439429877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823178916813296292953251 1234768375219944439429877)
                ·
                  refine ⟨115759535176869791196551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1234768375219944439429877 115759535176869791196551)
                  ·
                    rfl

theorem cell22_1014484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1014484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014484 prefixEnd_1014484 := by exact prefixLift 1014484
  have htrace : WordTrace (prefixWord ++ tailWord_1014484) baseStart_1014484 baseEnd_1014484 := by
    simpa [prefixWord, tailWord_1014484, baseEnd_1014484] using wordTrace_append hprefix tailTrace_1014484
  have hstable : (prefixWord ++ tailWord_1014484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014484).length < 2 ^ (prefixWord ++ tailWord_1014484).sum := by decide
  have hdescent : baseEnd_1014484 < baseStart_1014484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014557 : List Nat := [1, 4, 2, 4, 1, 1, 3, 6]
def baseStart_1014557 : Nat := 118140960795 + 1014557 * 2 ^ 59
def prefixEnd_1014557 : Nat := 4983230072969 + 3 ^ 40 * 1014557 * 2
def baseEnd_1014557 : Nat := 38589288324717946279381

theorem tailTrace_1014557 : CollatzResearch.WordTrace tailWord_1014557 prefixEnd_1014557 38589288324717946279381 := by
  unfold tailWord_1014557
  simp only [CollatzResearch.WordTrace]
  refine ⟨37003933785440736385777925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24669289190293824257185283 37003933785440736385777925)
  ·
    refine ⟨6938237584770138072333361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37003933785440736385777925 6938237584770138072333361)
    ·
      refine ⟨5203678188577603554250021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6938237584770138072333361 5203678188577603554250021)
      ·
        refine ⟨975689660358300666421879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5203678188577603554250021 975689660358300666421879)
        ·
          refine ⟨1463534490537450999632819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975689660358300666421879 1463534490537450999632819)
          ·
            refine ⟨2195301735806176499449229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463534490537450999632819 2195301735806176499449229)
            ·
              refine ⟨823238150927316187293461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2195301735806176499449229 823238150927316187293461)
              ·
                refine ⟨38589288324717946279381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 823238150927316187293461 38589288324717946279381)
                ·
                  rfl

theorem cell22_1014557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 6].length) (baseStart_1014557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014557 prefixEnd_1014557 := by exact prefixLift 1014557
  have htrace : WordTrace (prefixWord ++ tailWord_1014557) baseStart_1014557 baseEnd_1014557 := by
    simpa [prefixWord, tailWord_1014557, baseEnd_1014557] using wordTrace_append hprefix tailTrace_1014557
  have hstable : (prefixWord ++ tailWord_1014557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014557).length < 2 ^ (prefixWord ++ tailWord_1014557).sum := by decide
  have hdescent : baseEnd_1014557 < baseStart_1014557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014568 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_1014568 : Nat := 118140960795 + 1014568 * 2 ^ 59
def prefixEnd_1014568 : Nat := 4983230072969 + 3 ^ 40 * 1014568 * 2
def baseEnd_1014568 : Nat := 115769120149087051496465

theorem tailTrace_1014568 : CollatzResearch.WordTrace tailWord_1014568 prefixEnd_1014568 115769120149087051496465 := by
  unfold tailWord_1014568
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502167494200442632214179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24669556658933923509618905 18502167494200442632214179)
  ·
    refine ⟨27753251241300663948321269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18502167494200442632214179 27753251241300663948321269)
    ·
      refine ⟨2601867303871937245155119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27753251241300663948321269 2601867303871937245155119)
      ·
        refine ⟨3902800955807905867732679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601867303871937245155119 3902800955807905867732679)
        ·
          refine ⟨5854201433711858801599019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902800955807905867732679 5854201433711858801599019)
          ·
            refine ⟨8781302150567788202398529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854201433711858801599019 8781302150567788202398529)
            ·
              refine ⟨6585976612925841151798897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8781302150567788202398529 6585976612925841151798897)
              ·
                refine ⟨4939482459694380863849173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6585976612925841151798897 4939482459694380863849173)
                ·
                  refine ⟨115769120149087051496465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4939482459694380863849173 115769120149087051496465)
                  ·
                    rfl

theorem cell22_1014568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_1014568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014568 prefixEnd_1014568 := by exact prefixLift 1014568
  have htrace : WordTrace (prefixWord ++ tailWord_1014568) baseStart_1014568 baseEnd_1014568 := by
    simpa [prefixWord, tailWord_1014568, baseEnd_1014568] using wordTrace_append hprefix tailTrace_1014568
  have hstable : (prefixWord ++ tailWord_1014568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014568).length < 2 ^ (prefixWord ++ tailWord_1014568).sum := by decide
  have hdescent : baseEnd_1014568 < baseStart_1014568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014572 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_1014572 : Nat := 118140960795 + 1014572 * 2 ^ 59
def prefixEnd_1014572 : Nat := 4983230072969 + 3 ^ 40 * 1014572 * 2
def baseEnd_1014572 : Nat := 347308729729006477389383

theorem tailTrace_1014572 : CollatzResearch.WordTrace tailWord_1014572 prefixEnd_1014572 347308729729006477389383 := by
  unfold tailWord_1014572
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502240440193196973786985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24669653920257595965049313 18502240440193196973786985)
  ·
    refine ⟨13876680330144897730340239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18502240440193196973786985 13876680330144897730340239)
    ·
      refine ⟨20815020495217346595510359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13876680330144897730340239 20815020495217346595510359)
      ·
        refine ⟨31222530742826019893265539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20815020495217346595510359 31222530742826019893265539)
        ·
          refine ⟨46833796114239029839898309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31222530742826019893265539 46833796114239029839898309)
          ·
            refine ⟨8781336771419818094980933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46833796114239029839898309 8781336771419818094980933)
            ·
              refine ⟨1646500644641215892808925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8781336771419818094980933 1646500644641215892808925)
              ·
                refine ⟨617437741740455959803347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646500644641215892808925 617437741740455959803347)
                ·
                  refine ⟨926156612610683939705021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617437741740455959803347 926156612610683939705021)
                  ·
                    refine ⟨347308729729006477389383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926156612610683939705021 347308729729006477389383)
                    ·
                      rfl

theorem cell22_1014572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_1014572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014572 prefixEnd_1014572 := by exact prefixLift 1014572
  have htrace : WordTrace (prefixWord ++ tailWord_1014572) baseStart_1014572 baseEnd_1014572 := by
    simpa [prefixWord, tailWord_1014572, baseEnd_1014572] using wordTrace_append hprefix tailTrace_1014572
  have hstable : (prefixWord ++ tailWord_1014572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014572).length < 2 ^ (prefixWord ++ tailWord_1014572).sum := by decide
  have hdescent : baseEnd_1014572 < baseStart_1014572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014613 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 6]
def baseStart_1014613 : Nat := 118140960795 + 1014613 * 2 ^ 59
def prefixEnd_1014613 : Nat := 4983230072969 + 3 ^ 40 * 1014613 * 2
def baseEnd_1014613 : Nat := 115774254955632012371419

theorem tailTrace_1014613 : CollatzResearch.WordTrace tailWord_1014613 prefixEnd_1014613 115774254955632012371419 := by
  unfold tailWord_1014613
  simp only [CollatzResearch.WordTrace]
  refine ⟨37005976273237857949816493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24670650848825238633210995 37005976273237857949816493)
  ·
    refine ⟨13877241102464196731181185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37005976273237857949816493 13877241102464196731181185)
    ·
      refine ⟨10407930826848147548385889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13877241102464196731181185 10407930826848147548385889)
      ·
        refine ⟨7805948120136110661289417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10407930826848147548385889 7805948120136110661289417)
        ·
          refine ⟨5854461090102082995967063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7805948120136110661289417 5854461090102082995967063)
          ·
            refine ⟨8781691635153124493950595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854461090102082995967063 8781691635153124493950595)
            ·
              refine ⟨13172537452729686740925893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8781691635153124493950595 13172537452729686740925893)
              ·
                refine ⟨2469850772386816263923605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13172537452729686740925893 2469850772386816263923605)
                ·
                  refine ⟨115774254955632012371419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2469850772386816263923605 115774254955632012371419)
                  ·
                    rfl

theorem cell22_1014613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_1014613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014613 prefixEnd_1014613 := by exact prefixLift 1014613
  have htrace : WordTrace (prefixWord ++ tailWord_1014613) baseStart_1014613 baseEnd_1014613 := by
    simpa [prefixWord, tailWord_1014613, baseEnd_1014613] using wordTrace_append hprefix tailTrace_1014613
  have hstable : (prefixWord ++ tailWord_1014613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014613).length < 2 ^ (prefixWord ++ tailWord_1014613).sum := by decide
  have hdescent : baseEnd_1014613 < baseStart_1014613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014615 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 1, 4]
def baseStart_1014615 : Nat := 118140960795 + 1014615 * 2 ^ 59
def prefixEnd_1014615 : Nat := 4983230072969 + 3 ^ 40 * 1014615 * 2
def baseEnd_1014615 : Nat := 347323449507768698564251

theorem tailTrace_1014615 : CollatzResearch.WordTrace tailWord_1014615 prefixEnd_1014615 347323449507768698564251 := by
  unfold tailWord_1014615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37006049219230612291389299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24670699479487074860926199 37006049219230612291389299)
  ·
    refine ⟨55509073828845918437083949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37006049219230612291389299 55509073828845918437083949)
    ·
      refine ⟨20815902685817219413906481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55509073828845918437083949 20815902685817219413906481)
      ·
        refine ⟨15611927014362914560429861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20815902685817219413906481 15611927014362914560429861)
        ·
          refine ⟨2927236315193046480080599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15611927014362914560429861 2927236315193046480080599)
          ·
            refine ⟨4390854472789569720120899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927236315193046480080599 4390854472789569720120899)
            ·
              refine ⟨6586281709184354580181349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390854472789569720120899 6586281709184354580181349)
              ·
                refine ⟨1234927820472066483784003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6586281709184354580181349 1234927820472066483784003)
                ·
                  refine ⟨1852391730708099725676005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234927820472066483784003 1852391730708099725676005)
                  ·
                    refine ⟨347323449507768698564251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852391730708099725676005 347323449507768698564251)
                    ·
                      rfl

theorem cell22_1014615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_1014615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014615 prefixEnd_1014615 := by exact prefixLift 1014615
  have htrace : WordTrace (prefixWord ++ tailWord_1014615) baseStart_1014615 baseEnd_1014615 := by
    simpa [prefixWord, tailWord_1014615, baseEnd_1014615] using wordTrace_append hprefix tailTrace_1014615
  have hstable : (prefixWord ++ tailWord_1014615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014615).length < 2 ^ (prefixWord ++ tailWord_1014615).sum := by decide
  have hdescent : baseEnd_1014615 < baseStart_1014615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014643 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 4, 4]
def baseStart_1014643 : Nat := 118140960795 + 1014643 * 2 ^ 59
def prefixEnd_1014643 : Nat := 4983230072969 + 3 ^ 40 * 1014643 * 2
def baseEnd_1014643 : Nat := 347333034479985958864165

theorem tailTrace_1014643 : CollatzResearch.WordTrace tailWord_1014643 prefixEnd_1014643 347333034479985958864165 := by
  unfold tailWord_1014643
  simp only [CollatzResearch.WordTrace]
  refine ⟨37007070463129173073408583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24671380308752782048939055 37007070463129173073408583)
  ·
    refine ⟨55510605694693759610112875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37007070463129173073408583 55510605694693759610112875)
    ·
      refine ⟨83265908542040639415169313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55510605694693759610112875 83265908542040639415169313)
      ·
        refine ⟨62449431406530479561376985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83265908542040639415169313 62449431406530479561376985)
        ·
          refine ⟨46837073554897859671032739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62449431406530479561376985 46837073554897859671032739)
          ·
            refine ⟨70255610332346789506549109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46837073554897859671032739 70255610332346789506549109)
            ·
              refine ⟨6586463468657511516238979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70255610332346789506549109 6586463468657511516238979)
              ·
                refine ⟨9879695202986267274358469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6586463468657511516238979 9879695202986267274358469)
                ·
                  refine ⟨1852442850559925113942213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9879695202986267274358469 1852442850559925113942213)
                  ·
                    refine ⟨347333034479985958864165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852442850559925113942213 347333034479985958864165)
                    ·
                      rfl

theorem cell22_1014643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_1014643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014643 prefixEnd_1014643 := by exact prefixLift 1014643
  have htrace : WordTrace (prefixWord ++ tailWord_1014643) baseStart_1014643 baseEnd_1014643 := by
    simpa [prefixWord, tailWord_1014643, baseEnd_1014643] using wordTrace_append hprefix tailTrace_1014643
  have hstable : (prefixWord ++ tailWord_1014643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014643).length < 2 ^ (prefixWord ++ tailWord_1014643).sum := by decide
  have hdescent : baseEnd_1014643 < baseStart_1014643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014720 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_1014720 : Nat := 118140960795 + 1014720 * 2 ^ 59
def prefixEnd_1014720 : Nat := 4983230072969 + 3 ^ 40 * 1014720 * 2
def baseEnd_1014720 : Nat := 115786464384527808229643

theorem tailTrace_1014720 : CollatzResearch.WordTrace tailWord_1014720 prefixEnd_1014720 115786464384527808229643 := by
  unfold tailWord_1014720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504939441925107611980807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24673252589233476815974409 18504939441925107611980807)
  ·
    refine ⟨27757409162887661417971211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18504939441925107611980807 27757409162887661417971211)
    ·
      refine ⟨41636113744331492126956817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27757409162887661417971211 41636113744331492126956817)
      ·
        refine ⟨31227085308248619095217613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41636113744331492126956817 31227085308248619095217613)
        ·
          refine ⟨11710156990593232160706605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31227085308248619095217613 11710156990593232160706605)
          ·
            refine ⟨4391308871472462060264977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11710156990593232160706605 4391308871472462060264977)
            ·
              refine ⟨3293481653604346545198733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391308871472462060264977 3293481653604346545198733)
              ·
                refine ⟨1235055620101629954449525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3293481653604346545198733 1235055620101629954449525)
                ·
                  refine ⟨115786464384527808229643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235055620101629954449525 115786464384527808229643)
                  ·
                    rfl

theorem cell22_1014720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_1014720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014720 prefixEnd_1014720 := by exact prefixLift 1014720
  have htrace : WordTrace (prefixWord ++ tailWord_1014720) baseStart_1014720 baseEnd_1014720 := by
    simpa [prefixWord, tailWord_1014720, baseEnd_1014720] using wordTrace_append hprefix tailTrace_1014720
  have hstable : (prefixWord ++ tailWord_1014720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014720).length < 2 ^ (prefixWord ++ tailWord_1014720).sum := by decide
  have hdescent : baseEnd_1014720 < baseStart_1014720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014741 : List Nat := [1, 3, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_1014741 : Nat := 118140960795 + 1014741 * 2 ^ 59
def prefixEnd_1014741 : Nat := 4983230072969 + 3 ^ 40 * 1014741 * 2
def baseEnd_1014741 : Nat := 347366581882746369913865

theorem tailTrace_1014741 : CollatzResearch.WordTrace tailWord_1014741 prefixEnd_1014741 347366581882746369913865 := by
  unfold tailWord_1014741
  simp only [CollatzResearch.WordTrace]
  refine ⟨37010644816774135810476077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24673763211182757206984051 37010644816774135810476077)
  ·
    refine ⟨13878991806290300928928529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37010644816774135810476077 13878991806290300928928529)
    ·
      refine ⟨10409243854717725696696397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13878991806290300928928529 10409243854717725696696397)
      ·
        refine ⟨3903466445519147136261149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10409243854717725696696397 3903466445519147136261149)
        ·
          refine ⟨1463799917069680176097931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3903466445519147136261149 1463799917069680176097931)
          ·
            refine ⟨2195699875604520264146897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463799917069680176097931 2195699875604520264146897)
            ·
              refine ⟨1646774906703390198110173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195699875604520264146897 1646774906703390198110173)
              ·
                refine ⟨617540590013771324291315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1646774906703390198110173 617540590013771324291315)
                ·
                  refine ⟨926310885020656986436973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617540590013771324291315 926310885020656986436973)
                  ·
                    refine ⟨347366581882746369913865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926310885020656986436973 347366581882746369913865)
                    ·
                      rfl

theorem cell22_1014741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_1014741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014741 prefixEnd_1014741 := by exact prefixLift 1014741
  have htrace : WordTrace (prefixWord ++ tailWord_1014741) baseStart_1014741 baseEnd_1014741 := by
    simpa [prefixWord, tailWord_1014741, baseEnd_1014741] using wordTrace_append hprefix tailTrace_1014741
  have hstable : (prefixWord ++ tailWord_1014741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014741).length < 2 ^ (prefixWord ++ tailWord_1014741).sum := by decide
  have hdescent : baseEnd_1014741 < baseStart_1014741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014754 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1014754 : Nat := 118140960795 + 1014754 * 2 ^ 59
def prefixEnd_1014754 : Nat := 4983230072969 + 3 ^ 40 * 1014754 * 2
def baseEnd_1014754 : Nat := 115790344016139556446275

theorem tailTrace_1014754 : CollatzResearch.WordTrace tailWord_1014754 prefixEnd_1014754 115790344016139556446275 := by
  unfold tailWord_1014754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252779741431759757674829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24674079310484692687132877 9252779741431759757674829)
  ·
    refine ⟨3469792403036909909128061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9252779741431759757674829 3469792403036909909128061)
    ·
      refine ⟨1301172151138841215923023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3469792403036909909128061 1301172151138841215923023)
      ·
        refine ⟨1951758226708261823884535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301172151138841215923023 1951758226708261823884535)
        ·
          refine ⟨2927637340062392735826803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951758226708261823884535 2927637340062392735826803)
          ·
            refine ⟨4391456010093589103740205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927637340062392735826803 4391456010093589103740205)
            ·
              refine ⟨1646796003785095913902577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4391456010093589103740205 1646796003785095913902577)
              ·
                refine ⟨1235097002838821935426933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646796003785095913902577 1235097002838821935426933)
                ·
                  refine ⟨115790344016139556446275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235097002838821935426933 115790344016139556446275)
                  ·
                    rfl

theorem cell22_1014754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1014754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014754 prefixEnd_1014754 := by exact prefixLift 1014754
  have htrace : WordTrace (prefixWord ++ tailWord_1014754) baseStart_1014754 baseEnd_1014754 := by
    simpa [prefixWord, tailWord_1014754, baseEnd_1014754] using wordTrace_append hprefix tailTrace_1014754
  have hstable : (prefixWord ++ tailWord_1014754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014754).length < 2 ^ (prefixWord ++ tailWord_1014754).sum := by decide
  have hdescent : baseEnd_1014754 < baseStart_1014754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014763 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_1014763 : Nat := 118140960795 + 1014763 * 2 ^ 59
def prefixEnd_1014763 : Nat := 4983230072969 + 3 ^ 40 * 1014763 * 2
def baseEnd_1014763 : Nat := 347374112932345645863797

theorem tailTrace_1014763 : CollatzResearch.WordTrace tailWord_1014763 prefixEnd_1014763 347374112932345645863797 := by
  unfold tailWord_1014763
  simp only [CollatzResearch.WordTrace]
  refine ⟨37011447222694433567776943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24674298148462955711851295 37011447222694433567776943)
  ·
    refine ⟨55517170834041650351665415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37011447222694433567776943 55517170834041650351665415)
    ·
      refine ⟨83275756251062475527498123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55517170834041650351665415 83275756251062475527498123)
      ·
        refine ⟨124913634376593713291247185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83275756251062475527498123 124913634376593713291247185)
        ·
          refine ⟨93685225782445284968435389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124913634376593713291247185 93685225782445284968435389)
          ·
            refine ⟨35131959668416981863163271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93685225782445284968435389 35131959668416981863163271)
            ·
              refine ⟨52697939502625472794744907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35131959668416981863163271 52697939502625472794744907)
              ·
                refine ⟨79046909253938209192117361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52697939502625472794744907 79046909253938209192117361)
                ·
                  refine ⟨59285181940453656894088021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79046909253938209192117361 59285181940453656894088021)
                  ·
                    refine ⟨347374112932345645863797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59285181940453656894088021 347374112932345645863797)
                    ·
                      rfl

theorem cell22_1014763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_1014763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014763 prefixEnd_1014763 := by exact prefixLift 1014763
  have htrace : WordTrace (prefixWord ++ tailWord_1014763) baseStart_1014763 baseEnd_1014763 := by
    simpa [prefixWord, tailWord_1014763, baseEnd_1014763] using wordTrace_append hprefix tailTrace_1014763
  have hstable : (prefixWord ++ tailWord_1014763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014763).length < 2 ^ (prefixWord ++ tailWord_1014763).sum := by decide
  have hdescent : baseEnd_1014763 < baseStart_1014763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014795 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 1, 6]
def baseStart_1014795 : Nat := 118140960795 + 1014795 * 2 ^ 59
def prefixEnd_1014795 : Nat := 4983230072969 + 3 ^ 40 * 1014795 * 2
def baseEnd_1014795 : Nat := 347385067186308229063699

theorem tailTrace_1014795 : CollatzResearch.WordTrace tailWord_1014795 prefixEnd_1014795 347385067186308229063699 := by
  unfold tailWord_1014795
  simp only [CollatzResearch.WordTrace]
  refine ⟨37012614358578503032941839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24675076239052335355294559 37012614358578503032941839)
  ·
    refine ⟨55518921537867754549412759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37012614358578503032941839 55518921537867754549412759)
    ·
      refine ⟨83278382306801631824119139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55518921537867754549412759 83278382306801631824119139)
      ·
        refine ⟨124917573460202447736178709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83278382306801631824119139 124917573460202447736178709)
        ·
          refine ⟨5855511255946989737633377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124917573460202447736178709 5855511255946989737633377)
          ·
            refine ⟨4391633441960242303225033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5855511255946989737633377 4391633441960242303225033)
            ·
              refine ⟨3293725081470181727418775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391633441960242303225033 3293725081470181727418775)
              ·
                refine ⟨4940587622205272591128163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3293725081470181727418775 4940587622205272591128163)
                ·
                  refine ⟨7410881433307908886692245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940587622205272591128163 7410881433307908886692245)
                  ·
                    refine ⟨347385067186308229063699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7410881433307908886692245 347385067186308229063699)
                    ·
                      rfl

theorem cell22_1014795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_1014795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014795 prefixEnd_1014795 := by exact prefixLift 1014795
  have htrace : WordTrace (prefixWord ++ tailWord_1014795) baseStart_1014795 baseEnd_1014795 := by
    simpa [prefixWord, tailWord_1014795, baseEnd_1014795] using wordTrace_append hprefix tailTrace_1014795
  have hstable : (prefixWord ++ tailWord_1014795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014795).length < 2 ^ (prefixWord ++ tailWord_1014795).sum := by decide
  have hdescent : baseEnd_1014795 < baseStart_1014795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014816 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 6]
def baseStart_1014816 : Nat := 118140960795 + 1014816 * 2 ^ 59
def prefixEnd_1014816 : Nat := 4983230072969 + 3 ^ 40 * 1014816 * 2
def baseEnd_1014816 : Nat := 115797418638490391429545

theorem tailTrace_1014816 : CollatzResearch.WordTrace tailWord_1014816 prefixEnd_1014816 115797418638490391429545 := by
  unfold tailWord_1014816
  simp only [CollatzResearch.WordTrace]
  refine ⟨18506690145751211809728151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24675586861001615746304201 18506690145751211809728151)
  ·
    refine ⟨27760035218626817714592227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18506690145751211809728151 27760035218626817714592227)
    ·
      refine ⟨41640052827940226571888341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27760035218626817714592227 41640052827940226571888341)
      ·
        refine ⟨975938738154849060278633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41640052827940226571888341 975938738154849060278633)
        ·
          refine ⟨731954053616136795208975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975938738154849060278633 731954053616136795208975)
          ·
            refine ⟨1097931080424205192813463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731954053616136795208975 1097931080424205192813463)
            ·
              refine ⟨1646896620636307789220195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097931080424205192813463 1646896620636307789220195)
              ·
                refine ⟨2470344930954461683830293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646896620636307789220195 2470344930954461683830293)
                ·
                  refine ⟨115797418638490391429545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2470344930954461683830293 115797418638490391429545)
                  ·
                    rfl

theorem cell22_1014816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_1014816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014816 prefixEnd_1014816 := by exact prefixLift 1014816
  have htrace : WordTrace (prefixWord ++ tailWord_1014816) baseStart_1014816 baseEnd_1014816 := by
    simpa [prefixWord, tailWord_1014816, baseEnd_1014816] using wordTrace_append hprefix tailTrace_1014816
  have hstable : (prefixWord ++ tailWord_1014816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014816).length < 2 ^ (prefixWord ++ tailWord_1014816).sum := by decide
  have hdescent : baseEnd_1014816 < baseStart_1014816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014842 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_1014842 : Nat := 118140960795 + 1014842 * 2 ^ 59
def prefixEnd_1014842 : Nat := 4983230072969 + 3 ^ 40 * 1014842 * 2
def baseEnd_1014842 : Nat := 347401156246815773138555

theorem tailTrace_1014842 : CollatzResearch.WordTrace tailWord_1014842 prefixEnd_1014842 347401156246815773138555 := by
  unfold tailWord_1014842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253582147352057514975695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24676219059605486706601853 9253582147352057514975695)
  ·
    refine ⟨13880373221028086272463543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9253582147352057514975695 13880373221028086272463543)
    ·
      refine ⟨20820559831542129408695315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13880373221028086272463543 20820559831542129408695315)
      ·
        refine ⟨31230839747313194113042973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20820559831542129408695315 31230839747313194113042973)
        ·
          refine ⟨11711564905242447792391115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31230839747313194113042973 11711564905242447792391115)
          ·
            refine ⟨17567347357863671688586673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11711564905242447792391115 17567347357863671688586673)
            ·
              refine ⟨13175510518397753766440005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17567347357863671688586673 13175510518397753766440005)
              ·
                refine ⟨2470408222199578831207501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13175510518397753766440005 2470408222199578831207501)
                ·
                  refine ⟨926403083324842061702813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2470408222199578831207501 926403083324842061702813)
                  ·
                    refine ⟨347401156246815773138555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926403083324842061702813 347401156246815773138555)
                    ·
                      rfl

theorem cell22_1014842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_1014842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014842 prefixEnd_1014842 := by exact prefixLift 1014842
  have htrace : WordTrace (prefixWord ++ tailWord_1014842) baseStart_1014842 baseEnd_1014842 := by
    simpa [prefixWord, tailWord_1014842, baseEnd_1014842] using wordTrace_append hprefix tailTrace_1014842
  have hstable : (prefixWord ++ tailWord_1014842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014842).length < 2 ^ (prefixWord ++ tailWord_1014842).sum := by decide
  have hdescent : baseEnd_1014842 < baseStart_1014842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014872 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_1014872 : Nat := 118140960795 + 1014872 * 2 ^ 59
def prefixEnd_1014872 : Nat := 4983230072969 + 3 ^ 40 * 1014872 * 2
def baseEnd_1014872 : Nat := 115803808619968564962821

theorem tailTrace_1014872 : CollatzResearch.WordTrace tailWord_1014872 prefixEnd_1014872 115803808619968564962821 := by
  unfold tailWord_1014872
  simp only [CollatzResearch.WordTrace]
  refine ⟨18507711389649772591747435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24676948519533030122329913 18507711389649772591747435)
  ·
    refine ⟨27761567084474658887621153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18507711389649772591747435 27761567084474658887621153)
    ·
      refine ⟨20821175313355994165715865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27761567084474658887621153 20821175313355994165715865)
      ·
        refine ⟨15615881485016995624286899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20821175313355994165715865 15615881485016995624286899)
        ·
          refine ⟨23423822227525493436430349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15615881485016995624286899 23423822227525493436430349)
          ·
            refine ⟨8783933335322060038661381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23423822227525493436430349 8783933335322060038661381)
            ·
              refine ⟨1646987500372886257249009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8783933335322060038661381 1646987500372886257249009)
              ·
                refine ⟨1235240625279664692936757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646987500372886257249009 1235240625279664692936757)
                ·
                  refine ⟨115803808619968564962821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235240625279664692936757 115803808619968564962821)
                  ·
                    rfl

theorem cell22_1014872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_1014872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014872 prefixEnd_1014872 := by exact prefixLift 1014872
  have htrace : WordTrace (prefixWord ++ tailWord_1014872) baseStart_1014872 baseEnd_1014872 := by
    simpa [prefixWord, tailWord_1014872, baseEnd_1014872] using wordTrace_append hprefix tailTrace_1014872
  have hstable : (prefixWord ++ tailWord_1014872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014872).length < 2 ^ (prefixWord ++ tailWord_1014872).sum := by decide
  have hdescent : baseEnd_1014872 < baseStart_1014872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014876 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1014876 : Nat := 118140960795 + 1014876 * 2 ^ 59
def prefixEnd_1014876 : Nat := 4983230072969 + 3 ^ 40 * 1014876 * 2
def baseEnd_1014876 : Nat := 347412795141651017788451

theorem tailTrace_1014876 : CollatzResearch.WordTrace tailWord_1014876 prefixEnd_1014876 347412795141651017788451 := by
  unfold tailWord_1014876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18507784335642526933320241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24677045780856702577760321 18507784335642526933320241)
  ·
    refine ⟨13880838251731895199990181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18507784335642526933320241 13880838251731895199990181)
    ·
      refine ⟨2602657172199730349998159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13880838251731895199990181 2602657172199730349998159)
      ·
        refine ⟨3903985758299595524997239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602657172199730349998159 3903985758299595524997239)
        ·
          refine ⟨5855978637449393287495859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903985758299595524997239 5855978637449393287495859)
          ·
            refine ⟨8783967956174089931243789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855978637449393287495859 8783967956174089931243789)
            ·
              refine ⟨3293987983565283724216421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8783967956174089931243789 3293987983565283724216421)
              ·
                refine ⟨617622746918490698290579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3293987983565283724216421 617622746918490698290579)
                ·
                  refine ⟨926434120377736047435869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617622746918490698290579 926434120377736047435869)
                  ·
                    refine ⟨347412795141651017788451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926434120377736047435869 347412795141651017788451)
                    ·
                      rfl

theorem cell22_1014876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1014876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014876 prefixEnd_1014876 := by exact prefixLift 1014876
  have htrace : WordTrace (prefixWord ++ tailWord_1014876) baseStart_1014876 baseEnd_1014876 := by
    simpa [prefixWord, tailWord_1014876, baseEnd_1014876] using wordTrace_append hprefix tailTrace_1014876
  have hstable : (prefixWord ++ tailWord_1014876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014876).length < 2 ^ (prefixWord ++ tailWord_1014876).sum := by decide
  have hdescent : baseEnd_1014876 < baseStart_1014876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014887 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1014887 : Nat := 118140960795 + 1014887 * 2 ^ 59
def prefixEnd_1014887 : Nat := 4983230072969 + 3 ^ 40 * 1014887 * 2
def baseEnd_1014887 : Nat := 347416560666450655763417

theorem tailTrace_1014887 : CollatzResearch.WordTrace tailWord_1014887 prefixEnd_1014887 347416560666450655763417 := by
  unfold tailWord_1014887
  simp only [CollatzResearch.WordTrace]
  refine ⟨37015969874245202745290915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24677313249496801830193943 37015969874245202745290915)
  ·
    refine ⟨55523954811367804117936373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37015969874245202745290915 55523954811367804117936373)
    ·
      refine ⟨5205370763565731636056535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55523954811367804117936373 5205370763565731636056535)
      ·
        refine ⟨7808056145348597454084803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205370763565731636056535 7808056145348597454084803)
        ·
          refine ⟨11712084218022896181127205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808056145348597454084803 11712084218022896181127205)
          ·
            refine ⟨2196015790879293033961351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11712084218022896181127205 2196015790879293033961351)
            ·
              refine ⟨3294023686318939550942027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196015790879293033961351 3294023686318939550942027)
              ·
                refine ⟨4941035529478409326413041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294023686318939550942027 4941035529478409326413041)
                ·
                  refine ⟨3705776647108806994809781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4941035529478409326413041 3705776647108806994809781)
                  ·
                    refine ⟨347416560666450655763417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3705776647108806994809781 347416560666450655763417)
                    ·
                      rfl

theorem cell22_1014887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1014887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014887 prefixEnd_1014887 := by exact prefixLift 1014887
  have htrace : WordTrace (prefixWord ++ tailWord_1014887) baseStart_1014887 baseEnd_1014887 := by
    simpa [prefixWord, tailWord_1014887, baseEnd_1014887] using wordTrace_append hprefix tailTrace_1014887
  have hstable : (prefixWord ++ tailWord_1014887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014887).length < 2 ^ (prefixWord ++ tailWord_1014887).sum := by decide
  have hdescent : baseEnd_1014887 < baseStart_1014887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014949 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 1, 5]
def baseStart_1014949 : Nat := 118140960795 + 1014949 * 2 ^ 59
def prefixEnd_1014949 : Nat := 4983230072969 + 3 ^ 40 * 1014949 * 2
def baseEnd_1014949 : Nat := 347437784533503160713227

theorem tailTrace_1014949 : CollatzResearch.WordTrace tailWord_1014949 prefixEnd_1014949 347437784533503160713227 := by
  unfold tailWord_1014949
  simp only [CollatzResearch.WordTrace]
  refine ⟨37018231200020587334047901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24678820800013724889365267 37018231200020587334047901)
  ·
    refine ⟨13881836700007720250267963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37018231200020587334047901 13881836700007720250267963)
    ·
      refine ⟨20822755050011580375401945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13881836700007720250267963 20822755050011580375401945)
      ·
        refine ⟨15617066287508685281551459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20822755050011580375401945 15617066287508685281551459)
        ·
          refine ⟨23425599431263027922327189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617066287508685281551459 23425599431263027922327189)
          ·
            refine ⟨1098074973340454433859087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23425599431263027922327189 1098074973340454433859087)
            ·
              refine ⟨1647112460010681650788631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098074973340454433859087 1647112460010681650788631)
              ·
                refine ⟨2470668690016022476182947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647112460010681650788631 2470668690016022476182947)
                ·
                  refine ⟨3706003035024033714274421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470668690016022476182947 3706003035024033714274421)
                  ·
                    refine ⟨347437784533503160713227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3706003035024033714274421 347437784533503160713227)
                    ·
                      rfl

theorem cell22_1014949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_1014949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014949 prefixEnd_1014949 := by exact prefixLift 1014949
  have htrace : WordTrace (prefixWord ++ tailWord_1014949) baseStart_1014949 baseEnd_1014949 := by
    simpa [prefixWord, tailWord_1014949, baseEnd_1014949] using wordTrace_append hprefix tailTrace_1014949
  have hstable : (prefixWord ++ tailWord_1014949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014949).length < 2 ^ (prefixWord ++ tailWord_1014949).sum := by decide
  have hdescent : baseEnd_1014949 < baseStart_1014949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014962 : List Nat := [3, 2, 1, 1, 1, 5, 1, 8]
def baseStart_1014962 : Nat := 118140960795 + 1014962 * 2 ^ 59
def prefixEnd_1014962 : Nat := 4983230072969 + 3 ^ 40 * 1014962 * 2
def baseEnd_1014962 : Nat := 38604692744352828904243

theorem tailTrace_1014962 : CollatzResearch.WordTrace tailWord_1014962 prefixEnd_1014962 38604692744352828904243 := by
  unfold tailWord_1014962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254676337243372638567785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24679136899315660369514093 9254676337243372638567785)
  ·
    refine ⟨6941007252932529478925839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9254676337243372638567785 6941007252932529478925839)
    ·
      refine ⟨10411510879398794218388759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6941007252932529478925839 10411510879398794218388759)
      ·
        refine ⟨15617266319098191327583139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411510879398794218388759 15617266319098191327583139)
        ·
          refine ⟨23425899478647286991374709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617266319098191327583139 23425899478647286991374709)
          ·
            refine ⟨2196178076123183155441379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23425899478647286991374709 2196178076123183155441379)
            ·
              refine ⟨3294267114184774733162069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196178076123183155441379 3294267114184774733162069)
              ·
                refine ⟨38604692744352828904243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3294267114184774733162069 38604692744352828904243)
                ·
                  rfl

theorem cell22_1014962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_1014962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014962 prefixEnd_1014962 := by exact prefixLift 1014962
  have htrace : WordTrace (prefixWord ++ tailWord_1014962) baseStart_1014962 baseEnd_1014962 := by
    simpa [prefixWord, tailWord_1014962, baseEnd_1014962] using wordTrace_append hprefix tailTrace_1014962
  have hstable : (prefixWord ++ tailWord_1014962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014962).length < 2 ^ (prefixWord ++ tailWord_1014962).sum := by decide
  have hdescent : baseEnd_1014962 < baseStart_1014962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1014996 : List Nat := [2, 4, 1, 4, 1, 1, 2, 7]
def baseStart_1014996 : Nat := 118140960795 + 1014996 * 2 ^ 59
def prefixEnd_1014996 : Nat := 4983230072969 + 3 ^ 40 * 1014996 * 2
def baseEnd_1014996 : Nat := 38605985954890078309787

theorem tailTrace_1014996 : CollatzResearch.WordTrace tailWord_1014996 prefixEnd_1014996 38605985954890078309787 := by
  unfold tailWord_1014996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18509972715425157180504421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24679963620566876240672561 18509972715425157180504421)
  ·
    refine ⟨3470619884142216971344579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18509972715425157180504421 3470619884142216971344579)
    ·
      refine ⟨5205929826213325457016869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470619884142216971344579 5205929826213325457016869)
      ·
        refine ⟨976111842414998523190663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5205929826213325457016869 976111842414998523190663)
        ·
          refine ⟨1464167763622497784785995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976111842414998523190663 1464167763622497784785995)
          ·
            refine ⟨2196251645433746677178993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464167763622497784785995 2196251645433746677178993)
            ·
              refine ⟨1647188734075310007884245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196251645433746677178993 1647188734075310007884245)
              ·
                refine ⟨38605985954890078309787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1647188734075310007884245 38605985954890078309787)
                ·
                  rfl

theorem cell22_1014996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 7].length) (baseStart_1014996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1014996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1014996 prefixEnd_1014996 := by exact prefixLift 1014996
  have htrace : WordTrace (prefixWord ++ tailWord_1014996) baseStart_1014996 baseEnd_1014996 := by
    simpa [prefixWord, tailWord_1014996, baseEnd_1014996] using wordTrace_append hprefix tailTrace_1014996
  have hstable : (prefixWord ++ tailWord_1014996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1014996).length < 2 ^ (prefixWord ++ tailWord_1014996).sum := by decide
  have hdescent : baseEnd_1014996 < baseStart_1014996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1014996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015000 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 2, 3]
def baseStart_1015000 : Nat := 118140960795 + 1015000 * 2 ^ 59
def prefixEnd_1015000 : Nat := 4983230072969 + 3 ^ 40 * 1015000 * 2
def baseEnd_1015000 : Nat := 347455242875756027688071

theorem tailTrace_1015000 : CollatzResearch.WordTrace tailWord_1015000 prefixEnd_1015000 347455242875756027688071 := by
  unfold tailWord_1015000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510045661417911522077227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24680060881890548696102969 18510045661417911522077227)
  ·
    refine ⟨27765068492126867283115841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18510045661417911522077227 27765068492126867283115841)
    ·
      refine ⟨20823801369095150462336881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27765068492126867283115841 20823801369095150462336881)
      ·
        refine ⟨15617851026821362846752661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20823801369095150462336881 15617851026821362846752661)
        ·
          refine ⟨732086766882251383441531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15617851026821362846752661 732086766882251383441531)
          ·
            refine ⟨1098130150323377075162297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732086766882251383441531 1098130150323377075162297)
            ·
              refine ⟨823597612742532806371723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098130150323377075162297 823597612742532806371723)
              ·
                refine ⟨1235396419113799209557585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823597612742532806371723 1235396419113799209557585)
                ·
                  refine ⟨926547314335349407168189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1235396419113799209557585 926547314335349407168189)
                  ·
                    refine ⟨347455242875756027688071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926547314335349407168189 347455242875756027688071)
                    ·
                      rfl

theorem cell22_1015000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 3].length) (baseStart_1015000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015000 prefixEnd_1015000 := by exact prefixLift 1015000
  have htrace : WordTrace (prefixWord ++ tailWord_1015000) baseStart_1015000 baseEnd_1015000 := by
    simpa [prefixWord, tailWord_1015000, baseEnd_1015000] using wordTrace_append hprefix tailTrace_1015000
  have hstable : (prefixWord ++ tailWord_1015000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015000).length < 2 ^ (prefixWord ++ tailWord_1015000).sum := by decide
  have hdescent : baseEnd_1015000 < baseStart_1015000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015054 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1015054 : Nat := 118140960795 + 1015054 * 2 ^ 59
def prefixEnd_1015054 : Nat := 4983230072969 + 3 ^ 40 * 1015054 * 2
def baseEnd_1015054 : Nat := 347473728179317886837905

theorem tailTrace_1015054 : CollatzResearch.WordTrace tailWord_1015054 prefixEnd_1015054 347473728179317886837905 := by
  unfold tailWord_1015054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627757608080023783327527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24681373909760126844413477 4627757608080023783327527)
  ·
    refine ⟨6941636412120035674991291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4627757608080023783327527 6941636412120035674991291)
    ·
      refine ⟨10412454618180053512486937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6941636412120035674991291 10412454618180053512486937)
      ·
        refine ⟨7809340963635040134365203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10412454618180053512486937 7809340963635040134365203)
        ·
          refine ⟨11714011445452560201547805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809340963635040134365203 11714011445452560201547805)
          ·
            refine ⟨4392754292044710075580427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11714011445452560201547805 4392754292044710075580427)
            ·
              refine ⟨6589131438067065113370641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392754292044710075580427 6589131438067065113370641)
              ·
                refine ⟨4941848578550298835027981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6589131438067065113370641 4941848578550298835027981)
                ·
                  refine ⟨1853193216956362063135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4941848578550298835027981 1853193216956362063135493)
                  ·
                    refine ⟨347473728179317886837905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1853193216956362063135493 347473728179317886837905)
                    ·
                      rfl

theorem cell22_1015054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1015054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015054 prefixEnd_1015054 := by exact prefixLift 1015054
  have htrace : WordTrace (prefixWord ++ tailWord_1015054) baseStart_1015054 baseEnd_1015054 := by
    simpa [prefixWord, tailWord_1015054, baseEnd_1015054] using wordTrace_append hprefix tailTrace_1015054
  have hstable : (prefixWord ++ tailWord_1015054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015054).length < 2 ^ (prefixWord ++ tailWord_1015054).sum := by decide
  have hdescent : baseEnd_1015054 < baseStart_1015054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015069 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1015069 : Nat := 118140960795 + 1015069 * 2 ^ 59
def prefixEnd_1015069 : Nat := 4983230072969 + 3 ^ 40 * 1015069 * 2
def baseEnd_1015069 : Nat := 115826287661954282570953

theorem tailTrace_1015069 : CollatzResearch.WordTrace tailWord_1015069 prefixEnd_1015069 115826287661954282570953 := by
  unfold tailWord_1015069
  simp only [CollatzResearch.WordTrace]
  refine ⟨37022607959585847828416261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24681738639723898552277507 37022607959585847828416261)
  ·
    refine ⟨6941738992422346467828049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37022607959585847828416261 6941738992422346467828049)
    ·
      refine ⟨5206304244316759850871037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6941738992422346467828049 5206304244316759850871037)
      ·
        refine ⟨1952364091618784944076639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5206304244316759850871037 1952364091618784944076639)
        ·
          refine ⟨2928546137428177416114959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952364091618784944076639 2928546137428177416114959)
          ·
            refine ⟨4392819206142266124172439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928546137428177416114959 4392819206142266124172439)
            ·
              refine ⟨6589228809213399186258659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392819206142266124172439 6589228809213399186258659)
              ·
                refine ⟨9883843213820098779387989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589228809213399186258659 9883843213820098779387989)
                ·
                  refine ⟨115826287661954282570953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9883843213820098779387989 115826287661954282570953)
                  ·
                    rfl

theorem cell22_1015069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1015069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015069 prefixEnd_1015069 := by exact prefixLift 1015069
  have htrace : WordTrace (prefixWord ++ tailWord_1015069) baseStart_1015069 baseEnd_1015069 := by
    simpa [prefixWord, tailWord_1015069, baseEnd_1015069] using wordTrace_append hprefix tailTrace_1015069
  have hstable : (prefixWord ++ tailWord_1015069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015069).length < 2 ^ (prefixWord ++ tailWord_1015069).sum := by decide
  have hdescent : baseEnd_1015069 < baseStart_1015069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015084 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 4, 3]
def baseStart_1015084 : Nat := 118140960795 + 1015084 * 2 ^ 59
def prefixEnd_1015084 : Nat := 4983230072969 + 3 ^ 40 * 1015084 * 2
def baseEnd_1015084 : Nat := 347483997792407808587813

theorem tailTrace_1015084 : CollatzResearch.WordTrace tailWord_1015084 prefixEnd_1015084 347483997792407808587813 := by
  unfold tailWord_1015084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18511577527265752695106153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24682103369687670260141537 18511577527265752695106153)
  ·
    refine ⟨13883683145449314521329615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18511577527265752695106153 13883683145449314521329615)
    ·
      refine ⟨20825524718173971781994423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13883683145449314521329615 20825524718173971781994423)
      ·
        refine ⟨31238287077260957672991635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20825524718173971781994423 31238287077260957672991635)
        ·
          refine ⟨46857430615891436509487453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238287077260957672991635 46857430615891436509487453)
          ·
            refine ⟨17571536480959288691057795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46857430615891436509487453 17571536480959288691057795)
            ·
              refine ⟨26357304721438933036586693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17571536480959288691057795 26357304721438933036586693)
              ·
                refine ⟨4941994635269799944360005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26357304721438933036586693 4941994635269799944360005)
                ·
                  refine ⟨926623994113087489567501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4941994635269799944360005 926623994113087489567501)
                  ·
                    refine ⟨347483997792407808587813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926623994113087489567501 347483997792407808587813)
                    ·
                      rfl

theorem cell22_1015084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_1015084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015084 prefixEnd_1015084 := by exact prefixLift 1015084
  have htrace : WordTrace (prefixWord ++ tailWord_1015084) baseStart_1015084 baseEnd_1015084 := by
    simpa [prefixWord, tailWord_1015084, baseEnd_1015084] using wordTrace_append hprefix tailTrace_1015084
  have hstable : (prefixWord ++ tailWord_1015084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015084).length < 2 ^ (prefixWord ++ tailWord_1015084).sum := by decide
  have hdescent : baseEnd_1015084 < baseStart_1015084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015118 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_1015118 : Nat := 118140960795 + 1015118 * 2 ^ 59
def prefixEnd_1015118 : Nat := 4983230072969 + 3 ^ 40 * 1015118 * 2
def baseEnd_1015118 : Nat := 347495636687243053237709

theorem tailTrace_1015118 : CollatzResearch.WordTrace tailWord_1015118 prefixEnd_1015118 347495636687243053237709 := by
  unfold tailWord_1015118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628049392051041149618751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24682930090938886131300005 4628049392051041149618751)
  ·
    refine ⟨6942074088076561724428127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4628049392051041149618751 6942074088076561724428127)
    ·
      refine ⟨10413111132114842586642191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6942074088076561724428127 10413111132114842586642191)
      ·
        refine ⟨15619666698172263879963287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10413111132114842586642191 15619666698172263879963287)
        ·
          refine ⟨23429500047258395819944931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15619666698172263879963287 23429500047258395819944931)
          ·
            refine ⟨35144250070887593729917397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23429500047258395819944931 35144250070887593729917397)
            ·
              refine ⟨823693361036427978044939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35144250070887593729917397 823693361036427978044939)
              ·
                refine ⟨1235540041554641967067409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823693361036427978044939 1235540041554641967067409)
                ·
                  refine ⟨926655031165981475300557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1235540041554641967067409 926655031165981475300557)
                  ·
                    refine ⟨347495636687243053237709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926655031165981475300557 347495636687243053237709)
                    ·
                      rfl

theorem cell22_1015118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_1015118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015118 prefixEnd_1015118 := by exact prefixLift 1015118
  have htrace : WordTrace (prefixWord ++ tailWord_1015118) baseStart_1015118 baseEnd_1015118 := by
    simpa [prefixWord, tailWord_1015118, baseEnd_1015118] using wordTrace_append hprefix tailTrace_1015118
  have hstable : (prefixWord ++ tailWord_1015118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015118).length < 2 ^ (prefixWord ++ tailWord_1015118).sum := by decide
  have hdescent : baseEnd_1015118 < baseStart_1015118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015159 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 5]
def baseStart_1015159 : Nat := 118140960795 + 1015159 * 2 ^ 59
def prefixEnd_1015159 : Nat := 4983230072969 + 3 ^ 40 * 1015159 * 2
def baseEnd_1015159 : Nat := 115836557275044204320861

theorem tailTrace_1015159 : CollatzResearch.WordTrace tailWord_1015159 prefixEnd_1015159 115836557275044204320861 := by
  unfold tailWord_1015159
  simp only [CollatzResearch.WordTrace]
  refine ⟨37025890529259793199192531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24683927019506528799461687 37025890529259793199192531)
  ·
    refine ⟨55538835793889689798788797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37025890529259793199192531 55538835793889689798788797)
    ·
      refine ⟨20827063422708633674545799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55538835793889689798788797 20827063422708633674545799)
      ·
        refine ⟨31240595134062950511818699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20827063422708633674545799 31240595134062950511818699)
        ·
          refine ⟨46860892701094425767728049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31240595134062950511818699 46860892701094425767728049)
          ·
            refine ⟨35145669525820819325796037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46860892701094425767728049 35145669525820819325796037)
            ·
              refine ⟨6589813036091403623586757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35145669525820819325796037 6589813036091403623586757)
              ·
                refine ⟨1235589944267138179422517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6589813036091403623586757 1235589944267138179422517)
                ·
                  refine ⟨115836557275044204320861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235589944267138179422517 115836557275044204320861)
                  ·
                    rfl

theorem cell22_1015159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 5].length) (baseStart_1015159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015159 prefixEnd_1015159 := by exact prefixLift 1015159
  have htrace : WordTrace (prefixWord ++ tailWord_1015159) baseStart_1015159 baseEnd_1015159 := by
    simpa [prefixWord, tailWord_1015159, baseEnd_1015159] using wordTrace_append hprefix tailTrace_1015159
  have hstable : (prefixWord ++ tailWord_1015159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015159).length < 2 ^ (prefixWord ++ tailWord_1015159).sum := by decide
  have hdescent : baseEnd_1015159 < baseStart_1015159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015176 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_1015176 : Nat := 118140960795 + 1015176 * 2 ^ 59
def prefixEnd_1015176 : Nat := 4983230072969 + 3 ^ 40 * 1015176 * 2
def baseEnd_1015176 : Nat := 115838497090850078429177

theorem tailTrace_1015176 : CollatzResearch.WordTrace tailWord_1015176 prefixEnd_1015176 115838497090850078429177 := by
  unfold tailWord_1015176
  simp only [CollatzResearch.WordTrace]
  refine ⟨18513255285099102551280691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24684340380132136735040921 18513255285099102551280691)
  ·
    refine ⟨27769882927648653826921037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18513255285099102551280691 27769882927648653826921037)
    ·
      refine ⟨10413706097868245185095389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27769882927648653826921037 10413706097868245185095389)
      ·
        refine ⟨3905139786700591944410771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10413706097868245185095389 3905139786700591944410771)
        ·
          refine ⟨5857709680050887916616157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905139786700591944410771 5857709680050887916616157)
          ·
            refine ⟨2196641130019082968731059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5857709680050887916616157 2196641130019082968731059)
            ·
              refine ⟨3294961695028624453096589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196641130019082968731059 3294961695028624453096589)
              ·
                refine ⟨1235610635635734169911221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3294961695028624453096589 1235610635635734169911221)
                ·
                  refine ⟨115838497090850078429177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1235610635635734169911221 115838497090850078429177)
                  ·
                    rfl

theorem cell22_1015176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_1015176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015176 prefixEnd_1015176 := by exact prefixLift 1015176
  have htrace : WordTrace (prefixWord ++ tailWord_1015176) baseStart_1015176 baseEnd_1015176 := by
    simpa [prefixWord, tailWord_1015176, baseEnd_1015176] using wordTrace_append hprefix tailTrace_1015176
  have hstable : (prefixWord ++ tailWord_1015176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015176).length < 2 ^ (prefixWord ++ tailWord_1015176).sum := by decide
  have hdescent : baseEnd_1015176 < baseStart_1015176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015279 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_1015279 : Nat := 118140960795 + 1015279 * 2 ^ 59
def prefixEnd_1015279 : Nat := 4983230072969 + 3 ^ 40 * 1015279 * 2
def baseEnd_1015279 : Nat := 347550750277492299962215

theorem tailTrace_1015279 : CollatzResearch.WordTrace tailWord_1015279 prefixEnd_1015279 347550750277492299962215 := by
  unfold tailWord_1015279
  simp only [CollatzResearch.WordTrace]
  refine ⟨37030267288825053693560891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24686844859216702462373927 37030267288825053693560891)
  ·
    refine ⟨55545400933237580540341337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37030267288825053693560891 55545400933237580540341337)
    ·
      refine ⟨41659050699928185405256003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55545400933237580540341337 41659050699928185405256003)
      ·
        refine ⟨62488576049892278107884005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41659050699928185405256003 62488576049892278107884005)
        ·
          refine ⟨11716608009354802145228251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62488576049892278107884005 11716608009354802145228251)
          ·
            refine ⟨17574912014032203217842377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11716608009354802145228251 17574912014032203217842377)
            ·
              refine ⟨13181184010524152413381783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17574912014032203217842377 13181184010524152413381783)
              ·
                refine ⟨19771776015786228620072675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13181184010524152413381783 19771776015786228620072675)
                ·
                  refine ⟨29657664023679342930109013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19771776015786228620072675 29657664023679342930109013)
                  ·
                    refine ⟨347550750277492299962215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29657664023679342930109013 347550750277492299962215)
                    ·
                      rfl

theorem cell22_1015279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_1015279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015279 prefixEnd_1015279 := by exact prefixLift 1015279
  have htrace : WordTrace (prefixWord ++ tailWord_1015279) baseStart_1015279 baseEnd_1015279 := by
    simpa [prefixWord, tailWord_1015279, baseEnd_1015279] using wordTrace_append hprefix tailTrace_1015279
  have hstable : (prefixWord ++ tailWord_1015279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015279).length < 2 ^ (prefixWord ++ tailWord_1015279).sum := by decide
  have hdescent : baseEnd_1015279 < baseStart_1015279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015300 : List Nat := [2, 3, 2, 3, 2, 2, 2, 6]
def baseStart_1015300 : Nat := 118140960795 + 1015300 * 2 ^ 59
def prefixEnd_1015300 : Nat := 4983230072969 + 3 ^ 40 * 1015300 * 2
def baseEnd_1015300 : Nat := 38617548778517249465239

theorem tailTrace_1015300 : CollatzResearch.WordTrace tailWord_1015300 prefixEnd_1015300 38617548778517249465239 := by
  unfold tailWord_1015300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515516610874487140037677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24687355481165982853383569 18515516610874487140037677)
  ·
    refine ⟨6943318729077932677514129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18515516610874487140037677 6943318729077932677514129)
    ·
      refine ⟨5207489046808449508135597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6943318729077932677514129 5207489046808449508135597)
      ·
        refine ⟨1952808392553168565550849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5207489046808449508135597 1952808392553168565550849)
        ·
          refine ⟨1464606294414876424163137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952808392553168565550849 1464606294414876424163137)
          ·
            refine ⟨1098454720811157318122353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1464606294414876424163137 1098454720811157318122353)
            ·
              refine ⟨823841040608367988591765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1098454720811157318122353 823841040608367988591765)
              ·
                refine ⟨38617548778517249465239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 823841040608367988591765 38617548778517249465239)
                ·
                  rfl

theorem cell22_1015300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 6].length) (baseStart_1015300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015300 prefixEnd_1015300 := by exact prefixLift 1015300
  have htrace : WordTrace (prefixWord ++ tailWord_1015300) baseStart_1015300 baseEnd_1015300 := by
    simpa [prefixWord, tailWord_1015300, baseEnd_1015300] using wordTrace_append hprefix tailTrace_1015300
  have hstable : (prefixWord ++ tailWord_1015300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015300).length < 2 ^ (prefixWord ++ tailWord_1015300).sum := by decide
  have hdescent : baseEnd_1015300 < baseStart_1015300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015315 : List Nat := [1, 1, 1, 2, 1, 6, 3, 3, 1, 3]
def baseStart_1015315 : Nat := 118140960795 + 1015315 * 2 ^ 59
def prefixEnd_1015315 : Nat := 4983230072969 + 3 ^ 40 * 1015315 * 2
def baseEnd_1015315 : Nat := 347563073813200206062105

theorem tailTrace_1015315 : CollatzResearch.WordTrace tailWord_1015315 prefixEnd_1015315 347563073813200206062105 := by
  unfold tailWord_1015315
  simp only [CollatzResearch.WordTrace]
  refine ⟨37031580316694631841871399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24687720211129754561247599 37031580316694631841871399)
  ·
    refine ⟨55547370475041947762807099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37031580316694631841871399 55547370475041947762807099)
    ·
      refine ⟨83321055712562921644210649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55547370475041947762807099 83321055712562921644210649)
      ·
        refine ⟨62490791784422191233157987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83321055712562921644210649 62490791784422191233157987)
        ·
          refine ⟨93736187676633286849736981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62490791784422191233157987 93736187676633286849736981)
          ·
            refine ⟨4393883797342185321081421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93736187676633286849736981 4393883797342185321081421)
            ·
              refine ⟨1647706424003319495405533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4393883797342185321081421 1647706424003319495405533)
              ·
                refine ⟨617889909001244810777075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647706424003319495405533 617889909001244810777075)
                ·
                  refine ⟨926834863501867216165613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617889909001244810777075 926834863501867216165613)
                  ·
                    refine ⟨347563073813200206062105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926834863501867216165613 347563073813200206062105)
                    ·
                      rfl

theorem cell22_1015315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 1, 3].length) (baseStart_1015315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015315 prefixEnd_1015315 := by exact prefixLift 1015315
  have htrace : WordTrace (prefixWord ++ tailWord_1015315) baseStart_1015315 baseEnd_1015315 := by
    simpa [prefixWord, tailWord_1015315, baseEnd_1015315] using wordTrace_append hprefix tailTrace_1015315
  have hstable : (prefixWord ++ tailWord_1015315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015315).length < 2 ^ (prefixWord ++ tailWord_1015315).sum := by decide
  have hdescent : baseEnd_1015315 < baseStart_1015315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015401 : List Nat := [1, 2, 1, 1, 1, 4, 5, 7]
def baseStart_1015401 : Nat := 118140960795 + 1015401 * 2 ^ 59
def prefixEnd_1015401 : Nat := 4983230072969 + 3 ^ 40 * 1015401 * 2
def baseEnd_1015401 : Nat := 38621390374524960934649

theorem tailTrace_1015401 : CollatzResearch.WordTrace tailWord_1015401 prefixEnd_1015401 38621390374524960934649 := by
  unfold tailWord_1015401
  simp only [CollatzResearch.WordTrace]
  refine ⟨37034716994383068529502057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24689811329588712353001371 37034716994383068529502057)
  ·
    refine ⟨27776037745787301397126543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37034716994383068529502057 27776037745787301397126543)
    ·
      refine ⟨41664056618680952095689815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27776037745787301397126543 41664056618680952095689815)
      ·
        refine ⟨62496084928021428143534723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41664056618680952095689815 62496084928021428143534723)
        ·
          refine ⟨93744127392032142215302085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62496084928021428143534723 93744127392032142215302085)
          ·
            refine ⟨17577023886006026665369141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93744127392032142215302085 17577023886006026665369141)
            ·
              refine ⟨1647845989313064999878357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17577023886006026665369141 1647845989313064999878357)
              ·
                refine ⟨38621390374524960934649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1647845989313064999878357 38621390374524960934649)
                ·
                  rfl

theorem cell22_1015401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 7].length) (baseStart_1015401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015401 prefixEnd_1015401 := by exact prefixLift 1015401
  have htrace : WordTrace (prefixWord ++ tailWord_1015401) baseStart_1015401 baseEnd_1015401 := by
    simpa [prefixWord, tailWord_1015401, baseEnd_1015401] using wordTrace_append hprefix tailTrace_1015401
  have hstable : (prefixWord ++ tailWord_1015401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015401).length < 2 ^ (prefixWord ++ tailWord_1015401).sum := by decide
  have hdescent : baseEnd_1015401 < baseStart_1015401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015405 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1015405 : Nat := 118140960795 + 1015405 * 2 ^ 59
def prefixEnd_1015405 : Nat := 4983230072969 + 3 ^ 40 * 1015405 * 2
def baseEnd_1015405 : Nat := 347593882652469971311829

theorem tailTrace_1015405 : CollatzResearch.WordTrace tailWord_1015405 prefixEnd_1015405 347593882652469971311829 := by
  unfold tailWord_1015405
  simp only [CollatzResearch.WordTrace]
  refine ⟨37034862886368577212647669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24689908590912384808431779 37034862886368577212647669)
  ·
    refine ⟨3472018395597054113685719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37034862886368577212647669 3472018395597054113685719)
    ·
      refine ⟨5208027593395581170528579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3472018395597054113685719 5208027593395581170528579)
      ·
        refine ⟨7812041390093371755792869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5208027593395581170528579 7812041390093371755792869)
        ·
          refine ⟨1464757760642507204211163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7812041390093371755792869 1464757760642507204211163)
          ·
            refine ⟨2197136640963760806316745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464757760642507204211163 2197136640963760806316745)
            ·
              refine ⟨1647852480722820604737559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2197136640963760806316745 1647852480722820604737559)
              ·
                refine ⟨2471778721084230907106339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1647852480722820604737559 2471778721084230907106339)
                ·
                  refine ⟨3707668081626346360659509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471778721084230907106339 3707668081626346360659509)
                  ·
                    refine ⟨347593882652469971311829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3707668081626346360659509 347593882652469971311829)
                    ·
                      rfl

theorem cell22_1015405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1015405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015405 prefixEnd_1015405 := by exact prefixLift 1015405
  have htrace : WordTrace (prefixWord ++ tailWord_1015405) baseStart_1015405 baseEnd_1015405 := by
    simpa [prefixWord, tailWord_1015405, baseEnd_1015405] using wordTrace_append hprefix tailTrace_1015405
  have hstable : (prefixWord ++ tailWord_1015405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015405).length < 2 ^ (prefixWord ++ tailWord_1015405).sum := by decide
  have hdescent : baseEnd_1015405 < baseStart_1015405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015484 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_1015484 : Nat := 118140960795 + 1015484 * 2 ^ 59
def prefixEnd_1015484 : Nat := 4983230072969 + 3 ^ 40 * 1015484 * 2
def baseEnd_1015484 : Nat := 347620925966940098586587

theorem tailTrace_1015484 : CollatzResearch.WordTrace tailWord_1015484 prefixEnd_1015484 347620925966940098586587 := by
  unfold tailWord_1015484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518872126541186852386753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24691829502054915803182337 18518872126541186852386753)
  ·
    refine ⟨13889154094905890139290065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18518872126541186852386753 13889154094905890139290065)
    ·
      refine ⟨10416865571179417604467549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13889154094905890139290065 10416865571179417604467549)
      ·
        refine ⟨3906324589192281601675331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10416865571179417604467549 3906324589192281601675331)
        ·
          refine ⟨5859486883788422402512997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906324589192281601675331 5859486883788422402512997)
          ·
            refine ⟨1098653790710329200471187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5859486883788422402512997 1098653790710329200471187)
            ·
              refine ⟨1647980686065493800706781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098653790710329200471187 1647980686065493800706781)
              ·
                refine ⟨617992757274560175265043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1647980686065493800706781 617992757274560175265043)
                ·
                  refine ⟨926989135911840262897565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 617992757274560175265043 926989135911840262897565)
                  ·
                    refine ⟨347620925966940098586587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 926989135911840262897565 347620925966940098586587)
                    ·
                      rfl

theorem cell22_1015484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_1015484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015484 prefixEnd_1015484 := by exact prefixLift 1015484
  have htrace : WordTrace (prefixWord ++ tailWord_1015484) baseStart_1015484 baseEnd_1015484 := by
    simpa [prefixWord, tailWord_1015484, baseEnd_1015484] using wordTrace_append hprefix tailTrace_1015484
  have hstable : (prefixWord ++ tailWord_1015484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015484).length < 2 ^ (prefixWord ++ tailWord_1015484).sum := by decide
  have hdescent : baseEnd_1015484 < baseStart_1015484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015527 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1015527 : Nat := 118140960795 + 1015527 * 2 ^ 59
def prefixEnd_1015527 : Nat := 4983230072969 + 3 ^ 40 * 1015527 * 2
def baseEnd_1015527 : Nat := 347635645745702319761455

theorem tailTrace_1015527 : CollatzResearch.WordTrace tailWord_1015527 prefixEnd_1015527 347635645745702319761455 := by
  unfold tailWord_1015527
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039312591926592048588835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24692875061284394699059223 37039312591926592048588835)
  ·
    refine ⟨55558968887889888072883253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37039312591926592048588835 55558968887889888072883253)
    ·
      refine ⟨5208653333239677006832805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55558968887889888072883253 5208653333239677006832805)
      ·
        refine ⟨976622499982439438781151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5208653333239677006832805 976622499982439438781151)
        ·
          refine ⟨1464933749973659158171727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 976622499982439438781151 1464933749973659158171727)
          ·
            refine ⟨2197400624960488737257591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464933749973659158171727 2197400624960488737257591)
            ·
              refine ⟨3296100937440733105886387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197400624960488737257591 3296100937440733105886387)
              ·
                refine ⟨4944151406161099658829581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296100937440733105886387 4944151406161099658829581)
                ·
                  refine ⟨1854056777310412372061093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4944151406161099658829581 1854056777310412372061093)
                  ·
                    refine ⟨347635645745702319761455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1854056777310412372061093 347635645745702319761455)
                    ·
                      rfl

theorem cell22_1015527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1015527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015527 prefixEnd_1015527 := by exact prefixLift 1015527
  have htrace : WordTrace (prefixWord ++ tailWord_1015527) baseStart_1015527 baseEnd_1015527 := by
    simpa [prefixWord, tailWord_1015527, baseEnd_1015527] using wordTrace_append hprefix tailTrace_1015527
  have hstable : (prefixWord ++ tailWord_1015527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015527).length < 2 ^ (prefixWord ++ tailWord_1015527).sum := by decide
  have hdescent : baseEnd_1015527 < baseStart_1015527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015583 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_1015583 : Nat := 118140960795 + 1015583 * 2 ^ 59
def prefixEnd_1015583 : Nat := 4983230072969 + 3 ^ 40 * 1015583 * 2
def baseEnd_1015583 : Nat := 347654815690136840361283

theorem tailTrace_1015583 : CollatzResearch.WordTrace tailWord_1015583 prefixEnd_1015583 347654815690136840361283 := by
  unfold tailWord_1015583
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041355079723713612627403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24694236719815809075084935 37041355079723713612627403)
  ·
    refine ⟨55562032619585570418941105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37041355079723713612627403 55562032619585570418941105)
    ·
      refine ⟨41671524464689177814205829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55562032619585570418941105 41671524464689177814205829)
      ·
        refine ⟨7813410837129220840163593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41671524464689177814205829 7813410837129220840163593)
        ·
          refine ⟨5860058127846915630122695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7813410837129220840163593 5860058127846915630122695)
          ·
            refine ⟨8790087191770373445184043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860058127846915630122695 8790087191770373445184043)
            ·
              refine ⟨13185130787655560167776065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8790087191770373445184043 13185130787655560167776065)
              ·
                refine ⟨9888848090741670125832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13185130787655560167776065 9888848090741670125832049)
                ·
                  refine ⟨7416636068056252594374037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9888848090741670125832049 7416636068056252594374037)
                  ·
                    refine ⟨347654815690136840361283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7416636068056252594374037 347654815690136840361283)
                    ·
                      rfl

theorem cell22_1015583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_1015583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015583 prefixEnd_1015583 := by exact prefixLift 1015583
  have htrace : WordTrace (prefixWord ++ tailWord_1015583) baseStart_1015583 baseEnd_1015583 := by
    simpa [prefixWord, tailWord_1015583, baseEnd_1015583] using wordTrace_append hprefix tailTrace_1015583
  have hstable : (prefixWord ++ tailWord_1015583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015583).length < 2 ^ (prefixWord ++ tailWord_1015583).sum := by decide
  have hdescent : baseEnd_1015583 < baseStart_1015583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015585 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_1015585 : Nat := 118140960795 + 1015585 * 2 ^ 59
def prefixEnd_1015585 : Nat := 4983230072969 + 3 ^ 40 * 1015585 * 2
def baseEnd_1015585 : Nat := 347655500331009501811277

theorem tailTrace_1015585 : CollatzResearch.WordTrace tailWord_1015585 prefixEnd_1015585 347655500331009501811277 := by
  unfold tailWord_1015585
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041428025716467954200209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24694285350477645302800139 37041428025716467954200209)
  ·
    refine ⟨27781071019287350965650157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37041428025716467954200209 27781071019287350965650157)
    ·
      refine ⟨10417901632232756612118809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27781071019287350965650157 10417901632232756612118809)
      ·
        refine ⟨7813426224174567459089107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10417901632232756612118809 7813426224174567459089107)
        ·
          refine ⟨11720139336261851188633661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813426224174567459089107 11720139336261851188633661)
          ·
            refine ⟨4395052251098194195737623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11720139336261851188633661 4395052251098194195737623)
            ·
              refine ⟨6592578376647291293606435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395052251098194195737623 6592578376647291293606435)
              ·
                refine ⟨9888867564970936940409653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6592578376647291293606435 9888867564970936940409653)
                ·
                  refine ⟨927081334216025338163405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9888867564970936940409653 927081334216025338163405)
                  ·
                    refine ⟨347655500331009501811277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 927081334216025338163405 347655500331009501811277)
                    ·
                      rfl

theorem cell22_1015585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_1015585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015585 prefixEnd_1015585 := by exact prefixLift 1015585
  have htrace : WordTrace (prefixWord ++ tailWord_1015585) baseStart_1015585 baseEnd_1015585 := by
    simpa [prefixWord, tailWord_1015585, baseEnd_1015585] using wordTrace_append hprefix tailTrace_1015585
  have hstable : (prefixWord ++ tailWord_1015585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015585).length < 2 ^ (prefixWord ++ tailWord_1015585).sum := by decide
  have hdescent : baseEnd_1015585 < baseStart_1015585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015615 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 7]
def baseStart_1015615 : Nat := 118140960795 + 1015615 * 2 ^ 59
def prefixEnd_1015615 : Nat := 4983230072969 + 3 ^ 40 * 1015615 * 2
def baseEnd_1015615 : Nat := 115888589981366474520395

theorem tailTrace_1015615 : CollatzResearch.WordTrace tailWord_1015615 prefixEnd_1015615 115888589981366474520395 := by
  unfold tailWord_1015615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042522215607783077792299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24695014810405188718528199 37042522215607783077792299)
  ·
    refine ⟨55563783323411674616688449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37042522215607783077792299 55563783323411674616688449)
    ·
      refine ⟨41672837492558755962516337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55563783323411674616688449 41672837492558755962516337)
      ·
        refine ⟨31254628119419066971887253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41672837492558755962516337 31254628119419066971887253)
        ·
          refine ⟨1465060693097768764307215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31254628119419066971887253 1465060693097768764307215)
          ·
            refine ⟨2197591039646653146460823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465060693097768764307215 2197591039646653146460823)
            ·
              refine ⟨3296386559469979719691235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197591039646653146460823 3296386559469979719691235)
              ·
                refine ⟨4944579839204969579536853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296386559469979719691235 4944579839204969579536853)
                ·
                  refine ⟨115888589981366474520395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4944579839204969579536853 115888589981366474520395)
                  ·
                    rfl

theorem cell22_1015615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 7].length) (baseStart_1015615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015615 prefixEnd_1015615 := by exact prefixLift 1015615
  have htrace : WordTrace (prefixWord ++ tailWord_1015615) baseStart_1015615 baseEnd_1015615 := by
    simpa [prefixWord, tailWord_1015615, baseEnd_1015615] using wordTrace_append hprefix tailTrace_1015615
  have hstable : (prefixWord ++ tailWord_1015615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015615).length < 2 ^ (prefixWord ++ tailWord_1015615).sum := by decide
  have hdescent : baseEnd_1015615 < baseStart_1015615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015737 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_1015737 : Nat := 118140960795 + 1015737 * 2 ^ 59
def prefixEnd_1015737 : Nat := 4983230072969 + 3 ^ 40 * 1015737 * 2
def baseEnd_1015737 : Nat := 347707533037331772010811

theorem tailTrace_1015737 : CollatzResearch.WordTrace tailWord_1015737 prefixEnd_1015737 347707533037331772010811 := by
  unfold tailWord_1015737
  simp only [CollatzResearch.WordTrace]
  refine ⟨37046971921165797913733465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24697981280777198609155643 37046971921165797913733465)
  ·
    refine ⟨27785228940874348435300099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37046971921165797913733465 27785228940874348435300099)
    ·
      refine ⟨41677843411311522652950149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27785228940874348435300099 41677843411311522652950149)
      ·
        refine ⟨7814595639620910497428153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41677843411311522652950149 7814595639620910497428153)
        ·
          refine ⟨5860946729715682873071115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7814595639620910497428153 5860946729715682873071115)
          ·
            refine ⟨8791420094573524309606673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860946729715682873071115 8791420094573524309606673)
            ·
              refine ⟨6593565070930143232205005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791420094573524309606673 6593565070930143232205005)
              ·
                refine ⟨2472586901598803712076877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6593565070930143232205005 2472586901598803712076877)
                ·
                  refine ⟨927220088099551392028829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2472586901598803712076877 927220088099551392028829)
                  ·
                    refine ⟨347707533037331772010811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 927220088099551392028829 347707533037331772010811)
                    ·
                      rfl

theorem cell22_1015737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_1015737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015737 prefixEnd_1015737 := by exact prefixLift 1015737
  have htrace : WordTrace (prefixWord ++ tailWord_1015737) baseStart_1015737 baseEnd_1015737 := by
    simpa [prefixWord, tailWord_1015737, baseEnd_1015737] using wordTrace_append hprefix tailTrace_1015737
  have hstable : (prefixWord ++ tailWord_1015737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015737).length < 2 ^ (prefixWord ++ tailWord_1015737).sum := by decide
  have hdescent : baseEnd_1015737 < baseStart_1015737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015827 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 4, 3]
def baseStart_1015827 : Nat := 118140960795 + 1015827 * 2 ^ 59
def prefixEnd_1015827 : Nat := 4983230072969 + 3 ^ 40 * 1015827 * 2
def baseEnd_1015827 : Nat := 347738341876601537260535

theorem tailTrace_1015827 : CollatzResearch.WordTrace tailWord_1015827 prefixEnd_1015827 347738341876601537260535 := by
  unfold tailWord_1015827
  simp only [CollatzResearch.WordTrace]
  refine ⟨37050254490839743284509735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24700169660559828856339823 37050254490839743284509735)
  ·
    refine ⟨55575381736259614926764603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37050254490839743284509735 55575381736259614926764603)
    ·
      refine ⟨83363072604389422390146905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55575381736259614926764603 83363072604389422390146905)
      ·
        refine ⟨62522304453292066792610179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83363072604389422390146905 62522304453292066792610179)
        ·
          refine ⟨93783456679938100188915269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62522304453292066792610179 93783456679938100188915269)
          ·
            refine ⟨17584398127488393785421613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93783456679938100188915269 17584398127488393785421613)
            ·
              refine ⟨6594149297808147669533105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17584398127488393785421613 6594149297808147669533105)
              ·
                refine ⟨4945611973356110752149829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594149297808147669533105 4945611973356110752149829)
                ·
                  refine ⟨927302245004270766028093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4945611973356110752149829 927302245004270766028093)
                  ·
                    refine ⟨347738341876601537260535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 927302245004270766028093 347738341876601537260535)
                    ·
                      rfl

theorem cell22_1015827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 3].length) (baseStart_1015827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015827 prefixEnd_1015827 := by exact prefixLift 1015827
  have htrace : WordTrace (prefixWord ++ tailWord_1015827) baseStart_1015827 baseEnd_1015827 := by
    simpa [prefixWord, tailWord_1015827, baseEnd_1015827] using wordTrace_append hprefix tailTrace_1015827
  have hstable : (prefixWord ++ tailWord_1015827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015827).length < 2 ^ (prefixWord ++ tailWord_1015827).sum := by decide
  have hdescent : baseEnd_1015827 < baseStart_1015827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015855 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_1015855 : Nat := 118140960795 + 1015855 * 2 ^ 59
def prefixEnd_1015855 : Nat := 4983230072969 + 3 ^ 40 * 1015855 * 2
def baseEnd_1015855 : Nat := 347747926848818797560449

theorem tailTrace_1015855 : CollatzResearch.WordTrace tailWord_1015855 prefixEnd_1015855 347747926848818797560449 := by
  unfold tailWord_1015855
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051275734738304066529019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24700850489825536044352679 37051275734738304066529019)
  ·
    refine ⟨55576913602107456099793529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37051275734738304066529019 55576913602107456099793529)
    ·
      refine ⟨41682685201580592074845147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55576913602107456099793529 41682685201580592074845147)
      ·
        refine ⟨62524027802370888112267721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41682685201580592074845147 62524027802370888112267721)
        ·
          refine ⟨46893020851778166084200791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62524027802370888112267721 46893020851778166084200791)
          ·
            refine ⟨70339531277667249126301187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46893020851778166084200791 70339531277667249126301187)
            ·
              refine ⟨105509296916500873689451781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70339531277667249126301187 105509296916500873689451781)
              ·
                refine ⟨19782993171843913816772209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105509296916500873689451781 19782993171843913816772209)
                ·
                  refine ⟨14837244878882935362579157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19782993171843913816772209 14837244878882935362579157)
                  ·
                    refine ⟨347747926848818797560449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14837244878882935362579157 347747926848818797560449)
                    ·
                      rfl

theorem cell22_1015855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_1015855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015855 prefixEnd_1015855 := by exact prefixLift 1015855
  have htrace : WordTrace (prefixWord ++ tailWord_1015855) baseStart_1015855 baseEnd_1015855 := by
    simpa [prefixWord, tailWord_1015855, baseEnd_1015855] using wordTrace_append hprefix tailTrace_1015855
  have hstable : (prefixWord ++ tailWord_1015855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015855).length < 2 ^ (prefixWord ++ tailWord_1015855).sum := by decide
  have hdescent : baseEnd_1015855 < baseStart_1015855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015857 : List Nat := [1, 2, 2, 3, 1, 4, 2, 7]
def baseStart_1015857 : Nat := 118140960795 + 1015857 * 2 ^ 59
def prefixEnd_1015857 : Nat := 4983230072969 + 3 ^ 40 * 1015857 * 2
def baseEnd_1015857 : Nat := 38638734609965717667827

theorem tailTrace_1015857 : CollatzResearch.WordTrace tailWord_1015857 prefixEnd_1015857 38638734609965717667827 := by
  unfold tailWord_1015857
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051348680731058408101825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24700899120487372272067883 37051348680731058408101825)
  ·
    refine ⟨27788511510548293806076369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37051348680731058408101825 27788511510548293806076369)
    ·
      refine ⟨20841383632911220354557277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27788511510548293806076369 20841383632911220354557277)
      ·
        refine ⟨7815518862341707632958979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20841383632911220354557277 7815518862341707632958979)
        ·
          refine ⟨11723278293512561449438469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815518862341707632958979 11723278293512561449438469)
          ·
            refine ⟨2198114680033605271769713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11723278293512561449438469 2198114680033605271769713)
            ·
              refine ⟨1648586010025203953827285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198114680033605271769713 1648586010025203953827285)
              ·
                refine ⟨38638734609965717667827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1648586010025203953827285 38638734609965717667827)
                ·
                  rfl

theorem cell22_1015857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 7].length) (baseStart_1015857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015857 prefixEnd_1015857 := by exact prefixLift 1015857
  have htrace : WordTrace (prefixWord ++ tailWord_1015857) baseStart_1015857 baseEnd_1015857 := by
    simpa [prefixWord, tailWord_1015857, baseEnd_1015857] using wordTrace_append hprefix tailTrace_1015857
  have hstable : (prefixWord ++ tailWord_1015857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015857).length < 2 ^ (prefixWord ++ tailWord_1015857).sum := by decide
  have hdescent : baseEnd_1015857 < baseStart_1015857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015861 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1015861 : Nat := 118140960795 + 1015861 * 2 ^ 59
def prefixEnd_1015861 : Nat := 4983230072969 + 3 ^ 40 * 1015861 * 2
def baseEnd_1015861 : Nat := 347749980771436781910431

theorem tailTrace_1015861 : CollatzResearch.WordTrace tailWord_1015861 prefixEnd_1015861 347749980771436781910431 := by
  unfold tailWord_1015861
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051494572716567091247437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24700996381811044727498291 37051494572716567091247437)
  ·
    refine ⟨13894310464768712659217789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37051494572716567091247437 13894310464768712659217789)
    ·
      refine ⟨5210366424288267247206671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13894310464768712659217789 5210366424288267247206671)
      ·
        refine ⟨7815549636432400870810007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210366424288267247206671 7815549636432400870810007)
        ·
          refine ⟨11723324454648601306215011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815549636432400870810007 11723324454648601306215011)
          ·
            refine ⟨17584986681972901959322517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11723324454648601306215011 17584986681972901959322517)
            ·
              refine ⟨824296250717479779343243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17584986681972901959322517 824296250717479779343243)
              ·
                refine ⟨1236444376076219669014865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824296250717479779343243 1236444376076219669014865)
                ·
                  refine ⟨927333282057164751761149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1236444376076219669014865 927333282057164751761149)
                  ·
                    refine ⟨347749980771436781910431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 927333282057164751761149 347749980771436781910431)
                    ·
                      rfl

theorem cell22_1015861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1015861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015861 prefixEnd_1015861 := by exact prefixLift 1015861
  have htrace : WordTrace (prefixWord ++ tailWord_1015861) baseStart_1015861 baseEnd_1015861 := by
    simpa [prefixWord, tailWord_1015861, baseEnd_1015861] using wordTrace_append hprefix tailTrace_1015861
  have hstable : (prefixWord ++ tailWord_1015861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015861).length < 2 ^ (prefixWord ++ tailWord_1015861).sum := by decide
  have hdescent : baseEnd_1015861 < baseStart_1015861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015964 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_1015964 : Nat := 118140960795 + 1015964 * 2 ^ 59
def prefixEnd_1015964 : Nat := 4983230072969 + 3 ^ 40 * 1015964 * 2
def baseEnd_1015964 : Nat := 115928413258792948861705

theorem tailTrace_1015964 : CollatzResearch.WordTrace tailWord_1015964 prefixEnd_1015964 115928413258792948861705 := by
  unfold tailWord_1015964
  simp only [CollatzResearch.WordTrace]
  refine ⟨18527625645671707841123473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24703500860895610454831297 18527625645671707841123473)
  ·
    refine ⟨13895719234253780880842605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18527625645671707841123473 13895719234253780880842605)
    ·
      refine ⟨5210894712845167830315977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13895719234253780880842605 5210894712845167830315977)
      ·
        refine ⟨3908171034633875872736983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5210894712845167830315977 3908171034633875872736983)
        ·
          refine ⟨5862256551950813809105475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908171034633875872736983 5862256551950813809105475)
          ·
            refine ⟨8793384827926220713658213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862256551950813809105475 8793384827926220713658213)
            ·
              refine ⟨1648759655236166383810915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8793384827926220713658213 1648759655236166383810915)
              ·
                refine ⟨2473139482854249575716373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1648759655236166383810915 2473139482854249575716373)
                ·
                  refine ⟨115928413258792948861705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2473139482854249575716373 115928413258792948861705)
                  ·
                    rfl

theorem cell22_1015964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_1015964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015964 prefixEnd_1015964 := by exact prefixLift 1015964
  have htrace : WordTrace (prefixWord ++ tailWord_1015964) baseStart_1015964 baseEnd_1015964 := by
    simpa [prefixWord, tailWord_1015964, baseEnd_1015964] using wordTrace_append hprefix tailTrace_1015964
  have hstable : (prefixWord ++ tailWord_1015964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015964).length < 2 ^ (prefixWord ++ tailWord_1015964).sum := by decide
  have hdescent : baseEnd_1015964 < baseStart_1015964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1015992 : List Nat := [2, 1, 2, 1, 2, 1, 5, 8]
def baseStart_1015992 : Nat := 118140960795 + 1015992 * 2 ^ 59
def prefixEnd_1015992 : Nat := 4983230072969 + 3 ^ 40 * 1015992 * 2
def baseEnd_1015992 : Nat := 38643869416510678542781

theorem tailTrace_1015992 : CollatzResearch.WordTrace tailWord_1015992 prefixEnd_1015992 38643869416510678542781 := by
  unfold tailWord_1015992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528136267620988232133115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24704181690161317642844153 18528136267620988232133115)
  ·
    refine ⟨27792204401431482348199673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18528136267620988232133115 27792204401431482348199673)
    ·
      refine ⟨20844153301073611761149755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27792204401431482348199673 20844153301073611761149755)
      ·
        refine ⟨31266229951610417641724633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20844153301073611761149755 31266229951610417641724633)
        ·
          refine ⟨23449672463707813231293475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31266229951610417641724633 23449672463707813231293475)
          ·
            refine ⟨35174508695561719846940213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23449672463707813231293475 35174508695561719846940213)
            ·
              refine ⟨3297610190208911235650645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35174508695561719846940213 3297610190208911235650645)
              ·
                refine ⟨38643869416510678542781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3297610190208911235650645 38643869416510678542781)
                ·
                  rfl

theorem cell22_1015992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_1015992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1015992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1015992 prefixEnd_1015992 := by exact prefixLift 1015992
  have htrace : WordTrace (prefixWord ++ tailWord_1015992) baseStart_1015992 baseEnd_1015992 := by
    simpa [prefixWord, tailWord_1015992, baseEnd_1015992] using wordTrace_append hprefix tailTrace_1015992
  have hstable : (prefixWord ++ tailWord_1015992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1015992).length < 2 ^ (prefixWord ++ tailWord_1015992).sum := by decide
  have hdescent : baseEnd_1015992 < baseStart_1015992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1015992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016034 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1016034 : Nat := 118140960795 + 1016034 * 2 ^ 59
def prefixEnd_1016034 : Nat := 4983230072969 + 3 ^ 40 * 1016034 * 2
def baseEnd_1016034 : Nat := 347809202206921997334901

theorem tailTrace_1016034 : CollatzResearch.WordTrace tailWord_1016034 prefixEnd_1016034 347809202206921997334901 := by
  unfold tailWord_1016034
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264451100272454409323789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24705202934059878424863437 9264451100272454409323789)
  ·
    refine ⟨3474169162602170403496421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9264451100272454409323789 3474169162602170403496421)
    ·
      refine ⟨651406717987906950655579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3474169162602170403496421 651406717987906950655579)
      ·
        refine ⟨977110076981860425983369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651406717987906950655579 977110076981860425983369)
        ·
          refine ⟨732832557736395319487527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 977110076981860425983369 732832557736395319487527)
          ·
            refine ⟨1099248836604592979231291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732832557736395319487527 1099248836604592979231291)
            ·
              refine ⟨1648873254906889468846937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099248836604592979231291 1648873254906889468846937)
              ·
                refine ⟨1236654941180167101635203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648873254906889468846937 1236654941180167101635203)
                ·
                  refine ⟨1854982411770250652452805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1236654941180167101635203 1854982411770250652452805)
                  ·
                    refine ⟨347809202206921997334901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1854982411770250652452805 347809202206921997334901)
                    ·
                      rfl

theorem cell22_1016034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1016034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016034 prefixEnd_1016034 := by exact prefixLift 1016034
  have htrace : WordTrace (prefixWord ++ tailWord_1016034) baseStart_1016034 baseEnd_1016034 := by
    simpa [prefixWord, tailWord_1016034, baseEnd_1016034] using wordTrace_append hprefix tailTrace_1016034
  have hstable : (prefixWord ++ tailWord_1016034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016034).length < 2 ^ (prefixWord ++ tailWord_1016034).sum := by decide
  have hdescent : baseEnd_1016034 < baseStart_1016034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016054 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1016054 : Nat := 118140960795 + 1016054 * 2 ^ 59
def prefixEnd_1016054 : Nat := 4983230072969 + 3 ^ 40 * 1016054 * 2
def baseEnd_1016054 : Nat := 115938682871882870611613

theorem tailTrace_1016054 : CollatzResearch.WordTrace tailWord_1016054 prefixEnd_1016054 115938682871882870611613 := by
  unfold tailWord_1016054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316158366313585065813951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24705689240678240702015477 2316158366313585065813951)
  ·
    refine ⟨3474237549470377598720927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2316158366313585065813951 3474237549470377598720927)
    ·
      refine ⟨5211356324205566398081391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474237549470377598720927 5211356324205566398081391)
      ·
        refine ⟨7817034486308349597122087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211356324205566398081391 7817034486308349597122087)
        ·
          refine ⟨11725551729462524395683131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817034486308349597122087 11725551729462524395683131)
          ·
            refine ⟨17588327594193786593524697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11725551729462524395683131 17588327594193786593524697)
            ·
              refine ⟨13191245695645339945143523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17588327594193786593524697 13191245695645339945143523)
              ·
                refine ⟨19786868543468009917715285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13191245695645339945143523 19786868543468009917715285)
                ·
                  refine ⟨115938682871882870611613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19786868543468009917715285 115938682871882870611613)
                  ·
                    rfl

theorem cell22_1016054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1016054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016054 prefixEnd_1016054 := by exact prefixLift 1016054
  have htrace : WordTrace (prefixWord ++ tailWord_1016054) baseStart_1016054 baseEnd_1016054 := by
    simpa [prefixWord, tailWord_1016054, baseEnd_1016054] using wordTrace_append hprefix tailTrace_1016054
  have hstable : (prefixWord ++ tailWord_1016054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016054).length < 2 ^ (prefixWord ++ tailWord_1016054).sum := by decide
  have hdescent : baseEnd_1016054 < baseStart_1016054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016099 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 6]
def baseStart_1016099 : Nat := 118140960795 + 1016099 * 2 ^ 59
def prefixEnd_1016099 : Nat := 4983230072969 + 3 ^ 40 * 1016099 * 2
def baseEnd_1016099 : Nat := 115943817678427831486567

theorem tailTrace_1016099 : CollatzResearch.WordTrace tailWord_1016099 prefixEnd_1016099 115943817678427831486567 := by
  unfold tailWord_1016099
  simp only [CollatzResearch.WordTrace]
  refine ⟨37060175145854333738411351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24706783430569555825607567 37060175145854333738411351)
  ·
    refine ⟨55590262718781500607617027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37060175145854333738411351 55590262718781500607617027)
    ·
      refine ⟨83385394078172250911425541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55590262718781500607617027 83385394078172250911425541)
      ·
        refine ⟨15634761389657297045892289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83385394078172250911425541 15634761389657297045892289)
        ·
          refine ⟨11726071042242972784419217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15634761389657297045892289 11726071042242972784419217)
          ·
            refine ⟨8794553281682229588314413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11726071042242972784419217 8794553281682229588314413)
            ·
              refine ⟨3297957480630836095617905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8794553281682229588314413 3297957480630836095617905)
              ·
                refine ⟨2473468110473127071713429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297957480630836095617905 2473468110473127071713429)
                ·
                  refine ⟨115943817678427831486567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2473468110473127071713429 115943817678427831486567)
                  ·
                    rfl

theorem cell22_1016099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_1016099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016099 prefixEnd_1016099 := by exact prefixLift 1016099
  have htrace : WordTrace (prefixWord ++ tailWord_1016099) baseStart_1016099 baseEnd_1016099 := by
    simpa [prefixWord, tailWord_1016099, baseEnd_1016099] using wordTrace_append hprefix tailTrace_1016099
  have hstable : (prefixWord ++ tailWord_1016099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016099).length < 2 ^ (prefixWord ++ tailWord_1016099).sum := by decide
  have hdescent : baseEnd_1016099 < baseStart_1016099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016148 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1016148 : Nat := 118140960795 + 1016148 * 2 ^ 59
def prefixEnd_1016148 : Nat := 4983230072969 + 3 ^ 40 * 1016148 * 2
def baseEnd_1016148 : Nat := 347848226736663699984551

theorem tailTrace_1016148 : CollatzResearch.WordTrace tailWord_1016148 prefixEnd_1016148 347848226736663699984551 := by
  unfold tailWord_1016148
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530981161338407553472549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24707974881784543404630065 18530981161338407553472549)
  ·
    refine ⟨3474558967750951416276103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18530981161338407553472549 3474558967750951416276103)
    ·
      refine ⟨5211838451626427124414155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474558967750951416276103 5211838451626427124414155)
      ·
        refine ⟨7817757677439640686621233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211838451626427124414155 7817757677439640686621233)
        ·
          refine ⟨5863318258079730514965925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7817757677439640686621233 5863318258079730514965925)
          ·
            refine ⟨1099372173389949471556111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5863318258079730514965925 1099372173389949471556111)
            ·
              refine ⟨1649058260084924207334167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099372173389949471556111 1649058260084924207334167)
              ·
                refine ⟨2473587390127386311001251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649058260084924207334167 2473587390127386311001251)
                ·
                  refine ⟨3710381085191079466501877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473587390127386311001251 3710381085191079466501877)
                  ·
                    refine ⟨347848226736663699984551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3710381085191079466501877 347848226736663699984551)
                    ·
                      rfl

theorem cell22_1016148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1016148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016148 prefixEnd_1016148 := by exact prefixLift 1016148
  have htrace : WordTrace (prefixWord ++ tailWord_1016148) baseStart_1016148 baseEnd_1016148 := by
    simpa [prefixWord, tailWord_1016148, baseEnd_1016148] using wordTrace_append hprefix tailTrace_1016148
  have hstable : (prefixWord ++ tailWord_1016148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016148).length < 2 ^ (prefixWord ++ tailWord_1016148).sum := by decide
  have hdescent : baseEnd_1016148 < baseStart_1016148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016214 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1016214 : Nat := 118140960795 + 1016214 * 2 ^ 59
def prefixEnd_1016214 : Nat := 4983230072969 + 3 ^ 40 * 1016214 * 2
def baseEnd_1016214 : Nat := 347870819885461527834349

theorem tailTrace_1016214 : CollatzResearch.WordTrace tailWord_1016214 prefixEnd_1016214 347870819885461527834349 := by
  unfold tailWord_1016214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2316523096277356773677981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24709579693625138919231797 2316523096277356773677981)
  ·
    refine ⟨868696161104008790129243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2316523096277356773677981 868696161104008790129243)
    ·
      refine ⟨1303044241656013185193865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868696161104008790129243 1303044241656013185193865)
      ·
        refine ⟨977283181242009888895399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1303044241656013185193865 977283181242009888895399)
        ·
          refine ⟨1465924771863014833343099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977283181242009888895399 1465924771863014833343099)
          ·
            refine ⟨2198887157794522250014649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465924771863014833343099 2198887157794522250014649)
            ·
              refine ⟨1649165368345891687510987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2198887157794522250014649 1649165368345891687510987)
              ·
                refine ⟨2473748052518837531266481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649165368345891687510987 2473748052518837531266481)
                ·
                  refine ⟨1855311039389128148449861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2473748052518837531266481 1855311039389128148449861)
                  ·
                    refine ⟨347870819885461527834349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855311039389128148449861 347870819885461527834349)
                    ·
                      rfl

theorem cell22_1016214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1016214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016214 prefixEnd_1016214 := by exact prefixLift 1016214
  have htrace : WordTrace (prefixWord ++ tailWord_1016214) baseStart_1016214 baseEnd_1016214 := by
    simpa [prefixWord, tailWord_1016214, baseEnd_1016214] using wordTrace_append hprefix tailTrace_1016214
  have hstable : (prefixWord ++ tailWord_1016214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016214).length < 2 ^ (prefixWord ++ tailWord_1016214).sum := by decide
  have hdescent : baseEnd_1016214 < baseStart_1016214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016268 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_1016268 : Nat := 118140960795 + 1016268 * 2 ^ 59
def prefixEnd_1016268 : Nat := 4983230072969 + 3 ^ 40 * 1016268 * 2
def baseEnd_1016268 : Nat := 115963101729674462328061

theorem tailTrace_1016268 : CollatzResearch.WordTrace tailWord_1016268 prefixEnd_1016268 115963101729674462328061 := by
  unfold tailWord_1016268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18533169541121037800656729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24710892721494717067542305 18533169541121037800656729)
  ·
    refine ⟨13899877155840778350492547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18533169541121037800656729 13899877155840778350492547)
    ·
      refine ⟨20849815733761167525738821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13899877155840778350492547 20849815733761167525738821)
      ·
        refine ⟨3909340450080218911076029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20849815733761167525738821 3909340450080218911076029)
        ·
          refine ⟨1466002668780082091653511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3909340450080218911076029 1466002668780082091653511)
          ·
            refine ⟨2199004003170123137480267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466002668780082091653511 2199004003170123137480267)
            ·
              refine ⟨3298506004755184706220401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199004003170123137480267 3298506004755184706220401)
              ·
                refine ⟨2473879503566388529665301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3298506004755184706220401 2473879503566388529665301)
                ·
                  refine ⟨115963101729674462328061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2473879503566388529665301 115963101729674462328061)
                  ·
                    rfl

theorem cell22_1016268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_1016268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016268 prefixEnd_1016268 := by exact prefixLift 1016268
  have htrace : WordTrace (prefixWord ++ tailWord_1016268) baseStart_1016268 baseEnd_1016268 := by
    simpa [prefixWord, tailWord_1016268, baseEnd_1016268] using wordTrace_append hprefix tailTrace_1016268
  have hstable : (prefixWord ++ tailWord_1016268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016268).length < 2 ^ (prefixWord ++ tailWord_1016268).sum := by decide
  have hdescent : baseEnd_1016268 < baseStart_1016268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016281 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_1016281 : Nat := 118140960795 + 1016281 * 2 ^ 59
def prefixEnd_1016281 : Nat := 4983230072969 + 3 ^ 40 * 1016281 * 2
def baseEnd_1016281 : Nat := 347893755354695686409143

theorem tailTrace_1016281 : CollatzResearch.WordTrace tailWord_1016281 prefixEnd_1016281 347893755354695686409143 := by
  unfold tailWord_1016281
  simp only [CollatzResearch.WordTrace]
  refine ⟨37066813231194978821536697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24711208820796652547691131 37066813231194978821536697)
  ·
    refine ⟨27800109923396234116152523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37066813231194978821536697 27800109923396234116152523)
    ·
      refine ⟨41700164885094351174228785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27800109923396234116152523 41700164885094351174228785)
      ·
        refine ⟨31275123663820763380671589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41700164885094351174228785 31275123663820763380671589)
        ·
          refine ⟨5864085686966393133875923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31275123663820763380671589 5864085686966393133875923)
          ·
            refine ⟨8796128530449589700813885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864085686966393133875923 8796128530449589700813885)
            ·
              refine ⟨3298548198918596137805207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8796128530449589700813885 3298548198918596137805207)
              ·
                refine ⟨4947822298377894206707811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298548198918596137805207 4947822298377894206707811)
                ·
                  refine ⟨7421733447566841310061717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4947822298377894206707811 7421733447566841310061717)
                  ·
                    refine ⟨347893755354695686409143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7421733447566841310061717 347893755354695686409143)
                    ·
                      rfl

theorem cell22_1016281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_1016281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016281 prefixEnd_1016281 := by exact prefixLift 1016281
  have htrace : WordTrace (prefixWord ++ tailWord_1016281) baseStart_1016281 baseEnd_1016281 := by
    simpa [prefixWord, tailWord_1016281, baseEnd_1016281] using wordTrace_append hprefix tailTrace_1016281
  have hstable : (prefixWord ++ tailWord_1016281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016281).length < 2 ^ (prefixWord ++ tailWord_1016281).sum := by decide
  have hdescent : baseEnd_1016281 < baseStart_1016281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016285 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 4]
def baseStart_1016285 : Nat := 118140960795 + 1016285 * 2 ^ 59
def prefixEnd_1016285 : Nat := 4983230072969 + 3 ^ 40 * 1016285 * 2
def baseEnd_1016285 : Nat := 115965041545480336436377

theorem tailTrace_1016285 : CollatzResearch.WordTrace tailWord_1016285 prefixEnd_1016285 115965041545480336436377 := by
  unfold tailWord_1016285
  simp only [CollatzResearch.WordTrace]
  refine ⟨37066959123180487504682309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24711306082120325003121539 37066959123180487504682309)
  ·
    refine ⟨6950054835596341407127933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37066959123180487504682309 6950054835596341407127933)
    ·
      refine ⟨2606270563348628027672975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6950054835596341407127933 2606270563348628027672975)
      ·
        refine ⟨3909405845022942041509463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606270563348628027672975 3909405845022942041509463)
        ·
          refine ⟨5864108767534413062264195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909405845022942041509463 5864108767534413062264195)
          ·
            refine ⟨8796163151301619593396293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864108767534413062264195 8796163151301619593396293)
            ·
              refine ⟨1649280590869053673761805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8796163151301619593396293 1649280590869053673761805)
              ·
                refine ⟨618480221575895127660677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1649280590869053673761805 618480221575895127660677)
                ·
                  refine ⟨115965041545480336436377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618480221575895127660677 115965041545480336436377)
                  ·
                    rfl

theorem cell22_1016285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_1016285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016285 prefixEnd_1016285 := by exact prefixLift 1016285
  have htrace : WordTrace (prefixWord ++ tailWord_1016285) baseStart_1016285 baseEnd_1016285 := by
    simpa [prefixWord, tailWord_1016285, baseEnd_1016285] using wordTrace_append hprefix tailTrace_1016285
  have hstable : (prefixWord ++ tailWord_1016285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016285).length < 2 ^ (prefixWord ++ tailWord_1016285).sum := by decide
  have hdescent : baseEnd_1016285 < baseStart_1016285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016296 : List Nat := [2, 1, 4, 1, 1, 4, 9]
def baseStart_1016296 : Nat := 118140960795 + 1016296 * 2 ^ 59
def prefixEnd_1016296 : Nat := 4983230072969 + 3 ^ 40 * 1016296 * 2
def baseEnd_1016296 : Nat := 12885144080045949899411

theorem tailTrace_1016296 : CollatzResearch.WordTrace tailWord_1016296 prefixEnd_1016296 12885144080045949899411 := by
  unfold tailWord_1016296
  simp only [CollatzResearch.WordTrace]
  refine ⟨18533680163070318191666371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24711573550760424255555161 18533680163070318191666371)
  ·
    refine ⟨27800520244605477287499557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18533680163070318191666371 27800520244605477287499557)
    ·
      refine ⟨5212597545863526991406167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27800520244605477287499557 5212597545863526991406167)
      ·
        refine ⟨7818896318795290487109251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212597545863526991406167 7818896318795290487109251)
        ·
          refine ⟨11728344478192935730663877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818896318795290487109251 11728344478192935730663877)
          ·
            refine ⟨2199064589661175449499477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11728344478192935730663877 2199064589661175449499477)
            ·
              refine ⟨12885144080045949899411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2199064589661175449499477 12885144080045949899411)
              ·
                rfl

theorem cell22_1016296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 9].length) (baseStart_1016296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016296 prefixEnd_1016296 := by exact prefixLift 1016296
  have htrace : WordTrace (prefixWord ++ tailWord_1016296) baseStart_1016296 baseEnd_1016296 := by
    simpa [prefixWord, tailWord_1016296, baseEnd_1016296] using wordTrace_append hprefix tailTrace_1016296
  have hstable : (prefixWord ++ tailWord_1016296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016296).length < 2 ^ (prefixWord ++ tailWord_1016296).sum := by decide
  have hdescent : baseEnd_1016296 < baseStart_1016296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016341 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 9]
def baseStart_1016341 : Nat := 118140960795 + 1016341 * 2 ^ 59
def prefixEnd_1016341 : Nat := 4983230072969 + 3 ^ 40 * 1016341 * 2
def baseEnd_1016341 : Nat := 115971431526958509969653

theorem tailTrace_1016341 : CollatzResearch.WordTrace tailWord_1016341 prefixEnd_1016341 115971431526958509969653 := by
  unfold tailWord_1016341
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069001610977609068720877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24712667740651739379147251 37069001610977609068720877)
  ·
    refine ⟨13900875604116603400770329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37069001610977609068720877 13900875604116603400770329)
    ·
      refine ⟨10425656703087452550577747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13900875604116603400770329 10425656703087452550577747)
      ·
        refine ⟨15638485054631178825866621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10425656703087452550577747 15638485054631178825866621)
        ·
          refine ⟨5864431895486692059699983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15638485054631178825866621 5864431895486692059699983)
          ·
            refine ⟨8796647843230038089549975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864431895486692059699983 8796647843230038089549975)
            ·
              refine ⟨13194971764845057134324963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796647843230038089549975 13194971764845057134324963)
              ·
                refine ⟨19792457647267585701487445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13194971764845057134324963 19792457647267585701487445)
                ·
                  refine ⟨115971431526958509969653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19792457647267585701487445 115971431526958509969653)
                  ·
                    rfl

theorem cell22_1016341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_1016341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016341 prefixEnd_1016341 := by exact prefixLift 1016341
  have htrace : WordTrace (prefixWord ++ tailWord_1016341) baseStart_1016341 baseEnd_1016341 := by
    simpa [prefixWord, tailWord_1016341, baseEnd_1016341] using wordTrace_append hprefix tailTrace_1016341
  have hstable : (prefixWord ++ tailWord_1016341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016341).length < 2 ^ (prefixWord ++ tailWord_1016341).sum := by decide
  have hdescent : baseEnd_1016341 < baseStart_1016341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016362 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1016362 : Nat := 118140960795 + 1016362 * 2 ^ 59
def prefixEnd_1016362 : Nat := 4983230072969 + 3 ^ 40 * 1016362 * 2
def baseEnd_1016362 : Nat := 347921483310038475133895

theorem tailTrace_1016362 : CollatzResearch.WordTrace tailWord_1016362 prefixEnd_1016362 347921483310038475133895 := by
  unfold tailWord_1016362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9267441885975382413808835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24713178362601019770156893 9267441885975382413808835)
  ·
    refine ⟨13901162828963073620713253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9267441885975382413808835 13901162828963073620713253)
    ·
      refine ⟨2606468030430576303883735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13901162828963073620713253 2606468030430576303883735)
      ·
        refine ⟨3909702045645864455825603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606468030430576303883735 3909702045645864455825603)
        ·
          refine ⟨5864553068468796683738405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909702045645864455825603 5864553068468796683738405)
          ·
            refine ⟨1099603700337899378200951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5864553068468796683738405 1099603700337899378200951)
            ·
              refine ⟨1649405550506849067301427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099603700337899378200951 1649405550506849067301427)
              ·
                refine ⟨2474108325760273600952141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649405550506849067301427 2474108325760273600952141)
                ·
                  refine ⟨927790622160102600357053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2474108325760273600952141 927790622160102600357053)
                  ·
                    refine ⟨347921483310038475133895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 927790622160102600357053 347921483310038475133895)
                    ·
                      rfl

theorem cell22_1016362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1016362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016362 prefixEnd_1016362 := by exact prefixLift 1016362
  have htrace : WordTrace (prefixWord ++ tailWord_1016362) baseStart_1016362 baseEnd_1016362 := by
    simpa [prefixWord, tailWord_1016362, baseEnd_1016362] using wordTrace_append hprefix tailTrace_1016362
  have hstable : (prefixWord ++ tailWord_1016362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016362).length < 2 ^ (prefixWord ++ tailWord_1016362).sum := by decide
  have hdescent : baseEnd_1016362 < baseStart_1016362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016420 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1016420 : Nat := 118140960795 + 1016420 * 2 ^ 59
def prefixEnd_1016420 : Nat := 4983230072969 + 3 ^ 40 * 1016420 * 2
def baseEnd_1016420 : Nat := 115980445965115219061239

theorem tailTrace_1016420 : CollatzResearch.WordTrace tailWord_1016420 prefixEnd_1016420 115980445965115219061239 := by
  unfold tailWord_1016420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535941488845702780423357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24714588651794270373897809 18535941488845702780423357)
  ·
    refine ⟨6950978058317138542658759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18535941488845702780423357 6950978058317138542658759)
    ·
      refine ⟨10426467087475707813988139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6950978058317138542658759 10426467087475707813988139)
      ·
        refine ⟨15639700631213561720982209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10426467087475707813988139 15639700631213561720982209)
        ·
          refine ⟨11729775473410171290736657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15639700631213561720982209 11729775473410171290736657)
          ·
            refine ⟨8797331605057628468052493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11729775473410171290736657 8797331605057628468052493)
            ·
              refine ⟨3298999351896610675519685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8797331605057628468052493 3298999351896610675519685)
              ·
                refine ⟨618562378480614501659941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3298999351896610675519685 618562378480614501659941)
                ·
                  refine ⟨115980445965115219061239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618562378480614501659941 115980445965115219061239)
                  ·
                    rfl

theorem cell22_1016420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1016420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016420 prefixEnd_1016420 := by exact prefixLift 1016420
  have htrace : WordTrace (prefixWord ++ tailWord_1016420) baseStart_1016420 baseEnd_1016420 := by
    simpa [prefixWord, tailWord_1016420, baseEnd_1016420] using wordTrace_append hprefix tailTrace_1016420
  have hstable : (prefixWord ++ tailWord_1016420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016420).length < 2 ^ (prefixWord ++ tailWord_1016420).sum := by decide
  have hdescent : baseEnd_1016420 < baseStart_1016420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016523 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 7, 4]
def baseStart_1016523 : Nat := 118140960795 + 1016523 * 2 ^ 59
def prefixEnd_1016523 : Nat := 4983230072969 + 3 ^ 40 * 1016523 * 2
def baseEnd_1016523 : Nat := 347976596900287721858401

theorem tailTrace_1016523 : CollatzResearch.WordTrace tailWord_1016523 prefixEnd_1016523 347976596900287721858401 := by
  unfold tailWord_1016523
  simp only [CollatzResearch.WordTrace]
  refine ⟨37075639696318254151846223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24717093130878836101230815 37075639696318254151846223)
  ·
    refine ⟨55613459544477381227769335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37075639696318254151846223 55613459544477381227769335)
    ·
      refine ⟨83420189316716071841654003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55613459544477381227769335 83420189316716071841654003)
      ·
        refine ⟨125130283975074107762481005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83420189316716071841654003 125130283975074107762481005)
        ·
          refine ⟨46923856490652790410930377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125130283975074107762481005 46923856490652790410930377)
          ·
            refine ⟨35192892367989592808197783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46923856490652790410930377 35192892367989592808197783)
            ·
              refine ⟨52789338551984389212296675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35192892367989592808197783 52789338551984389212296675)
              ·
                refine ⟨79184007827976583818445013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52789338551984389212296675 79184007827976583818445013)
                ·
                  refine ⟨1855875183468201183244805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 79184007827976583818445013 1855875183468201183244805)
                  ·
                    refine ⟨347976596900287721858401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855875183468201183244805 347976596900287721858401)
                    ·
                      rfl

theorem cell22_1016523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_1016523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016523 prefixEnd_1016523 := by exact prefixLift 1016523
  have htrace : WordTrace (prefixWord ++ tailWord_1016523) baseStart_1016523 baseEnd_1016523 := by
    simpa [prefixWord, tailWord_1016523, baseEnd_1016523] using wordTrace_append hprefix tailTrace_1016523
  have hstable : (prefixWord ++ tailWord_1016523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016523).length < 2 ^ (prefixWord ++ tailWord_1016523).sum := by decide
  have hdescent : baseEnd_1016523 < baseStart_1016523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016570 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_1016570 : Nat := 118140960795 + 1016570 * 2 ^ 59
def prefixEnd_1016570 : Nat := 4983230072969 + 3 ^ 40 * 1016570 * 2
def baseEnd_1016570 : Nat := 347992685960795265933257

theorem tailTrace_1016570 : CollatzResearch.WordTrace tailWord_1016570 prefixEnd_1016570 347992685960795265933257 := by
  unfold tailWord_1016570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9269338481786995294701791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24718235951431987452538109 9269338481786995294701791)
  ·
    refine ⟨13904007722680492942052687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9269338481786995294701791 13904007722680492942052687)
    ·
      refine ⟨20856011584020739413079031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13904007722680492942052687 20856011584020739413079031)
      ·
        refine ⟨31284017376031109119618547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20856011584020739413079031 31284017376031109119618547)
        ·
          refine ⟨46926026064046663679427821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31284017376031109119618547 46926026064046663679427821)
          ·
            refine ⟨17597259774017498879785433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46926026064046663679427821 17597259774017498879785433)
            ·
              refine ⟨13197944830513124159839075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17597259774017498879785433 13197944830513124159839075)
              ·
                refine ⟨19796917245769686239758613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13197944830513124159839075 19796917245769686239758613)
                ·
                  refine ⟨927980495895454042488685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19796917245769686239758613 927980495895454042488685)
                  ·
                    refine ⟨347992685960795265933257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 927980495895454042488685 347992685960795265933257)
                    ·
                      rfl

theorem cell22_1016570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_1016570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016570 prefixEnd_1016570 := by exact prefixLift 1016570
  have htrace : WordTrace (prefixWord ++ tailWord_1016570) baseStart_1016570 baseEnd_1016570 := by
    simpa [prefixWord, tailWord_1016570, baseEnd_1016570] using wordTrace_append hprefix tailTrace_1016570
  have hstable : (prefixWord ++ tailWord_1016570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016570).length < 2 ^ (prefixWord ++ tailWord_1016570).sum := by decide
  have hdescent : baseEnd_1016570 < baseStart_1016570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016585 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_1016585 : Nat := 118140960795 + 1016585 * 2 ^ 59
def prefixEnd_1016585 : Nat := 4983230072969 + 3 ^ 40 * 1016585 * 2
def baseEnd_1016585 : Nat := 347997820767340226808211

theorem tailTrace_1016585 : CollatzResearch.WordTrace tailWord_1016585 prefixEnd_1016585 347997820767340226808211 := by
  unfold tailWord_1016585
  simp only [CollatzResearch.WordTrace]
  refine ⟨37077901022093638740603209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24718600681395759160402139 37077901022093638740603209)
  ·
    refine ⟨27808425766570229055452407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37077901022093638740603209 27808425766570229055452407)
    ·
      refine ⟨41712638649855343583178611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27808425766570229055452407 41712638649855343583178611)
      ·
        refine ⟨62568957974783015374767917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41712638649855343583178611 62568957974783015374767917)
        ·
          refine ⟨23463359240543630765537969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62568957974783015374767917 23463359240543630765537969)
          ·
            refine ⟨17597519430407723074153477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23463359240543630765537969 17597519430407723074153477)
            ·
              refine ⟨3299534893201448076403777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17597519430407723074153477 3299534893201448076403777)
              ·
                refine ⟨2474651169901086057302833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3299534893201448076403777 2474651169901086057302833)
                ·
                  refine ⟨1855988377425814542977125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2474651169901086057302833 1855988377425814542977125)
                  ·
                    refine ⟨347997820767340226808211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1855988377425814542977125 347997820767340226808211)
                    ·
                      rfl

theorem cell22_1016585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_1016585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016585 prefixEnd_1016585 := by exact prefixLift 1016585
  have htrace : WordTrace (prefixWord ++ tailWord_1016585) baseStart_1016585 baseEnd_1016585 := by
    simpa [prefixWord, tailWord_1016585, baseEnd_1016585] using wordTrace_append hprefix tailTrace_1016585
  have hstable : (prefixWord ++ tailWord_1016585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016585).length < 2 ^ (prefixWord ++ tailWord_1016585).sum := by decide
  have hdescent : baseEnd_1016585 < baseStart_1016585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016638 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_1016638 : Nat := 118140960795 + 1016638 * 2 ^ 59
def prefixEnd_1016638 : Nat := 4983230072969 + 3 ^ 40 * 1016638 * 2
def baseEnd_1016638 : Nat := 348015963750465755233049

theorem tailTrace_1016638 : CollatzResearch.WordTrace tailWord_1016638 prefixEnd_1016638 348015963750465755233049 := by
  unfold tailWord_1016638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4634979261362703599035321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24719889393934419194855045 4634979261362703599035321)
  ·
    refine ⟨3476234446022027699276491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4634979261362703599035321 3476234446022027699276491)
    ·
      refine ⟨5214351669033041548914737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476234446022027699276491 5214351669033041548914737)
      ·
        refine ⟨3910763751774781161686053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5214351669033041548914737 3910763751774781161686053)
        ·
          refine ⟨733268203457771467816135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3910763751774781161686053 733268203457771467816135)
          ·
            refine ⟨1099902305186657201724203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733268203457771467816135 1099902305186657201724203)
            ·
              refine ⟨1649853457779985802586305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099902305186657201724203 1649853457779985802586305)
              ·
                refine ⟨1237390093334989351939729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649853457779985802586305 1237390093334989351939729)
                ·
                  refine ⟨928042570001242013954797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237390093334989351939729 928042570001242013954797)
                  ·
                    refine ⟨348015963750465755233049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928042570001242013954797 348015963750465755233049)
                    ·
                      rfl

theorem cell22_1016638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_1016638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016638 prefixEnd_1016638 := by exact prefixLift 1016638
  have htrace : WordTrace (prefixWord ++ tailWord_1016638) baseStart_1016638 baseEnd_1016638 := by
    simpa [prefixWord, tailWord_1016638, baseEnd_1016638] using wordTrace_append hprefix tailTrace_1016638
  have hstable : (prefixWord ++ tailWord_1016638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016638).length < 2 ^ (prefixWord ++ tailWord_1016638).sum := by decide
  have hdescent : baseEnd_1016638 < baseStart_1016638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016645 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 5]
def baseStart_1016645 : Nat := 118140960795 + 1016645 * 2 ^ 59
def prefixEnd_1016645 : Nat := 4983230072969 + 3 ^ 40 * 1016645 * 2
def baseEnd_1016645 : Nat := 116006119997840023436009

theorem tailTrace_1016645 : CollatzResearch.WordTrace tailWord_1016645 prefixEnd_1016645 116006119997840023436009 := by
  unfold tailWord_1016645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37080089401876268987787389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24720059601250845991858259 37080089401876268987787389)
  ·
    refine ⟨13905033525703600870420271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37080089401876268987787389 13905033525703600870420271)
    ·
      refine ⟨20857550288555401305630407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13905033525703600870420271 20857550288555401305630407)
      ·
        refine ⟨31286325432833101958445611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20857550288555401305630407 31286325432833101958445611)
        ·
          refine ⟨46929488149249652937668417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31286325432833101958445611 46929488149249652937668417)
          ·
            refine ⟨35197116111937239703251313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46929488149249652937668417 35197116111937239703251313)
            ·
              refine ⟨26397837083952929777438485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35197116111937239703251313 26397837083952929777438485)
              ·
                refine ⟨1237398613310293583317429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26397837083952929777438485 1237398613310293583317429)
                ·
                  refine ⟨116006119997840023436009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1237398613310293583317429 116006119997840023436009)
                  ·
                    rfl

theorem cell22_1016645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_1016645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016645 prefixEnd_1016645 := by exact prefixLift 1016645
  have htrace : WordTrace (prefixWord ++ tailWord_1016645) baseStart_1016645 baseEnd_1016645 := by
    simpa [prefixWord, tailWord_1016645, baseEnd_1016645] using wordTrace_append hprefix tailTrace_1016645
  have hstable : (prefixWord ++ tailWord_1016645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016645).length < 2 ^ (prefixWord ++ tailWord_1016645).sum := by decide
  have hdescent : baseEnd_1016645 < baseStart_1016645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016649 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 1, 3]
def baseStart_1016649 : Nat := 118140960795 + 1016649 * 2 ^ 59
def prefixEnd_1016649 : Nat := 4983230072969 + 3 ^ 40 * 1016649 * 2
def baseEnd_1016649 : Nat := 348019729275265393208015

theorem tailTrace_1016649 : CollatzResearch.WordTrace tailWord_1016649 prefixEnd_1016649 348019729275265393208015 := by
  unfold tailWord_1016649
  simp only [CollatzResearch.WordTrace]
  refine ⟨37080235293861777670933001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24720156862574518447288667 37080235293861777670933001)
  ·
    refine ⟨27810176470396333253199751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37080235293861777670933001 27810176470396333253199751)
    ·
      refine ⟨41715264705594499879799627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27810176470396333253199751 41715264705594499879799627)
      ·
        refine ⟨62572897058391749819699441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41715264705594499879799627 62572897058391749819699441)
        ·
          refine ⟨46929672793793812364774581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62572897058391749819699441 46929672793793812364774581)
          ·
            refine ⟨4399656824418169909197617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46929672793793812364774581 4399656824418169909197617)
            ·
              refine ⟨3299742618313627431898213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4399656824418169909197617 3299742618313627431898213)
              ·
                refine ⟨618701740933805143480915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3299742618313627431898213 618701740933805143480915)
                ·
                  refine ⟨928052611400707715221373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618701740933805143480915 928052611400707715221373)
                  ·
                    refine ⟨348019729275265393208015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928052611400707715221373 348019729275265393208015)
                    ·
                      rfl

theorem cell22_1016649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_1016649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016649 prefixEnd_1016649 := by exact prefixLift 1016649
  have htrace : WordTrace (prefixWord ++ tailWord_1016649) baseStart_1016649 baseEnd_1016649 := by
    simpa [prefixWord, tailWord_1016649, baseEnd_1016649] using wordTrace_append hprefix tailTrace_1016649
  have hstable : (prefixWord ++ tailWord_1016649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016649).length < 2 ^ (prefixWord ++ tailWord_1016649).sum := by decide
  have hdescent : baseEnd_1016649 < baseStart_1016649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016690 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1016690 : Nat := 118140960795 + 1016690 * 2 ^ 59
def prefixEnd_1016690 : Nat := 4983230072969 + 3 ^ 40 * 1016690 * 2
def baseEnd_1016690 : Nat := 116011254804384984310963

theorem tailTrace_1016690 : CollatzResearch.WordTrace tailWord_1016690 prefixEnd_1016690 116011254804384984310963 := by
  unfold tailWord_1016690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270432671678310418293881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24721153791142161115450349 9270432671678310418293881)
  ·
    refine ⟨6952824503758732813720411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9270432671678310418293881 6952824503758732813720411)
    ·
      refine ⟨10429236755638099220580617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6952824503758732813720411 10429236755638099220580617)
      ·
        refine ⟨7821927566728574415435463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10429236755638099220580617 7821927566728574415435463)
        ·
          refine ⟨11732891350092861623153195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7821927566728574415435463 11732891350092861623153195)
          ·
            refine ⟨17599337025139292434729793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11732891350092861623153195 17599337025139292434729793)
            ·
              refine ⟨13199502768854469326047345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17599337025139292434729793 13199502768854469326047345)
              ·
                refine ⟨9899627076640851994535509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13199502768854469326047345 9899627076640851994535509)
                ·
                  refine ⟨116011254804384984310963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9899627076640851994535509 116011254804384984310963)
                  ·
                    rfl

theorem cell22_1016690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1016690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016690 prefixEnd_1016690 := by exact prefixLift 1016690
  have htrace : WordTrace (prefixWord ++ tailWord_1016690) baseStart_1016690 baseEnd_1016690 := by
    simpa [prefixWord, tailWord_1016690, baseEnd_1016690] using wordTrace_append hprefix tailTrace_1016690
  have hstable : (prefixWord ++ tailWord_1016690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016690).length < 2 ^ (prefixWord ++ tailWord_1016690).sum := by decide
  have hdescent : baseEnd_1016690 < baseStart_1016690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016814 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_1016814 : Nat := 118140960795 + 1016814 * 2 ^ 59
def prefixEnd_1016814 : Nat := 4983230072969 + 3 ^ 40 * 1016814 * 2
def baseEnd_1016814 : Nat := 116025404049086654277503

theorem tailTrace_1016814 : CollatzResearch.WordTrace tailWord_1016814 prefixEnd_1016814 116025404049086654277503 := by
  unfold tailWord_1016814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635781667283001356336187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24724168892176007233792997 4635781667283001356336187)
  ·
    refine ⟨6953672500924502034504281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4635781667283001356336187 6953672500924502034504281)
    ·
      refine ⟨5215254375693376525878211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6953672500924502034504281 5215254375693376525878211)
      ·
        refine ⟨7822881563540064788817317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215254375693376525878211 7822881563540064788817317)
        ·
          refine ⟨1466790293163762147903247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7822881563540064788817317 1466790293163762147903247)
          ·
            refine ⟨2200185439745643221854871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466790293163762147903247 2200185439745643221854871)
            ·
              refine ⟨3300278159618464832782307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200185439745643221854871 3300278159618464832782307)
              ·
                refine ⟨4950417239427697249173461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300278159618464832782307 4950417239427697249173461)
                ·
                  refine ⟨116025404049086654277503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4950417239427697249173461 116025404049086654277503)
                  ·
                    rfl

theorem cell22_1016814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_1016814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016814 prefixEnd_1016814 := by exact prefixLift 1016814
  have htrace : WordTrace (prefixWord ++ tailWord_1016814) baseStart_1016814 baseEnd_1016814 := by
    simpa [prefixWord, tailWord_1016814, baseEnd_1016814] using wordTrace_append hprefix tailTrace_1016814
  have hstable : (prefixWord ++ tailWord_1016814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016814).length < 2 ^ (prefixWord ++ tailWord_1016814).sum := by decide
  have hdescent : baseEnd_1016814 < baseStart_1016814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016818 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1016818 : Nat := 118140960795 + 1016818 * 2 ^ 59
def prefixEnd_1016818 : Nat := 4983230072969 + 3 ^ 40 * 1016818 * 2
def baseEnd_1016818 : Nat := 348077581429005285732497

theorem tailTrace_1016818 : CollatzResearch.WordTrace tailWord_1016818 prefixEnd_1016818 348077581429005285732497 := by
  unfold tailWord_1016818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271599807562379883458777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24724266153499679689223405 9271599807562379883458777)
  ·
    refine ⟨6953699855671784912594083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9271599807562379883458777 6953699855671784912594083)
    ·
      refine ⟨10430549783507677368891125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6953699855671784912594083 10430549783507677368891125)
      ·
        refine ⟨977864042203844753333543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10430549783507677368891125 977864042203844753333543)
        ·
          refine ⟨1466796063305767130000315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977864042203844753333543 1466796063305767130000315)
          ·
            refine ⟨2200194094958650695000473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466796063305767130000315 2200194094958650695000473)
            ·
              refine ⟨1650145571218988021250355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200194094958650695000473 1650145571218988021250355)
              ·
                refine ⟨2475218356828482031875533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650145571218988021250355 2475218356828482031875533)
                ·
                  refine ⟨928206883810680761953325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2475218356828482031875533 928206883810680761953325)
                  ·
                    refine ⟨348077581429005285732497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928206883810680761953325 348077581429005285732497)
                    ·
                      rfl

theorem cell22_1016818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1016818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016818 prefixEnd_1016818 := by exact prefixLift 1016818
  have htrace : WordTrace (prefixWord ++ tailWord_1016818) baseStart_1016818 baseEnd_1016818 := by
    simpa [prefixWord, tailWord_1016818, baseEnd_1016818] using wordTrace_append hprefix tailTrace_1016818
  have hstable : (prefixWord ++ tailWord_1016818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016818).length < 2 ^ (prefixWord ++ tailWord_1016818).sum := by decide
  have hdescent : baseEnd_1016818 < baseStart_1016818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016844 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_1016844 : Nat := 118140960795 + 1016844 * 2 ^ 59
def prefixEnd_1016844 : Nat := 4983230072969 + 3 ^ 40 * 1016844 * 2
def baseEnd_1016844 : Nat := 348086481760349884582417

theorem tailTrace_1016844 : CollatzResearch.WordTrace tailWord_1016844 prefixEnd_1016844 348086481760349884582417 := by
  unfold tailWord_1016844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543673764077662987140793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24724898352103550649521057 18543673764077662987140793)
  ·
    refine ⟨13907755323058247240355595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18543673764077662987140793 13907755323058247240355595)
    ·
      refine ⟨20861632984587370860533393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13907755323058247240355595 20861632984587370860533393)
      ·
        refine ⟨15646224738440528145400045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20861632984587370860533393 15646224738440528145400045)
        ·
          refine ⟨5867334276915198054525017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15646224738440528145400045 5867334276915198054525017)
          ·
            refine ⟨4400500707686398540893763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5867334276915198054525017 4400500707686398540893763)
            ·
              refine ⟨6600751061529597811340645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4400500707686398540893763 6600751061529597811340645)
              ·
                refine ⟨1237640824036799589626371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6600751061529597811340645 1237640824036799589626371)
                ·
                  refine ⟨1856461236055199384439557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1237640824036799589626371 1856461236055199384439557)
                  ·
                    refine ⟨348086481760349884582417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1856461236055199384439557 348086481760349884582417)
                    ·
                      rfl

theorem cell22_1016844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_1016844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016844 prefixEnd_1016844 := by exact prefixLift 1016844
  have htrace : WordTrace (prefixWord ++ tailWord_1016844) baseStart_1016844 baseEnd_1016844 := by
    simpa [prefixWord, tailWord_1016844, baseEnd_1016844] using wordTrace_append hprefix tailTrace_1016844
  have hstable : (prefixWord ++ tailWord_1016844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016844).length < 2 ^ (prefixWord ++ tailWord_1016844).sum := by decide
  have hdescent : baseEnd_1016844 < baseStart_1016844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016857 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_1016857 : Nat := 118140960795 + 1016857 * 2 ^ 59
def prefixEnd_1016857 : Nat := 4983230072969 + 3 ^ 40 * 1016857 * 2
def baseEnd_1016857 : Nat := 348090931926022184007377

theorem tailTrace_1016857 : CollatzResearch.WordTrace tailWord_1016857 prefixEnd_1016857 348090931926022184007377 := by
  unfold tailWord_1016857
  simp only [CollatzResearch.WordTrace]
  refine ⟨37087821677108229194504825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24725214451405486129669883 37087821677108229194504825)
  ·
    refine ⟨27815866257831171895878619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37087821677108229194504825 27815866257831171895878619)
    ·
      refine ⟨41723799386746757843817929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27815866257831171895878619 41723799386746757843817929)
      ·
        refine ⟨31292849540060068382863447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41723799386746757843817929 31292849540060068382863447)
        ·
          refine ⟨46939274310090102574295171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31292849540060068382863447 46939274310090102574295171)
          ·
            refine ⟨70408911465135153861442757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46939274310090102574295171 70408911465135153861442757)
            ·
              refine ⟨13201670899712841349020517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70408911465135153861442757 13201670899712841349020517)
              ·
                refine ⟨2475313293696157752941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13201670899712841349020517 2475313293696157752941347)
                ·
                  refine ⟨3712969940544236629412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2475313293696157752941347 3712969940544236629412021)
                  ·
                    refine ⟨348090931926022184007377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3712969940544236629412021 348090931926022184007377)
                    ·
                      rfl

theorem cell22_1016857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_1016857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016857 prefixEnd_1016857 := by exact prefixLift 1016857
  have htrace : WordTrace (prefixWord ++ tailWord_1016857) baseStart_1016857 baseEnd_1016857 := by
    simpa [prefixWord, tailWord_1016857, baseEnd_1016857] using wordTrace_append hprefix tailTrace_1016857
  have hstable : (prefixWord ++ tailWord_1016857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016857).length < 2 ^ (prefixWord ++ tailWord_1016857).sum := by decide
  have hdescent : baseEnd_1016857 < baseStart_1016857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016876 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 4]
def baseStart_1016876 : Nat := 118140960795 + 1016876 * 2 ^ 59
def prefixEnd_1016876 : Nat := 4983230072969 + 3 ^ 40 * 1016876 * 2
def baseEnd_1016876 : Nat := 116032478671437489260773

theorem tailTrace_1016876 : CollatzResearch.WordTrace tailWord_1016876 prefixEnd_1016876 116032478671437489260773 := by
  unfold tailWord_1016876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18544257332019697719723241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24725676442692930292964321 18544257332019697719723241)
  ·
    refine ⟨13908192999014773289792431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18544257332019697719723241 13908192999014773289792431)
    ·
      refine ⟨20862289498522159934688647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13908192999014773289792431 20862289498522159934688647)
      ·
        refine ⟨31293434247783239902032971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20862289498522159934688647 31293434247783239902032971)
        ·
          refine ⟨46940151371674859853049457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31293434247783239902032971 46940151371674859853049457)
          ·
            refine ⟨35205113528756144889787093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46940151371674859853049457 35205113528756144889787093)
            ·
              refine ⟨825119848330222145854385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35205113528756144889787093 825119848330222145854385)
              ·
                refine ⟨618839886247666609390789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825119848330222145854385 618839886247666609390789)
                ·
                  refine ⟨116032478671437489260773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618839886247666609390789 116032478671437489260773)
                  ·
                    rfl

theorem cell22_1016876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_1016876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016876 prefixEnd_1016876 := by exact prefixLift 1016876
  have htrace : WordTrace (prefixWord ++ tailWord_1016876) baseStart_1016876 baseEnd_1016876 := by
    simpa [prefixWord, tailWord_1016876, baseEnd_1016876] using wordTrace_append hprefix tailTrace_1016876
  have hstable : (prefixWord ++ tailWord_1016876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016876).length < 2 ^ (prefixWord ++ tailWord_1016876).sum := by decide
  have hdescent : baseEnd_1016876 < baseStart_1016876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1016925 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1016925 : Nat := 118140960795 + 1016925 * 2 ^ 59
def prefixEnd_1016925 : Nat := 4983230072969 + 3 ^ 40 * 1016925 * 2
def baseEnd_1016925 : Nat := 348114209715692673307169

theorem tailTrace_1016925 : CollatzResearch.WordTrace tailWord_1016925 prefixEnd_1016925 348114209715692673307169 := by
  unfold tailWord_1016925
  simp only [CollatzResearch.WordTrace]
  refine ⟨37090301840861876807980229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24726867893907917871986819 37090301840861876807980229)
  ·
    refine ⟨6954431595161601901496293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37090301840861876807980229 6954431595161601901496293)
    ·
      refine ⟨1303955924092800356530555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6954431595161601901496293 1303955924092800356530555)
      ·
        refine ⟨1955933886139200534795833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303955924092800356530555 1955933886139200534795833)
        ·
          refine ⟨1466950414604400401096875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1955933886139200534795833 1466950414604400401096875)
          ·
            refine ⟨2200425621906600601645313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466950414604400401096875 2200425621906600601645313)
            ·
              refine ⟨1650319216429950451233985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200425621906600601645313 1650319216429950451233985)
              ·
                refine ⟨1237739412322462838425489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650319216429950451233985 1237739412322462838425489)
                ·
                  refine ⟨928304559241847128819117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1237739412322462838425489 928304559241847128819117)
                  ·
                    refine ⟨348114209715692673307169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928304559241847128819117 348114209715692673307169)
                    ·
                      rfl

theorem cell22_1016925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1016925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1016925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1016925 prefixEnd_1016925 := by exact prefixLift 1016925
  have htrace : WordTrace (prefixWord ++ tailWord_1016925) baseStart_1016925 baseEnd_1016925 := by
    simpa [prefixWord, tailWord_1016925, baseEnd_1016925] using wordTrace_append hprefix tailTrace_1016925
  have hstable : (prefixWord ++ tailWord_1016925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1016925).length < 2 ^ (prefixWord ++ tailWord_1016925).sum := by decide
  have hdescent : baseEnd_1016925 < baseStart_1016925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1016925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017045 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 4]
def baseStart_1017045 : Nat := 118140960795 + 1017045 * 2 ^ 59
def prefixEnd_1017045 : Nat := 4983230072969 + 3 ^ 40 * 1017045 * 2
def baseEnd_1017045 : Nat := 116051762722684120102267

theorem tailTrace_1017045 : CollatzResearch.WordTrace tailWord_1017045 prefixEnd_1017045 116051762722684120102267 := by
  unfold tailWord_1017045
  simp only [CollatzResearch.WordTrace]
  refine ⟨37094678600427137302348589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24729785733618091534899059 37094678600427137302348589)
  ·
    refine ⟨13910504475160176488380721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37094678600427137302348589 13910504475160176488380721)
    ·
      refine ⟨10432878356370132366285541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13910504475160176488380721 10432878356370132366285541)
      ·
        refine ⟨1956164691819399818678539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10432878356370132366285541 1956164691819399818678539)
        ·
          refine ⟨2934247037729099728017809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956164691819399818678539 2934247037729099728017809)
          ·
            refine ⟨2200685278296824796013357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2934247037729099728017809 2200685278296824796013357)
            ·
              refine ⟨825256979361309298505009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2200685278296824796013357 825256979361309298505009)
              ·
                refine ⟨618942734520981973878757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825256979361309298505009 618942734520981973878757)
                ·
                  refine ⟨116051762722684120102267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 618942734520981973878757 116051762722684120102267)
                  ·
                    rfl

theorem cell22_1017045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_1017045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017045 prefixEnd_1017045 := by exact prefixLift 1017045
  have htrace : WordTrace (prefixWord ++ tailWord_1017045) baseStart_1017045 baseEnd_1017045 := by
    simpa [prefixWord, tailWord_1017045, baseEnd_1017045] using wordTrace_append hprefix tailTrace_1017045
  have hstable : (prefixWord ++ tailWord_1017045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017045).length < 2 ^ (prefixWord ++ tailWord_1017045).sum := by decide
  have hdescent : baseEnd_1017045 < baseStart_1017045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017088 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 1, 3]
def baseStart_1017088 : Nat := 118140960795 + 1017088 * 2 ^ 59
def prefixEnd_1017088 : Nat := 4983230072969 + 3 ^ 40 * 1017088 * 2
def baseEnd_1017088 : Nat := 348170007946814581481669

theorem tailTrace_1017088 : CollatzResearch.WordTrace tailWord_1017088 prefixEnd_1017088 348170007946814581481669 := by
  unfold tailWord_1017088
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548123469635677823081959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24730831292847570430775945 18548123469635677823081959)
  ·
    refine ⟨27822185204453516734622939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18548123469635677823081959 27822185204453516734622939)
    ·
      refine ⟨41733277806680275101934409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27822185204453516734622939 41733277806680275101934409)
      ·
        refine ⟨31299958355010206326450807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41733277806680275101934409 31299958355010206326450807)
        ·
          refine ⟨46949937532515309489676211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31299958355010206326450807 46949937532515309489676211)
          ·
            refine ⟨70424906298772964234514317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46949937532515309489676211 70424906298772964234514317)
            ·
              refine ⟨26409339862039861587942869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70424906298772964234514317 26409339862039861587942869)
              ·
                refine ⟨618968903016559255967411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26409339862039861587942869 618968903016559255967411)
                ·
                  refine ⟨928453354524838883951117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618968903016559255967411 928453354524838883951117)
                  ·
                    refine ⟨348170007946814581481669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928453354524838883951117 348170007946814581481669)
                    ·
                      rfl

theorem cell22_1017088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 1, 3].length) (baseStart_1017088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017088 prefixEnd_1017088 := by exact prefixLift 1017088
  have htrace : WordTrace (prefixWord ++ tailWord_1017088) baseStart_1017088 baseEnd_1017088 := by
    simpa [prefixWord, tailWord_1017088, baseEnd_1017088] using wordTrace_append hprefix tailTrace_1017088
  have hstable : (prefixWord ++ tailWord_1017088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017088).length < 2 ^ (prefixWord ++ tailWord_1017088).sum := by decide
  have hdescent : baseEnd_1017088 < baseStart_1017088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017148 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_1017148 : Nat := 118140960795 + 1017148 * 2 ^ 59
def prefixEnd_1017148 : Nat := 4983230072969 + 3 ^ 40 * 1017148 * 2
def baseEnd_1017148 : Nat := 348190547172994424981485

theorem tailTrace_1017148 : CollatzResearch.WordTrace tailWord_1017148 prefixEnd_1017148 348190547172994424981485 := by
  unfold tailWord_1017148
  simp only [CollatzResearch.WordTrace]
  refine ⟨18549217659526992946674049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24732290212702657262232065 18549217659526992946674049)
  ·
    refine ⟨13911913244645244710005537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18549217659526992946674049 13911913244645244710005537)
    ·
      refine ⟨10433934933483933532504153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13911913244645244710005537 10433934933483933532504153)
      ·
        refine ⟨7825451200112950149378115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10433934933483933532504153 7825451200112950149378115)
        ·
          refine ⟨11738176800169425224067173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7825451200112950149378115 11738176800169425224067173)
          ·
            refine ⟨2200908150031767229512595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11738176800169425224067173 2200908150031767229512595)
            ·
              refine ⟨3301362225047650844268893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200908150031767229512595 3301362225047650844268893)
              ·
                refine ⟨1238010834392869066600835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3301362225047650844268893 1238010834392869066600835)
                ·
                  refine ⟨1857016251589303599901253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238010834392869066600835 1857016251589303599901253)
                  ·
                    refine ⟨348190547172994424981485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857016251589303599901253 348190547172994424981485)
                    ·
                      rfl

theorem cell22_1017148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_1017148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017148 prefixEnd_1017148 := by exact prefixLift 1017148
  have htrace : WordTrace (prefixWord ++ tailWord_1017148) baseStart_1017148 baseEnd_1017148 := by
    simpa [prefixWord, tailWord_1017148, baseEnd_1017148] using wordTrace_append hprefix tailTrace_1017148
  have hstable : (prefixWord ++ tailWord_1017148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017148).length < 2 ^ (prefixWord ++ tailWord_1017148).sum := by decide
  have hdescent : baseEnd_1017148 < baseStart_1017148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017178 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_1017178 : Nat := 118140960795 + 1017178 * 2 ^ 59
def prefixEnd_1017178 : Nat := 4983230072969 + 3 ^ 40 * 1017178 * 2
def baseEnd_1017178 : Nat := 348200816786084346731393

theorem tailTrace_1017178 : CollatzResearch.WordTrace tailWord_1017178 prefixEnd_1017178 348200816786084346731393 := by
  unfold tailWord_1017178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9274882377236325254235047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24733019672630200677960125 9274882377236325254235047)
  ·
    refine ⟨13912323565854487881352571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9274882377236325254235047 13912323565854487881352571)
    ·
      refine ⟨20868485348781731822028857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13912323565854487881352571 20868485348781731822028857)
      ·
        refine ⟨15651364011586298866521643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20868485348781731822028857 15651364011586298866521643)
        ·
          refine ⟨23477046017379448299782465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15651364011586298866521643 23477046017379448299782465)
          ·
            refine ⟨17607784513034586224836849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23477046017379448299782465 17607784513034586224836849)
            ·
              refine ⟨13205838384775939668627637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17607784513034586224836849 13205838384775939668627637)
              ·
                refine ⟨1238047348572744343933841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13205838384775939668627637 1238047348572744343933841)
                ·
                  refine ⟨928535511429558257950381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238047348572744343933841 928535511429558257950381)
                  ·
                    refine ⟨348200816786084346731393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928535511429558257950381 348200816786084346731393)
                    ·
                      rfl

theorem cell22_1017178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_1017178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017178 prefixEnd_1017178 := by exact prefixLift 1017178
  have htrace : WordTrace (prefixWord ++ tailWord_1017178) baseStart_1017178 baseEnd_1017178 := by
    simpa [prefixWord, tailWord_1017178, baseEnd_1017178] using wordTrace_append hprefix tailTrace_1017178
  have hstable : (prefixWord ++ tailWord_1017178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017178).length < 2 ^ (prefixWord ++ tailWord_1017178).sum := by decide
  have hdescent : baseEnd_1017178 < baseStart_1017178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017214 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1017214 : Nat := 118140960795 + 1017214 * 2 ^ 59
def prefixEnd_1017214 : Nat := 4983230072969 + 3 ^ 40 * 1017214 * 2
def baseEnd_1017214 : Nat := 116071046773930750943761

theorem tailTrace_1017214 : CollatzResearch.WordTrace tailWord_1017214 prefixEnd_1017214 116071046773930750943761 := by
  unfold tailWord_1017214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637605317101859895656337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24733895024543252776833797 4637605317101859895656337)
  ·
    refine ⟨3478203987826394921742253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4637605317101859895656337 3478203987826394921742253)
    ·
      refine ⟨1304326495434898095653345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3478203987826394921742253 1304326495434898095653345)
      ·
        refine ⟨978244871576173571740009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1304326495434898095653345 978244871576173571740009)
        ·
          refine ⟨733683653682130178805007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978244871576173571740009 733683653682130178805007)
          ·
            refine ⟨1100525480523195268207511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733683653682130178805007 1100525480523195268207511)
            ·
              refine ⟨1650788220784792902311267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100525480523195268207511 1650788220784792902311267)
              ·
                refine ⟨2476182331177189353466901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650788220784792902311267 2476182331177189353466901)
                ·
                  refine ⟨116071046773930750943761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2476182331177189353466901 116071046773930750943761)
                  ·
                    rfl

theorem cell22_1017214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1017214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017214 prefixEnd_1017214 := by exact prefixLift 1017214
  have htrace : WordTrace (prefixWord ++ tailWord_1017214) baseStart_1017214 baseEnd_1017214 := by
    simpa [prefixWord, tailWord_1017214, baseEnd_1017214] using wordTrace_append hprefix tailTrace_1017214
  have hstable : (prefixWord ++ tailWord_1017214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017214).length < 2 ^ (prefixWord ++ tailWord_1017214).sum := by decide
  have hdescent : baseEnd_1017214 < baseStart_1017214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017296 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_1017296 : Nat := 118140960795 + 1017296 * 2 ^ 59
def prefixEnd_1017296 : Nat := 4983230072969 + 3 ^ 40 * 1017296 * 2
def baseEnd_1017296 : Nat := 348241210597571372281031

theorem tailTrace_1017296 : CollatzResearch.WordTrace tailWord_1017296 prefixEnd_1017296 348241210597571372281031 := by
  unfold tailWord_1017296
  simp only [CollatzResearch.WordTrace]
  refine ⟨18551916661258903584867871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24735888881678538113157161 18551916661258903584867871)
  ·
    refine ⟨27827874991888355377301807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18551916661258903584867871 27827874991888355377301807)
    ·
      refine ⟨41741812487832533065952711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27827874991888355377301807 41741812487832533065952711)
      ·
        refine ⟨62612718731748799598929067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41741812487832533065952711 62612718731748799598929067)
        ·
          refine ⟨93919078097623199398393601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62612718731748799598929067 93919078097623199398393601)
          ·
            refine ⟨70439308573217399548795201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93919078097623199398393601 70439308573217399548795201)
            ·
              refine ⟨52829481429913049661596401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70439308573217399548795201 52829481429913049661596401)
              ·
                refine ⟨39622111072434787246197301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52829481429913049661596401 39622111072434787246197301)
                ·
                  refine ⟨3714572913040761304330997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39622111072434787246197301 3714572913040761304330997)
                  ·
                    refine ⟨348241210597571372281031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3714572913040761304330997 348241210597571372281031)
                    ·
                      rfl

theorem cell22_1017296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_1017296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017296 prefixEnd_1017296 := by exact prefixLift 1017296
  have htrace : WordTrace (prefixWord ++ tailWord_1017296) baseStart_1017296 baseEnd_1017296 := by
    simpa [prefixWord, tailWord_1017296, baseEnd_1017296] using wordTrace_append hprefix tailTrace_1017296
  have hstable : (prefixWord ++ tailWord_1017296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017296).length < 2 ^ (prefixWord ++ tailWord_1017296).sum := by decide
  have hdescent : baseEnd_1017296 < baseStart_1017296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017313 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_1017313 : Nat := 118140960795 + 1017313 * 2 ^ 59
def prefixEnd_1017313 : Nat := 4983230072969 + 3 ^ 40 * 1017313 * 2
def baseEnd_1017313 : Nat := 348247030044988994605979

theorem tailTrace_1017313 : CollatzResearch.WordTrace tailWord_1017313 prefixEnd_1017313 348247030044988994605979 := by
  unfold tailWord_1017313
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104453363456219073104593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736302242304146048736395 37104453363456219073104593)
  ·
    refine ⟨27828340022592164304828445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37104453363456219073104593 27828340022592164304828445)
    ·
      refine ⟨10435627508472061614310667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27828340022592164304828445 10435627508472061614310667)
      ·
        refine ⟨15653441262708092421466001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10435627508472061614310667 15653441262708092421466001)
        ·
          refine ⟨11740080947031069316099501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15653441262708092421466001 11740080947031069316099501)
          ·
            refine ⟨4402530355136650993537313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11740080947031069316099501 4402530355136650993537313)
            ·
              refine ⟨3301897766352488245152985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4402530355136650993537313 3301897766352488245152985)
              ·
                refine ⟨2476423324764366183864739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3301897766352488245152985 2476423324764366183864739)
                ·
                  refine ⟨3714634987146549275797109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476423324764366183864739 3714634987146549275797109)
                  ·
                    refine ⟨348247030044988994605979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3714634987146549275797109 348247030044988994605979)
                    ·
                      rfl

theorem cell22_1017313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_1017313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017313 prefixEnd_1017313 := by exact prefixLift 1017313
  have htrace : WordTrace (prefixWord ++ tailWord_1017313) baseStart_1017313 baseEnd_1017313 := by
    simpa [prefixWord, tailWord_1017313, baseEnd_1017313] using wordTrace_append hprefix tailTrace_1017313
  have hstable : (prefixWord ++ tailWord_1017313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017313).length < 2 ^ (prefixWord ++ tailWord_1017313).sum := by decide
  have hdescent : baseEnd_1017313 < baseStart_1017313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017315 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 4]
def baseStart_1017315 : Nat := 118140960795 + 1017315 * 2 ^ 59
def prefixEnd_1017315 : Nat := 4983230072969 + 3 ^ 40 * 1017315 * 2
def baseEnd_1017315 : Nat := 116082571561953885351991

theorem tailTrace_1017315 : CollatzResearch.WordTrace tailWord_1017315 prefixEnd_1017315 116082571561953885351991 := by
  unfold tailWord_1017315
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104526309448973414677399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736350872965982276451599 37104526309448973414677399)
  ·
    refine ⟨55656789464173460122016099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37104526309448973414677399 55656789464173460122016099)
    ·
      refine ⟨83485184196260190183024149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55656789464173460122016099 83485184196260190183024149)
      ·
        refine ⟨3913368009199696414829257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83485184196260190183024149 3913368009199696414829257)
        ·
          refine ⟨2935026006899772311121943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3913368009199696414829257 2935026006899772311121943)
          ·
            refine ⟨4402539010349658466682915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935026006899772311121943 4402539010349658466682915)
            ·
              refine ⟨6603808515524487700024373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4402539010349658466682915 6603808515524487700024373)
              ·
                refine ⟨619107048330420721877285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6603808515524487700024373 619107048330420721877285)
                ·
                  refine ⟨116082571561953885351991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619107048330420721877285 116082571561953885351991)
                  ·
                    rfl

theorem cell22_1017315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 4].length) (baseStart_1017315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017315 prefixEnd_1017315 := by exact prefixLift 1017315
  have htrace : WordTrace (prefixWord ++ tailWord_1017315) baseStart_1017315 baseEnd_1017315 := by
    simpa [prefixWord, tailWord_1017315, baseEnd_1017315] using wordTrace_append hprefix tailTrace_1017315
  have hstable : (prefixWord ++ tailWord_1017315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017315).length < 2 ^ (prefixWord ++ tailWord_1017315).sum := by decide
  have hdescent : baseEnd_1017315 < baseStart_1017315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017317 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_1017317 : Nat := 118140960795 + 1017317 * 2 ^ 59
def prefixEnd_1017317 : Nat := 4983230072969 + 3 ^ 40 * 1017317 * 2
def baseEnd_1017317 : Nat := 348248399326734317505967

theorem tailTrace_1017317 : CollatzResearch.WordTrace tailWord_1017317 prefixEnd_1017317 348248399326734317505967 := by
  unfold tailWord_1017317
  simp only [CollatzResearch.WordTrace]
  refine ⟨37104599255441727756250205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24736399503627818504166803 37104599255441727756250205)
  ·
    refine ⟨13914224720790647908593827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37104599255441727756250205 13914224720790647908593827)
    ·
      refine ⟨20871337081185971862890741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13914224720790647908593827 20871337081185971862890741)
      ·
        refine ⟨1956687851361184862146007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20871337081185971862890741 1956687851361184862146007)
        ·
          refine ⟨2935031777041777293219011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1956687851361184862146007 2935031777041777293219011)
          ·
            refine ⟨4402547665562665939828517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935031777041777293219011 4402547665562665939828517)
            ·
              refine ⟨825477687292999863717847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4402547665562665939828517 825477687292999863717847)
              ·
                refine ⟨1238216530939499795576771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825477687292999863717847 1238216530939499795576771)
                ·
                  refine ⟨1857324796409249693365157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238216530939499795576771 1857324796409249693365157)
                  ·
                    refine ⟨348248399326734317505967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857324796409249693365157 348248399326734317505967)
                    ·
                      rfl

theorem cell22_1017317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_1017317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017317 prefixEnd_1017317 := by exact prefixLift 1017317
  have htrace : WordTrace (prefixWord ++ tailWord_1017317) baseStart_1017317 baseEnd_1017317 := by
    simpa [prefixWord, tailWord_1017317, baseEnd_1017317] using wordTrace_append hprefix tailTrace_1017317
  have hstable : (prefixWord ++ tailWord_1017317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017317).length < 2 ^ (prefixWord ++ tailWord_1017317).sum := by decide
  have hdescent : baseEnd_1017317 < baseStart_1017317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017398 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1017398 : Nat := 118140960795 + 1017398 * 2 ^ 59
def prefixEnd_1017398 : Nat := 4983230072969 + 3 ^ 40 * 1017398 * 2
def baseEnd_1017398 : Nat := 348276127282077106230719

theorem tailTrace_1017398 : CollatzResearch.WordTrace tailWord_1017398 prefixEnd_1017398 348276127282077106230719 := by
  unfold tailWord_1017398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2319222098009267411871803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24738369045432185726632565 2319222098009267411871803)
  ·
    refine ⟨3478833147013901117807705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2319222098009267411871803 3478833147013901117807705)
    ·
      refine ⟨2609124860260425838355779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3478833147013901117807705 2609124860260425838355779)
      ·
        refine ⟨3913687290390638757533669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609124860260425838355779 3913687290390638757533669)
        ·
          refine ⟨733816366948244767037563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3913687290390638757533669 733816366948244767037563)
          ·
            refine ⟨1100724550422367150556345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733816366948244767037563 1100724550422367150556345)
            ·
              refine ⟨825543412816775362917259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100724550422367150556345 825543412816775362917259)
              ·
                refine ⟨1238315119225163044375889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825543412816775362917259 1238315119225163044375889)
                ·
                  refine ⟨928736339418872283281917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238315119225163044375889 928736339418872283281917)
                  ·
                    refine ⟨348276127282077106230719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928736339418872283281917 348276127282077106230719)
                    ·
                      rfl

theorem cell22_1017398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1017398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017398 prefixEnd_1017398 := by exact prefixLift 1017398
  have htrace : WordTrace (prefixWord ++ tailWord_1017398) baseStart_1017398 baseEnd_1017398 := by
    simpa [prefixWord, tailWord_1017398, baseEnd_1017398] using wordTrace_append hprefix tailTrace_1017398
  have hstable : (prefixWord ++ tailWord_1017398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017398).length < 2 ^ (prefixWord ++ tailWord_1017398).sum := by decide
  have hdescent : baseEnd_1017398 < baseStart_1017398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017463 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1017463 : Nat := 118140960795 + 1017463 * 2 ^ 59
def prefixEnd_1017463 : Nat := 4983230072969 + 3 ^ 40 * 1017463 * 2
def baseEnd_1017463 : Nat := 348298378110438603355519

theorem tailTrace_1017463 : CollatzResearch.WordTrace tailWord_1017463 prefixEnd_1017463 348298378110438603355519 := by
  unfold tailWord_1017463
  simp only [CollatzResearch.WordTrace]
  refine ⟨37109924312912794691065043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24739949541941863127376695 37109924312912794691065043)
  ·
    refine ⟨55664886469369192036597565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37109924312912794691065043 55664886469369192036597565)
    ·
      refine ⟨20874332426013447013724087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55664886469369192036597565 20874332426013447013724087)
      ·
        refine ⟨31311498639020170520586131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20874332426013447013724087 31311498639020170520586131)
        ·
          refine ⟨46967247958530255780879197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31311498639020170520586131 46967247958530255780879197)
          ·
            refine ⟨17612717984448845917829699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46967247958530255780879197 17612717984448845917829699)
            ·
              refine ⟨26419076976673268876744549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17612717984448845917829699 26419076976673268876744549)
              ·
                refine ⟨4953576933126237914389603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26419076976673268876744549 4953576933126237914389603)
                ·
                  refine ⟨7430365399689356871584405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4953576933126237914389603 7430365399689356871584405)
                  ·
                    refine ⟨348298378110438603355519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7430365399689356871584405 348298378110438603355519)
                    ·
                      rfl

theorem cell22_1017463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1017463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017463 prefixEnd_1017463 := by exact prefixLift 1017463
  have htrace : WordTrace (prefixWord ++ tailWord_1017463) baseStart_1017463 baseEnd_1017463 := by
    simpa [prefixWord, tailWord_1017463, baseEnd_1017463] using wordTrace_append hprefix tailTrace_1017463
  have hstable : (prefixWord ++ tailWord_1017463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017463).length < 2 ^ (prefixWord ++ tailWord_1017463).sum := by decide
  have hdescent : baseEnd_1017463 < baseStart_1017463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017465 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_1017465 : Nat := 118140960795 + 1017465 * 2 ^ 59
def prefixEnd_1017465 : Nat := 4983230072969 + 3 ^ 40 * 1017465 * 2
def baseEnd_1017465 : Nat := 348299062751311264805513

theorem tailTrace_1017465 : CollatzResearch.WordTrace tailWord_1017465 prefixEnd_1017465 348299062751311264805513 := by
  unfold tailWord_1017465
  simp only [CollatzResearch.WordTrace]
  refine ⟨37109997258905549032637849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24739998172603699355091899 37109997258905549032637849)
  ·
    refine ⟨27832497944179161774478387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37109997258905549032637849 27832497944179161774478387)
    ·
      refine ⟨41748746916268742661717581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27832497944179161774478387 41748746916268742661717581)
      ·
        refine ⟨15655780093600778498144093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41748746916268742661717581 15655780093600778498144093)
        ·
          refine ⟨5870917535100291936804035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15655780093600778498144093 5870917535100291936804035)
          ·
            refine ⟨8806376302650437905206053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5870917535100291936804035 8806376302650437905206053)
            ·
              refine ⟨1651195556746957107226135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8806376302650437905206053 1651195556746957107226135)
              ·
                refine ⟨2476793335120435660839203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651195556746957107226135 2476793335120435660839203)
                ·
                  refine ⟨3715190002680653491258805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2476793335120435660839203 3715190002680653491258805)
                  ·
                    refine ⟨348299062751311264805513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3715190002680653491258805 348299062751311264805513)
                    ·
                      rfl

theorem cell22_1017465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_1017465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017465 prefixEnd_1017465 := by exact prefixLift 1017465
  have htrace : WordTrace (prefixWord ++ tailWord_1017465) baseStart_1017465 baseEnd_1017465 := by
    simpa [prefixWord, tailWord_1017465, baseEnd_1017465] using wordTrace_append hprefix tailTrace_1017465
  have hstable : (prefixWord ++ tailWord_1017465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017465).length < 2 ^ (prefixWord ++ tailWord_1017465).sum := by decide
  have hdescent : baseEnd_1017465 < baseStart_1017465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017493 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1017493 : Nat := 118140960795 + 1017493 * 2 ^ 59
def prefixEnd_1017493 : Nat := 4983230072969 + 3 ^ 40 * 1017493 * 2
def baseEnd_1017493 : Nat := 348308647723528525105427

theorem tailTrace_1017493 : CollatzResearch.WordTrace tailWord_1017493 prefixEnd_1017493 348308647723528525105427 := by
  unfold tailWord_1017493
  simp only [CollatzResearch.WordTrace]
  refine ⟨37111018502804109814657133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24740679001869406543104755 37111018502804109814657133)
  ·
    refine ⟨13916631938551541180496425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37111018502804109814657133 13916631938551541180496425)
    ·
      refine ⟨10437473953913655885372319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13916631938551541180496425 10437473953913655885372319)
      ·
        refine ⟨15656210930870483828058479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10437473953913655885372319 15656210930870483828058479)
        ·
          refine ⟨23484316396305725742087719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656210930870483828058479 23484316396305725742087719)
          ·
            refine ⟨35226474594458588613131579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23484316396305725742087719 35226474594458588613131579)
            ·
              refine ⟨52839711891687882919697369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35226474594458588613131579 52839711891687882919697369)
              ·
                refine ⟨39629783918765912189773027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52839711891687882919697369 39629783918765912189773027)
                ·
                  refine ⟨59444675878148868284659541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39629783918765912189773027 59444675878148868284659541)
                  ·
                    refine ⟨348308647723528525105427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59444675878148868284659541 348308647723528525105427)
                    ·
                      rfl

theorem cell22_1017493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1017493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017493 prefixEnd_1017493 := by exact prefixLift 1017493
  have htrace : WordTrace (prefixWord ++ tailWord_1017493) baseStart_1017493 baseEnd_1017493 := by
    simpa [prefixWord, tailWord_1017493, baseEnd_1017493] using wordTrace_append hprefix tailTrace_1017493
  have hstable : (prefixWord ++ tailWord_1017493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017493).length < 2 ^ (prefixWord ++ tailWord_1017493).sum := by decide
  have hdescent : baseEnd_1017493 < baseStart_1017493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017527 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 3, 3]
def baseStart_1017527 : Nat := 118140960795 + 1017527 * 2 ^ 59
def prefixEnd_1017527 : Nat := 4983230072969 + 3 ^ 40 * 1017527 * 2
def baseEnd_1017527 : Nat := 348320286618363769755323

theorem tailTrace_1017527 : CollatzResearch.WordTrace tailWord_1017527 prefixEnd_1017527 348320286618363769755323 := by
  unfold tailWord_1017527
  simp only [CollatzResearch.WordTrace]
  refine ⟨37112258584680933621394835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24741505723120622414263223 37112258584680933621394835)
  ·
    refine ⟨55668387877021400432092253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37112258584680933621394835 55668387877021400432092253)
    ·
      refine ⟨20875645453883025162034595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55668387877021400432092253 20875645453883025162034595)
      ·
        refine ⟨31313468180824537743051893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20875645453883025162034595 31313468180824537743051893)
        ·
          refine ⟨2935637641952300413411115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31313468180824537743051893 2935637641952300413411115)
          ·
            refine ⟨4403456462928450620116673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935637641952300413411115 4403456462928450620116673)
            ·
              refine ⟨3302592347196337965087505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403456462928450620116673 3302592347196337965087505)
              ·
                refine ⟨2476944260397253473815629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3302592347196337965087505 2476944260397253473815629)
                ·
                  refine ⟨928854097648970052680861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2476944260397253473815629 928854097648970052680861)
                  ·
                    refine ⟨348320286618363769755323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928854097648970052680861 348320286618363769755323)
                    ·
                      rfl

theorem cell22_1017527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_1017527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017527 prefixEnd_1017527 := by exact prefixLift 1017527
  have htrace : WordTrace (prefixWord ++ tailWord_1017527) baseStart_1017527 baseEnd_1017527 := by
    simpa [prefixWord, tailWord_1017527, baseEnd_1017527] using wordTrace_append hprefix tailTrace_1017527
  have hstable : (prefixWord ++ tailWord_1017527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017527).length < 2 ^ (prefixWord ++ tailWord_1017527).sum := by decide
  have hdescent : baseEnd_1017527 < baseStart_1017527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017540 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1017540 : Nat := 118140960795 + 1017540 * 2 ^ 59
def prefixEnd_1017540 : Nat := 4983230072969 + 3 ^ 40 * 1017540 * 2
def baseEnd_1017540 : Nat := 116108245594678689726761

theorem tailTrace_1017540 : CollatzResearch.WordTrace tailWord_1017540 prefixEnd_1017540 116108245594678689726761 := by
  unfold tailWord_1017540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18556366366816918420809037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24741821822422557894412049 18556366366816918420809037)
  ·
    refine ⟨6958637387556344407803389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18556366366816918420809037 6958637387556344407803389)
    ·
      refine ⟨2609489020333629152926271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6958637387556344407803389 2609489020333629152926271)
      ·
        refine ⟨3914233530500443729389407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609489020333629152926271 3914233530500443729389407)
        ·
          refine ⟨5871350295750665594084111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914233530500443729389407 5871350295750665594084111)
          ·
            refine ⟨8807025443625998391126167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871350295750665594084111 8807025443625998391126167)
            ·
              refine ⟨13210538165438997586689251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807025443625998391126167 13210538165438997586689251)
              ·
                refine ⟨19815807248158496380033877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13210538165438997586689251 19815807248158496380033877)
                ·
                  refine ⟨116108245594678689726761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19815807248158496380033877 116108245594678689726761)
                  ·
                    rfl

theorem cell22_1017540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1017540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017540 prefixEnd_1017540 := by exact prefixLift 1017540
  have htrace : WordTrace (prefixWord ++ tailWord_1017540) baseStart_1017540 baseEnd_1017540 := by
    simpa [prefixWord, tailWord_1017540, baseEnd_1017540] using wordTrace_append hprefix tailTrace_1017540
  have hstable : (prefixWord ++ tailWord_1017540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017540).length < 2 ^ (prefixWord ++ tailWord_1017540).sum := by decide
  have hdescent : baseEnd_1017540 < baseStart_1017540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017561 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 1, 3]
def baseStart_1017561 : Nat := 118140960795 + 1017561 * 2 ^ 59
def prefixEnd_1017561 : Nat := 4983230072969 + 3 ^ 40 * 1017561 * 2
def baseEnd_1017561 : Nat := 348331925513199014405219

theorem tailTrace_1017561 : CollatzResearch.WordTrace tailWord_1017561 prefixEnd_1017561 348331925513199014405219 := by
  unfold tailWord_1017561
  simp only [CollatzResearch.WordTrace]
  refine ⟨37113498666557757428132537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24742332444371838285421691 37113498666557757428132537)
  ·
    refine ⟨27835123999918318071099403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37113498666557757428132537 27835123999918318071099403)
    ·
      refine ⟨41752685999877477106649105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27835123999918318071099403 41752685999877477106649105)
      ·
        refine ⟨31314514499908107829986829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41752685999877477106649105 31314514499908107829986829)
        ·
          refine ⟨11742942937465540436245061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31314514499908107829986829 11742942937465540436245061)
          ·
            refine ⟨2201801800774788831795949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11742942937465540436245061 2201801800774788831795949)
            ·
              refine ⟨825675675290545811923481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2201801800774788831795949 825675675290545811923481)
              ·
                refine ⟨619256756467909358942611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825675675290545811923481 619256756467909358942611)
                ·
                  refine ⟨928885134701864038413917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619256756467909358942611 928885134701864038413917)
                  ·
                    refine ⟨348331925513199014405219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928885134701864038413917 348331925513199014405219)
                    ·
                      rfl

theorem cell22_1017561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_1017561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017561 prefixEnd_1017561 := by exact prefixLift 1017561
  have htrace : WordTrace (prefixWord ++ tailWord_1017561) baseStart_1017561 baseEnd_1017561 := by
    simpa [prefixWord, tailWord_1017561, baseEnd_1017561] using wordTrace_append hprefix tailTrace_1017561
  have hstable : (prefixWord ++ tailWord_1017561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017561).length < 2 ^ (prefixWord ++ tailWord_1017561).sum := by decide
  have hdescent : baseEnd_1017561 < baseStart_1017561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017587 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 1, 4]
def baseStart_1017587 : Nat := 118140960795 + 1017587 * 2 ^ 59
def prefixEnd_1017587 : Nat := 4983230072969 + 3 ^ 40 * 1017587 * 2
def baseEnd_1017587 : Nat := 348340825844543613255139

theorem tailTrace_1017587 : CollatzResearch.WordTrace tailWord_1017587 prefixEnd_1017587 348340825844543613255139 := by
  unfold tailWord_1017587
  simp only [CollatzResearch.WordTrace]
  refine ⟨37114446964463563868579015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24742964642975709245719343 37114446964463563868579015)
  ·
    refine ⟨55671670446695345802868523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37114446964463563868579015 55671670446695345802868523)
    ·
      refine ⟨83507505670043018704302785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55671670446695345802868523 83507505670043018704302785)
      ·
        refine ⟨62630629252532264028227089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83507505670043018704302785 62630629252532264028227089)
        ·
          refine ⟨46972971939399198021170317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62630629252532264028227089 46972971939399198021170317)
          ·
            refine ⟨17614864477274699257938869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46972971939399198021170317 17614864477274699257938869)
            ·
              refine ⟨1651393544744503055431769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17614864477274699257938869 1651393544744503055431769)
              ·
                refine ⟨1238545158558377291573827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651393544744503055431769 1238545158558377291573827)
                ·
                  refine ⟨1857817737837565937360741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238545158558377291573827 1857817737837565937360741)
                  ·
                    refine ⟨348340825844543613255139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857817737837565937360741 348340825844543613255139)
                    ·
                      rfl

theorem cell22_1017587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 4].length) (baseStart_1017587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017587 prefixEnd_1017587 := by exact prefixLift 1017587
  have htrace : WordTrace (prefixWord ++ tailWord_1017587) baseStart_1017587 baseEnd_1017587 := by
    simpa [prefixWord, tailWord_1017587, baseEnd_1017587] using wordTrace_append hprefix tailTrace_1017587
  have hstable : (prefixWord ++ tailWord_1017587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017587).length < 2 ^ (prefixWord ++ tailWord_1017587).sum := by decide
  have hdescent : baseEnd_1017587 < baseStart_1017587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017600 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_1017600 : Nat := 118140960795 + 1017600 * 2 ^ 59
def prefixEnd_1017600 : Nat := 4983230072969 + 3 ^ 40 * 1017600 * 2
def baseEnd_1017600 : Nat := 348345276010215912680099

theorem tailTrace_1017600 : CollatzResearch.WordTrace tailWord_1017600 prefixEnd_1017600 348345276010215912680099 := by
  unfold tailWord_1017600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557460556708233544401127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24743280742277644725868169 18557460556708233544401127)
  ·
    refine ⟨27836190835062350316601691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18557460556708233544401127 27836190835062350316601691)
    ·
      refine ⟨41754286252593525474902537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27836190835062350316601691 41754286252593525474902537)
      ·
        refine ⟨31315714689445144106176903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41754286252593525474902537 31315714689445144106176903)
        ·
          refine ⟨46973572034167716159265355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31315714689445144106176903 46973572034167716159265355)
          ·
            refine ⟨70460358051251574238898033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46973572034167716159265355 70460358051251574238898033)
            ·
              refine ⟨52845268538438680679173525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70460358051251574238898033 52845268538438680679173525)
              ·
                refine ⟨2477121962739313156836259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52845268538438680679173525 2477121962739313156836259)
                ·
                  refine ⟨3715682944108969735254389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477121962739313156836259 3715682944108969735254389)
                  ·
                    refine ⟨348345276010215912680099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3715682944108969735254389 348345276010215912680099)
                    ·
                      rfl

theorem cell22_1017600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_1017600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017600 prefixEnd_1017600 := by exact prefixLift 1017600
  have htrace : WordTrace (prefixWord ++ tailWord_1017600) baseStart_1017600 baseEnd_1017600 := by
    simpa [prefixWord, tailWord_1017600, baseEnd_1017600] using wordTrace_append hprefix tailTrace_1017600
  have hstable : (prefixWord ++ tailWord_1017600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017600).length < 2 ^ (prefixWord ++ tailWord_1017600).sum := by decide
  have hdescent : baseEnd_1017600 < baseStart_1017600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017615 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 4, 4]
def baseStart_1017615 : Nat := 118140960795 + 1017615 * 2 ^ 59
def prefixEnd_1017615 : Nat := 4983230072969 + 3 ^ 40 * 1017615 * 2
def baseEnd_1017615 : Nat := 348350410816760873555053

theorem tailTrace_1017615 : CollatzResearch.WordTrace tailWord_1017615 prefixEnd_1017615 348350410816760873555053 := by
  unfold tailWord_1017615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37115468208362124650598299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24743645472241416433732199 37115468208362124650598299)
  ·
    refine ⟨55673202312543186975897449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37115468208362124650598299 55673202312543186975897449)
    ·
      refine ⟨41754901734407390231923087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55673202312543186975897449 41754901734407390231923087)
      ·
        refine ⟨62632352601611085347884631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41754901734407390231923087 62632352601611085347884631)
        ·
          refine ⟨93948528902416628021826947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62632352601611085347884631 93948528902416628021826947)
          ·
            refine ⟨140922793353624942032740421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93948528902416628021826947 140922793353624942032740421)
            ·
              refine ⟨26423023753804676631138829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140922793353624942032740421 26423023753804676631138829)
              ·
                refine ⟨9908633907676753736677061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26423023753804676631138829 9908633907676753736677061)
                ·
                  refine ⟨1857868857689391325626949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9908633907676753736677061 1857868857689391325626949)
                  ·
                    refine ⟨348350410816760873555053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857868857689391325626949 348350410816760873555053)
                    ·
                      rfl

theorem cell22_1017615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_1017615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017615 prefixEnd_1017615 := by exact prefixLift 1017615
  have htrace : WordTrace (prefixWord ++ tailWord_1017615) baseStart_1017615 baseEnd_1017615 := by
    simpa [prefixWord, tailWord_1017615, baseEnd_1017615] using wordTrace_append hprefix tailTrace_1017615
  have hstable : (prefixWord ++ tailWord_1017615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017615).length < 2 ^ (prefixWord ++ tailWord_1017615).sum := by decide
  have hdescent : baseEnd_1017615 < baseStart_1017615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017634 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1017634 : Nat := 118140960795 + 1017634 * 2 ^ 59
def prefixEnd_1017634 : Nat := 4983230072969 + 3 ^ 40 * 1017634 * 2
def baseEnd_1017634 : Nat := 348356914905051157329995

theorem tailTrace_1017634 : CollatzResearch.WordTrace tailWord_1017634 prefixEnd_1017634 348356914905051157329995 := by
  unfold tailWord_1017634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279040298823322723884989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24744107463528860597026637 9279040298823322723884989)
  ·
    refine ⟨3479640112058746021456871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9279040298823322723884989 3479640112058746021456871)
    ·
      refine ⟨5219460168088119032185307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479640112058746021456871 5219460168088119032185307)
      ·
        refine ⟨7829190252132178548277961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219460168088119032185307 7829190252132178548277961)
        ·
          refine ⟨5871892689099133911208471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7829190252132178548277961 5871892689099133911208471)
          ·
            refine ⟨8807839033648700866812707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871892689099133911208471 8807839033648700866812707)
            ·
              refine ⟨13211758550473051300219061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8807839033648700866812707 13211758550473051300219061)
              ·
                refine ⟨1238602364106848559395537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13211758550473051300219061 1238602364106848559395537)
                ·
                  refine ⟨928951773080136419546653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238602364106848559395537 928951773080136419546653)
                  ·
                    refine ⟨348356914905051157329995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 928951773080136419546653 348356914905051157329995)
                    ·
                      rfl

theorem cell22_1017634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1017634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017634 prefixEnd_1017634 := by exact prefixLift 1017634
  have htrace : WordTrace (prefixWord ++ tailWord_1017634) baseStart_1017634 baseEnd_1017634 := by
    simpa [prefixWord, tailWord_1017634, baseEnd_1017634] using wordTrace_append hprefix tailTrace_1017634
  have hstable : (prefixWord ++ tailWord_1017634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017634).length < 2 ^ (prefixWord ++ tailWord_1017634).sum := by decide
  have hdescent : baseEnd_1017634 < baseStart_1017634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017649 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_1017649 : Nat := 118140960795 + 1017649 * 2 ^ 59
def prefixEnd_1017649 : Nat := 4983230072969 + 3 ^ 40 * 1017649 * 2
def baseEnd_1017649 : Nat := 348362049711596118204949

theorem tailTrace_1017649 : CollatzResearch.WordTrace tailWord_1017649 prefixEnd_1017649 348362049711596118204949 := by
  unfold tailWord_1017649
  simp only [CollatzResearch.WordTrace]
  refine ⟨37116708290238948457336001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24744472193492632304890667 37116708290238948457336001)
  ·
    refine ⟨27837531217679211343002001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37116708290238948457336001 27837531217679211343002001)
    ·
      refine ⟨20878148413259408507251501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27837531217679211343002001 20878148413259408507251501)
      ·
        refine ⟨7829305654972278190219313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20878148413259408507251501 7829305654972278190219313)
        ·
          refine ⟨5871979241229208642664485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7829305654972278190219313 5871979241229208642664485)
          ·
            refine ⟨1100996107730476620499591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5871979241229208642664485 1100996107730476620499591)
            ·
              refine ⟨1651494161595714930749387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100996107730476620499591 1651494161595714930749387)
              ·
                refine ⟨2477241242393572396124081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651494161595714930749387 2477241242393572396124081)
                ·
                  refine ⟨1857930931795179297093061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477241242393572396124081 1857930931795179297093061)
                  ·
                    refine ⟨348362049711596118204949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1857930931795179297093061 348362049711596118204949)
                    ·
                      rfl

theorem cell22_1017649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_1017649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017649 prefixEnd_1017649 := by exact prefixLift 1017649
  have htrace : WordTrace (prefixWord ++ tailWord_1017649) baseStart_1017649 baseEnd_1017649 := by
    simpa [prefixWord, tailWord_1017649, baseEnd_1017649] using wordTrace_append hprefix tailTrace_1017649
  have hstable : (prefixWord ++ tailWord_1017649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017649).length < 2 ^ (prefixWord ++ tailWord_1017649).sum := by decide
  have hdescent : baseEnd_1017649 < baseStart_1017649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017705 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_1017705 : Nat := 118140960795 + 1017705 * 2 ^ 59
def prefixEnd_1017705 : Nat := 4983230072969 + 3 ^ 40 * 1017705 * 2
def baseEnd_1017705 : Nat := 348381219656030638804777

theorem tailTrace_1017705 : CollatzResearch.WordTrace tailWord_1017705 prefixEnd_1017705 348381219656030638804777 := by
  unfold tailWord_1017705
  simp only [CollatzResearch.WordTrace]
  refine ⟨37118750778036070021374569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24745833852024046680916379 37118750778036070021374569)
  ·
    refine ⟨27839063083527052516030927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37118750778036070021374569 27839063083527052516030927)
    ·
      refine ⟨41758594625290578774046391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27839063083527052516030927 41758594625290578774046391)
      ·
        refine ⟨62637891937935868161069587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41758594625290578774046391 62637891937935868161069587)
        ·
          refine ⟨93956837906903802241604381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62637891937935868161069587 93956837906903802241604381)
          ·
            refine ⟨35233814215088925840601643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93956837906903802241604381 35233814215088925840601643)
            ·
              refine ⟨52850721322633388760902465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35233814215088925840601643 52850721322633388760902465)
              ·
                refine ⟨39638040991975041570676849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52850721322633388760902465 39638040991975041570676849)
                ·
                  refine ⟨29728530743981281178007637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39638040991975041570676849 29728530743981281178007637)
                  ·
                    refine ⟨348381219656030638804777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29728530743981281178007637 348381219656030638804777)
                    ·
                      rfl

theorem cell22_1017705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_1017705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017705 prefixEnd_1017705 := by exact prefixLift 1017705
  have htrace : WordTrace (prefixWord ++ tailWord_1017705) baseStart_1017705 baseEnd_1017705 := by
    simpa [prefixWord, tailWord_1017705, baseEnd_1017705] using wordTrace_append hprefix tailTrace_1017705
  have hstable : (prefixWord ++ tailWord_1017705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017705).length < 2 ^ (prefixWord ++ tailWord_1017705).sum := by decide
  have hdescent : baseEnd_1017705 < baseStart_1017705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017756 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1017756 : Nat := 118140960795 + 1017756 * 2 ^ 59
def prefixEnd_1017756 : Nat := 4983230072969 + 3 ^ 40 * 1017756 * 2
def baseEnd_1017756 : Nat := 348398677998283505779621

theorem tailTrace_1017756 : CollatzResearch.WordTrace tailWord_1017756 prefixEnd_1017756 348398677998283505779621 := by
  unfold tailWord_1017756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560305450425652865740561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24747073933900870487654081 18560305450425652865740561)
  ·
    refine ⟨13920229087819239649305421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18560305450425652865740561 13920229087819239649305421)
    ·
      refine ⟨5220085907932214868489533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13920229087819239649305421 5220085907932214868489533)
      ·
        refine ⟨1957532215474580575683575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5220085907932214868489533 1957532215474580575683575)
        ·
          refine ⟨2936298323211870863525363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957532215474580575683575 2936298323211870863525363)
          ·
            refine ⟨4404447484817806295288045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936298323211870863525363 4404447484817806295288045)
            ·
              refine ⟨1651667806806677360733017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4404447484817806295288045 1651667806806677360733017)
              ·
                refine ⟨1238750855105008020549763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651667806806677360733017 1238750855105008020549763)
                ·
                  refine ⟨1858126282657512030824645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238750855105008020549763 1858126282657512030824645)
                  ·
                    refine ⟨348398677998283505779621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858126282657512030824645 348398677998283505779621)
                    ·
                      rfl

theorem cell22_1017756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1017756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017756 prefixEnd_1017756 := by exact prefixLift 1017756
  have htrace : WordTrace (prefixWord ++ tailWord_1017756) baseStart_1017756 baseEnd_1017756 := by
    simpa [prefixWord, tailWord_1017756, baseEnd_1017756] using wordTrace_append hprefix tailTrace_1017756
  have hstable : (prefixWord ++ tailWord_1017756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017756).length < 2 ^ (prefixWord ++ tailWord_1017756).sum := by decide
  have hdescent : baseEnd_1017756 < baseStart_1017756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017788 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 4]
def baseStart_1017788 : Nat := 118140960795 + 1017788 * 2 ^ 59
def prefixEnd_1017788 : Nat := 4983230072969 + 3 ^ 40 * 1017788 * 2
def baseEnd_1017788 : Nat := 116136544084082029659841

theorem tailTrace_1017788 : CollatzResearch.WordTrace tailWord_1017788 prefixEnd_1017788 116136544084082029659841 := by
  unfold tailWord_1017788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560889018367687598323009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24747852024490250131097345 18560889018367687598323009)
  ·
    refine ⟨13920666763775765698742257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18560889018367687598323009 13920666763775765698742257)
    ·
      refine ⟨10440500072831824274056693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13920666763775765698742257 10440500072831824274056693)
      ·
        refine ⟨978796881827983525692815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10440500072831824274056693 978796881827983525692815)
        ·
          refine ⟨1468195322741975288539223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978796881827983525692815 1468195322741975288539223)
          ·
            refine ⟨2202292984112962932808835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468195322741975288539223 2202292984112962932808835)
            ·
              refine ⟨3303439476169444399213253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202292984112962932808835 3303439476169444399213253)
              ·
                refine ⟨619394901781770824852485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3303439476169444399213253 619394901781770824852485)
                ·
                  refine ⟨116136544084082029659841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619394901781770824852485 116136544084082029659841)
                  ·
                    rfl

theorem cell22_1017788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_1017788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017788 prefixEnd_1017788 := by exact prefixLift 1017788
  have htrace : WordTrace (prefixWord ++ tailWord_1017788) baseStart_1017788 baseEnd_1017788 := by
    simpa [prefixWord, tailWord_1017788, baseEnd_1017788] using wordTrace_append hprefix tailTrace_1017788
  have hstable : (prefixWord ++ tailWord_1017788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017788).length < 2 ^ (prefixWord ++ tailWord_1017788).sum := by decide
  have hdescent : baseEnd_1017788 < baseStart_1017788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017818 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_1017818 : Nat := 118140960795 + 1017818 * 2 ^ 59
def prefixEnd_1017818 : Nat := 4983230072969 + 3 ^ 40 * 1017818 * 2
def baseEnd_1017818 : Nat := 348419901865336010729431

theorem tailTrace_1017818 : CollatzResearch.WordTrace tailWord_1017818 prefixEnd_1017818 348419901865336010729431 := by
  unfold tailWord_1017818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280718056656672580059527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24748581484417793546825405 9280718056656672580059527)
  ·
    refine ⟨13921077084985008870089291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9280718056656672580059527 13921077084985008870089291)
    ·
      refine ⟨20881615627477513305133937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921077084985008870089291 20881615627477513305133937)
      ·
        refine ⟨15661211720608134978850453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20881615627477513305133937 15661211720608134978850453)
        ·
          refine ⟨734119299403506327133615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15661211720608134978850453 734119299403506327133615)
          ·
            refine ⟨1101178949105259490700423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734119299403506327133615 1101178949105259490700423)
            ·
              refine ⟨1651768423657889236050635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101178949105259490700423 1651768423657889236050635)
              ·
                refine ⟨2477652635486833854075953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651768423657889236050635 2477652635486833854075953)
                ·
                  refine ⟨1858239476615125390556965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477652635486833854075953 1858239476615125390556965)
                  ·
                    refine ⟨348419901865336010729431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858239476615125390556965 348419901865336010729431)
                    ·
                      rfl

theorem cell22_1017818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_1017818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017818 prefixEnd_1017818 := by exact prefixLift 1017818
  have htrace : WordTrace (prefixWord ++ tailWord_1017818) baseStart_1017818 baseEnd_1017818 := by
    simpa [prefixWord, tailWord_1017818, baseEnd_1017818] using wordTrace_append hprefix tailTrace_1017818
  have hstable : (prefixWord ++ tailWord_1017818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017818).length < 2 ^ (prefixWord ++ tailWord_1017818).sum := by decide
  have hdescent : baseEnd_1017818 < baseStart_1017818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017837 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1017837 : Nat := 118140960795 + 1017837 * 2 ^ 59
def prefixEnd_1017837 : Nat := 4983230072969 + 3 ^ 40 * 1017837 * 2
def baseEnd_1017837 : Nat := 348426405953626294504373

theorem tailTrace_1017837 : CollatzResearch.WordTrace tailWord_1017837 prefixEnd_1017837 348426405953626294504373 := by
  unfold tailWord_1017837
  simp only [CollatzResearch.WordTrace]
  refine ⟨37123565213557856565179765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24749043475705237710119843 37123565213557856565179765)
  ·
    refine ⟨3480334238771049052985603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37123565213557856565179765 3480334238771049052985603)
    ·
      refine ⟨5220501358156573579478405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480334238771049052985603 5220501358156573579478405)
      ·
        refine ⟨978844004654357546152201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5220501358156573579478405 978844004654357546152201)
        ·
          refine ⟨734133003490768159614151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978844004654357546152201 734133003490768159614151)
          ·
            refine ⟨1101199505236152239421227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734133003490768159614151 1101199505236152239421227)
            ·
              refine ⟨1651799257854228359131841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101199505236152239421227 1651799257854228359131841)
              ·
                refine ⟨1238849443390671269348881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651799257854228359131841 1238849443390671269348881)
                ·
                  refine ⟨929137082543003452011661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1238849443390671269348881 929137082543003452011661)
                  ·
                    refine ⟨348426405953626294504373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929137082543003452011661 348426405953626294504373)
                    ·
                      rfl

theorem cell22_1017837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1017837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017837 prefixEnd_1017837 := by exact prefixLift 1017837
  have htrace : WordTrace (prefixWord ++ tailWord_1017837) baseStart_1017837 baseEnd_1017837 := by
    simpa [prefixWord, tailWord_1017837, baseEnd_1017837] using wordTrace_append hprefix tailTrace_1017837
  have hstable : (prefixWord ++ tailWord_1017837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017837).length < 2 ^ (prefixWord ++ tailWord_1017837).sum := by decide
  have hdescent : baseEnd_1017837 < baseStart_1017837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017861 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 5]
def baseStart_1017861 : Nat := 118140960795 + 1017861 * 2 ^ 59
def prefixEnd_1017861 : Nat := 4983230072969 + 3 ^ 40 * 1017861 * 2
def baseEnd_1017861 : Nat := 116144873881366077301433

theorem tailTrace_1017861 : CollatzResearch.WordTrace tailWord_1017861 prefixEnd_1017861 116144873881366077301433 := by
  unfold tailWord_1017861
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124440565470908664053437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24749627043647272442702291 37124440565470908664053437)
  ·
    refine ⟨13921665212051590749020039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37124440565470908664053437 13921665212051590749020039)
    ·
      refine ⟨20882497818077386123530059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921665212051590749020039 20882497818077386123530059)
      ·
        refine ⟨31323746727116079185295089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20882497818077386123530059 31323746727116079185295089)
        ·
          refine ⟨23492810045337059388971317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31323746727116079185295089 23492810045337059388971317)
          ·
            refine ⟨2202450941750349317716061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23492810045337059388971317 2202450941750349317716061)
            ·
              refine ⟨825919103156380994143523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202450941750349317716061 825919103156380994143523)
              ·
                refine ⟨1238878654734571491215285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825919103156380994143523 1238878654734571491215285)
                ·
                  refine ⟨116144873881366077301433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1238878654734571491215285 116144873881366077301433)
                  ·
                    rfl

theorem cell22_1017861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_1017861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017861 prefixEnd_1017861 := by exact prefixLift 1017861
  have htrace : WordTrace (prefixWord ++ tailWord_1017861) baseStart_1017861 baseEnd_1017861 := by
    simpa [prefixWord, tailWord_1017861, baseEnd_1017861] using wordTrace_append hprefix tailTrace_1017861
  have hstable : (prefixWord ++ tailWord_1017861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017861).length < 2 ^ (prefixWord ++ tailWord_1017861).sum := by decide
  have hdescent : baseEnd_1017861 < baseStart_1017861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017906 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_1017906 : Nat := 118140960795 + 1017906 * 2 ^ 59
def prefixEnd_1017906 : Nat := 4983230072969 + 3 ^ 40 * 1017906 * 2
def baseEnd_1017906 : Nat := 116150008687911038176387

theorem tailTrace_1017906 : CollatzResearch.WordTrace tailWord_1017906 prefixEnd_1017906 116150008687911038176387 := by
  unfold tailWord_1017906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9281520462576970337360393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24750721233538587566294381 9281520462576970337360393)
  ·
    refine ⟨6961140346932727753020295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9281520462576970337360393 6961140346932727753020295)
    ·
      refine ⟨10441710520399091629530443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961140346932727753020295 10441710520399091629530443)
      ·
        refine ⟨15662565780598637444295665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10441710520399091629530443 15662565780598637444295665)
        ·
          refine ⟨11746924335448978083221749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15662565780598637444295665 11746924335448978083221749)
          ·
            refine ⟨1101274156448341695302039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11746924335448978083221749 1101274156448341695302039)
            ·
              refine ⟨1651911234672512542953059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101274156448341695302039 1651911234672512542953059)
              ·
                refine ⟨2477866852008768814429589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651911234672512542953059 2477866852008768814429589)
                ·
                  refine ⟨116150008687911038176387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2477866852008768814429589 116150008687911038176387)
                  ·
                    rfl

theorem cell22_1017906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_1017906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017906 prefixEnd_1017906 := by exact prefixLift 1017906
  have htrace : WordTrace (prefixWord ++ tailWord_1017906) baseStart_1017906 baseEnd_1017906 := by
    simpa [prefixWord, tailWord_1017906, baseEnd_1017906] using wordTrace_append hprefix tailTrace_1017906
  have hstable : (prefixWord ++ tailWord_1017906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017906).length < 2 ^ (prefixWord ++ tailWord_1017906).sum := by decide
  have hdescent : baseEnd_1017906 < baseStart_1017906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017934 : List Nat := [4, 1, 1, 1, 1, 4, 2, 8]
def baseStart_1017934 : Nat := 118140960795 + 1017934 * 2 ^ 59
def prefixEnd_1017934 : Nat := 4983230072969 + 3 ^ 40 * 1017934 * 2
def baseEnd_1017934 : Nat := 38717734559550041647675

theorem tailTrace_1017934 : CollatzResearch.WordTrace tailWord_1017934 prefixEnd_1017934 38717734559550041647675 := by
  unfold tailWord_1017934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640887886775805266432607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24751402062804294754307237 4640887886775805266432607)
  ·
    refine ⟨6961331830163707899648911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4640887886775805266432607 6961331830163707899648911)
    ·
      refine ⟨10441997745245561849473367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961331830163707899648911 10441997745245561849473367)
      ·
        refine ⟨15662996617868342774210051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10441997745245561849473367 15662996617868342774210051)
        ·
          refine ⟨23494494926802514161315077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15662996617868342774210051 23494494926802514161315077)
          ·
            refine ⟨4405217798775471405246577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23494494926802514161315077 4405217798775471405246577)
            ·
              refine ⟨3303913349081603553934933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4405217798775471405246577 3303913349081603553934933)
              ·
                refine ⟨38717734559550041647675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3303913349081603553934933 38717734559550041647675)
                ·
                  rfl

theorem cell22_1017934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_1017934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017934 prefixEnd_1017934 := by exact prefixLift 1017934
  have htrace : WordTrace (prefixWord ++ tailWord_1017934) baseStart_1017934 baseEnd_1017934 := by
    simpa [prefixWord, tailWord_1017934, baseEnd_1017934] using wordTrace_append hprefix tailTrace_1017934
  have hstable : (prefixWord ++ tailWord_1017934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017934).length < 2 ^ (prefixWord ++ tailWord_1017934).sum := by decide
  have hdescent : baseEnd_1017934 < baseStart_1017934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017942 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1017942 : Nat := 118140960795 + 1017942 * 2 ^ 59
def prefixEnd_1017942 : Nat := 4983230072969 + 3 ^ 40 * 1017942 * 2
def baseEnd_1017942 : Nat := 348462349599441020629051

theorem tailTrace_1017942 : CollatzResearch.WordTrace tailWord_1017942 prefixEnd_1017942 348462349599441020629051 := by
  unfold tailWord_1017942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320462179886091218609505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24751596585451639665168053 2320462179886091218609505)
  ·
    refine ⟨1740346634914568413957129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2320462179886091218609505 1740346634914568413957129)
    ·
      refine ⟨1305259976185926310467847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1740346634914568413957129 1305259976185926310467847)
      ·
        refine ⟨1957889964278889465701771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305259976185926310467847 1957889964278889465701771)
        ·
          refine ⟨2936834946418334198552657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957889964278889465701771 2936834946418334198552657)
          ·
            refine ⟨2202626209813750648914493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2936834946418334198552657 2202626209813750648914493)
            ·
              refine ⟨825984828680156493342935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202626209813750648914493 825984828680156493342935)
              ·
                refine ⟨1238977243020234740014403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825984828680156493342935 1238977243020234740014403)
                ·
                  refine ⟨1858465864530352110021605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238977243020234740014403 1858465864530352110021605)
                  ·
                    refine ⟨348462349599441020629051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858465864530352110021605 348462349599441020629051)
                    ·
                      rfl

theorem cell22_1017942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1017942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017942 prefixEnd_1017942 := by exact prefixLift 1017942
  have htrace : WordTrace (prefixWord ++ tailWord_1017942) baseStart_1017942 baseEnd_1017942 := by
    simpa [prefixWord, tailWord_1017942, baseEnd_1017942] using wordTrace_append hprefix tailTrace_1017942
  have hstable : (prefixWord ++ tailWord_1017942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017942).length < 2 ^ (prefixWord ++ tailWord_1017942).sum := by decide
  have hdescent : baseEnd_1017942 < baseStart_1017942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1017964 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1017964 : Nat := 118140960795 + 1017964 * 2 ^ 59
def prefixEnd_1017964 : Nat := 4983230072969 + 3 ^ 40 * 1017964 * 2
def baseEnd_1017964 : Nat := 348469880649040296578983

theorem tailTrace_1017964 : CollatzResearch.WordTrace tailWord_1017964 prefixEnd_1017964 348469880649040296578983 := by
  unfold tailWord_1017964
  simp only [CollatzResearch.WordTrace]
  refine ⟨18564098642048878627526473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24752131522731838170035297 18564098642048878627526473)
  ·
    refine ⟨13923073981536658970644855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18564098642048878627526473 13923073981536658970644855)
    ·
      refine ⟨20884610972304988455967283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923073981536658970644855 20884610972304988455967283)
      ·
        refine ⟨31326916458457482683950925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20884610972304988455967283 31326916458457482683950925)
        ·
          refine ⟨11747593671921556006481597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31326916458457482683950925 11747593671921556006481597)
          ·
            refine ⟨4405347626970583502430599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11747593671921556006481597 4405347626970583502430599)
            ·
              refine ⟨6608021440455875253645899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405347626970583502430599 6608021440455875253645899)
              ·
                refine ⟨9912032160683812880468849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6608021440455875253645899 9912032160683812880468849)
                ·
                  refine ⟨7434024120512859660351637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9912032160683812880468849 7434024120512859660351637)
                  ·
                    refine ⟨348469880649040296578983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7434024120512859660351637 348469880649040296578983)
                    ·
                      rfl

theorem cell22_1017964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1017964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1017964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1017964 prefixEnd_1017964 := by exact prefixLift 1017964
  have htrace : WordTrace (prefixWord ++ tailWord_1017964) baseStart_1017964 baseEnd_1017964 := by
    simpa [prefixWord, tailWord_1017964, baseEnd_1017964] using wordTrace_append hprefix tailTrace_1017964
  have hstable : (prefixWord ++ tailWord_1017964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1017964).length < 2 ^ (prefixWord ++ tailWord_1017964).sum := by decide
  have hdescent : baseEnd_1017964 < baseStart_1017964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1017964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018013 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 5]
def baseStart_1018013 : Nat := 118140960795 + 1018013 * 2 ^ 59
def prefixEnd_1018013 : Nat := 4983230072969 + 3 ^ 40 * 1018013 * 2
def baseEnd_1018013 : Nat := 116162218116806834034611

theorem tailTrace_1018013 : CollatzResearch.WordTrace tailWord_1018013 prefixEnd_1018013 116162218116806834034611 := by
  unfold tailWord_1018013
  simp only [CollatzResearch.WordTrace]
  refine ⟨37129984460920238623586693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24753322973946825749057795 37129984460920238623586693)
  ·
    refine ⟨6961872086422544741922505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37129984460920238623586693 6961872086422544741922505)
    ·
      refine ⟨5221404064816908556441879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6961872086422544741922505 5221404064816908556441879)
      ·
        refine ⟨7832106097225362834662819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5221404064816908556441879 7832106097225362834662819)
        ·
          refine ⟨11748159145838044251994229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7832106097225362834662819 11748159145838044251994229)
          ·
            refine ⟨1101389919922316648624459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11748159145838044251994229 1101389919922316648624459)
            ·
              refine ⟨1652084879883474972936689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101389919922316648624459 1652084879883474972936689)
              ·
                refine ⟨1239063659912606229702517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652084879883474972936689 1239063659912606229702517)
                ·
                  refine ⟨116162218116806834034611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239063659912606229702517 116162218116806834034611)
                  ·
                    rfl

theorem cell22_1018013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_1018013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018013 prefixEnd_1018013 := by exact prefixLift 1018013
  have htrace : WordTrace (prefixWord ++ tailWord_1018013) baseStart_1018013 baseEnd_1018013 := by
    simpa [prefixWord, tailWord_1018013, baseEnd_1018013] using wordTrace_append hprefix tailTrace_1018013
  have hstable : (prefixWord ++ tailWord_1018013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018013).length < 2 ^ (prefixWord ++ tailWord_1018013).sum := by decide
  have hdescent : baseEnd_1018013 < baseStart_1018013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018148 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1018148 : Nat := 118140960795 + 1018148 * 2 ^ 59
def prefixEnd_1018148 : Nat := 4983230072969 + 3 ^ 40 * 1018148 * 2
def baseEnd_1018148 : Nat := 116177622536441716659473

theorem tailTrace_1018148 : CollatzResearch.WordTrace tailWord_1018148 prefixEnd_1018148 116177622536441716659473 := by
  unfold tailWord_1018148
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567454157715578339875549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24756605543620771119834065 18567454157715578339875549)
  ·
    refine ⟨6962795309143341877453331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18567454157715578339875549 6962795309143341877453331)
    ·
      refine ⟨10444192963715012816179997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6962795309143341877453331 10444192963715012816179997)
      ·
        refine ⟨3916572361393129806067499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10444192963715012816179997 3916572361393129806067499)
        ·
          refine ⟨5874858542089694709101249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916572361393129806067499 5874858542089694709101249)
          ·
            refine ⟨4406143906567271031825937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5874858542089694709101249 4406143906567271031825937)
            ·
              refine ⟨3304607929925453273869453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4406143906567271031825937 3304607929925453273869453)
              ·
                refine ⟨1239227973722044977701045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3304607929925453273869453 1239227973722044977701045)
                ·
                  refine ⟨116177622536441716659473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239227973722044977701045 116177622536441716659473)
                  ·
                    rfl

theorem cell22_1018148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1018148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018148 prefixEnd_1018148 := by exact prefixLift 1018148
  have htrace : WordTrace (prefixWord ++ tailWord_1018148) baseStart_1018148 baseEnd_1018148 := by
    simpa [prefixWord, tailWord_1018148, baseEnd_1018148] using wordTrace_append hprefix tailTrace_1018148
  have hstable : (prefixWord ++ tailWord_1018148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018148).length < 2 ^ (prefixWord ++ tailWord_1018148).sum := by decide
  have hdescent : baseEnd_1018148 < baseStart_1018148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018193 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 6]
def baseStart_1018193 : Nat := 118140960795 + 1018193 * 2 ^ 59
def prefixEnd_1018193 : Nat := 4983230072969 + 3 ^ 40 * 1018193 * 2
def baseEnd_1018193 : Nat := 116182757342986677534427

theorem tailTrace_1018193 : CollatzResearch.WordTrace tailWord_1018193 prefixEnd_1018193 116182757342986677534427 := by
  unfold tailWord_1018193
  simp only [CollatzResearch.WordTrace]
  refine ⟨37136549600268129365139233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24757699733512086243426155 37136549600268129365139233)
  ·
    refine ⟨27852412200201097023854425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37136549600268129365139233 27852412200201097023854425)
    ·
      refine ⟨20889309150150822767890819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27852412200201097023854425 20889309150150822767890819)
      ·
        refine ⟨31333963725226234151836229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20889309150150822767890819 31333963725226234151836229)
        ·
          refine ⟨5875118198479918903469293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31333963725226234151836229 5875118198479918903469293)
          ·
            refine ⟨2203169324429969588800985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5875118198479918903469293 2203169324429969588800985)
            ·
              refine ⟨1652376993322477191600739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203169324429969588800985 1652376993322477191600739)
              ·
                refine ⟨2478565489983715787401109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652376993322477191600739 2478565489983715787401109)
                ·
                  refine ⟨116182757342986677534427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2478565489983715787401109 116182757342986677534427)
                  ·
                    rfl

theorem cell22_1018193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_1018193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018193 prefixEnd_1018193 := by exact prefixLift 1018193
  have htrace : WordTrace (prefixWord ++ tailWord_1018193) baseStart_1018193 baseEnd_1018193 := by
    simpa [prefixWord, tailWord_1018193, baseEnd_1018193] using wordTrace_append hprefix tailTrace_1018193
  have hstable : (prefixWord ++ tailWord_1018193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018193).length < 2 ^ (prefixWord ++ tailWord_1018193).sum := by decide
  have hdescent : baseEnd_1018193 < baseStart_1018193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018300 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 5]
def baseStart_1018300 : Nat := 118140960795 + 1018300 * 2 ^ 59
def prefixEnd_1018300 : Nat := 4983230072969 + 3 ^ 40 * 1018300 * 2
def baseEnd_1018300 : Nat := 116194966771882473392651

theorem tailTrace_1018300 : CollatzResearch.WordTrace tailWord_1018300 prefixEnd_1018300 116194966771882473392651 := by
  unfold tailWord_1018300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18570226105440243319642177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24760301473920324426189569 18570226105440243319642177)
  ·
    refine ⟨13927669579080182489731633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18570226105440243319642177 13927669579080182489731633)
    ·
      refine ⟨10445752184310136867298725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13927669579080182489731633 10445752184310136867298725)
      ·
        refine ⟨1958578534558150662618511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10445752184310136867298725 1958578534558150662618511)
        ·
          refine ⟨2937867801837225993927767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958578534558150662618511 2937867801837225993927767)
          ·
            refine ⟨4406801702755838990891651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937867801837225993927767 4406801702755838990891651)
            ·
              refine ⟨6610202554133758486337477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4406801702755838990891651 6610202554133758486337477)
              ·
                refine ⟨1239412978900079716188277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6610202554133758486337477 1239412978900079716188277)
                ·
                  refine ⟨116194966771882473392651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239412978900079716188277 116194966771882473392651)
                  ·
                    rfl

theorem cell22_1018300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_1018300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018300 prefixEnd_1018300 := by exact prefixLift 1018300
  have htrace : WordTrace (prefixWord ++ tailWord_1018300) baseStart_1018300 baseEnd_1018300 := by
    simpa [prefixWord, tailWord_1018300, baseEnd_1018300] using wordTrace_append hprefix tailTrace_1018300
  have hstable : (prefixWord ++ tailWord_1018300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018300).length < 2 ^ (prefixWord ++ tailWord_1018300).sum := by decide
  have hdescent : baseEnd_1018300 < baseStart_1018300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018313 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_1018313 : Nat := 118140960795 + 1018313 * 2 ^ 59
def prefixEnd_1018313 : Nat := 4983230072969 + 3 ^ 40 * 1018313 * 2
def baseEnd_1018313 : Nat := 348589350481319719602913

theorem tailTrace_1018313 : CollatzResearch.WordTrace tailWord_1018313 prefixEnd_1018313 348589350481319719602913 := by
  unfold tailWord_1018313
  simp only [CollatzResearch.WordTrace]
  refine ⟨37140926359833389859507593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24760617573222259906338395 37140926359833389859507593)
  ·
    refine ⟨27855694769875042394630695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37140926359833389859507593 27855694769875042394630695)
    ·
      refine ⟨41783542154812563591946043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27855694769875042394630695 41783542154812563591946043)
      ·
        refine ⟨62675313232218845387919065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41783542154812563591946043 62675313232218845387919065)
        ·
          refine ⟨47006484924164134040939299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62675313232218845387919065 47006484924164134040939299)
          ·
            refine ⟨70509727386246201061408949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47006484924164134040939299 70509727386246201061408949)
            ·
              refine ⟨6610286942460581349507089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70509727386246201061408949 6610286942460581349507089)
              ·
                refine ⟨4957715206845436012130317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6610286942460581349507089 4957715206845436012130317)
                ·
                  refine ⟨1859143202567038504548869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4957715206845436012130317 1859143202567038504548869)
                  ·
                    refine ⟨348589350481319719602913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859143202567038504548869 348589350481319719602913)
                    ·
                      rfl

theorem cell22_1018313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_1018313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018313 prefixEnd_1018313 := by exact prefixLift 1018313
  have htrace : WordTrace (prefixWord ++ tailWord_1018313) baseStart_1018313 baseEnd_1018313 := by
    simpa [prefixWord, tailWord_1018313, baseEnd_1018313] using wordTrace_append hprefix tailTrace_1018313
  have hstable : (prefixWord ++ tailWord_1018313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018313).length < 2 ^ (prefixWord ++ tailWord_1018313).sum := by decide
  have hdescent : baseEnd_1018313 < baseStart_1018313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018330 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_1018330 : Nat := 118140960795 + 1018330 * 2 ^ 59
def prefixEnd_1018330 : Nat := 4983230072969 + 3 ^ 40 * 1018330 * 2
def baseEnd_1018330 : Nat := 348595169928737341927861

theorem tailTrace_1018330 : CollatzResearch.WordTrace tailWord_1018330 prefixEnd_1018330 348595169928737341927861 := by
  unfold tailWord_1018330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285386600192950440719111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24761030933847867841917629 9285386600192950440719111)
  ·
    refine ⟨13928079900289425661078667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9285386600192950440719111 13928079900289425661078667)
    ·
      refine ⟨20892119850434138491618001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13928079900289425661078667 20892119850434138491618001)
      ·
        refine ⟨15669089887825603868713501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20892119850434138491618001 15669089887825603868713501)
        ·
          refine ⟨5875908707934601450767563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15669089887825603868713501 5875908707934601450767563)
          ·
            refine ⟨8813863061901902176151345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875908707934601450767563 8813863061901902176151345)
            ·
              refine ⟨6610397296426426632113509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8813863061901902176151345 6610397296426426632113509)
              ·
                refine ⟨1239449493079954993521283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6610397296426426632113509 1239449493079954993521283)
                ·
                  refine ⟨1859174239619932490281925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239449493079954993521283 1859174239619932490281925)
                  ·
                    refine ⟨348595169928737341927861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859174239619932490281925 348595169928737341927861)
                    ·
                      rfl

theorem cell22_1018330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_1018330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018330 prefixEnd_1018330 := by exact prefixLift 1018330
  have htrace : WordTrace (prefixWord ++ tailWord_1018330) baseStart_1018330 baseEnd_1018330 := by
    simpa [prefixWord, tailWord_1018330, baseEnd_1018330] using wordTrace_append hprefix tailTrace_1018330
  have hstable : (prefixWord ++ tailWord_1018330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018330).length < 2 ^ (prefixWord ++ tailWord_1018330).sum := by decide
  have hdescent : baseEnd_1018330 < baseStart_1018330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018338 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1018338 : Nat := 118140960795 + 1018338 * 2 ^ 59
def prefixEnd_1018338 : Nat := 4983230072969 + 3 ^ 40 * 1018338 * 2
def baseEnd_1018338 : Nat := 348597908492227987727837

theorem tailTrace_1018338 : CollatzResearch.WordTrace tailWord_1018338 prefixEnd_1018338 348597908492227987727837 := by
  unfold tailWord_1018338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285459546185704782291917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24761225456495212752778445 9285459546185704782291917)
  ·
    refine ⟨3482047329819639293359469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9285459546185704782291917 3482047329819639293359469)
    ·
      refine ⟨1305767748682364735009801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3482047329819639293359469 1305767748682364735009801)
      ·
        refine ⟨979325811511773551257351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305767748682364735009801 979325811511773551257351)
        ·
          refine ⟨1468988717267660326886027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979325811511773551257351 1468988717267660326886027)
          ·
            refine ⟨2203483075901490490329041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468988717267660326886027 2203483075901490490329041)
            ·
              refine ⟨1652612306926117867746781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203483075901490490329041 1652612306926117867746781)
              ·
                refine ⟨619729615097294200405043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1652612306926117867746781 619729615097294200405043)
                ·
                  refine ⟨929594422645941300607565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619729615097294200405043 929594422645941300607565)
                  ·
                    refine ⟨348597908492227987727837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929594422645941300607565 348597908492227987727837)
                    ·
                      rfl

theorem cell22_1018338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1018338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018338 prefixEnd_1018338 := by exact prefixLift 1018338
  have htrace : WordTrace (prefixWord ++ tailWord_1018338) baseStart_1018338 baseEnd_1018338 := by
    simpa [prefixWord, tailWord_1018338, baseEnd_1018338] using wordTrace_append hprefix tailTrace_1018338
  have hstable : (prefixWord ++ tailWord_1018338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018338).length < 2 ^ (prefixWord ++ tailWord_1018338).sum := by decide
  have hdescent : baseEnd_1018338 < baseStart_1018338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018360 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 4, 3]
def baseStart_1018360 : Nat := 118140960795 + 1018360 * 2 ^ 59
def prefixEnd_1018360 : Nat := 4983230072969 + 3 ^ 40 * 1018360 * 2
def baseEnd_1018360 : Nat := 348605439541827263677769

theorem tailTrace_1018360 : CollatzResearch.WordTrace tailWord_1018360 prefixEnd_1018360 348605439541827263677769 := by
  unfold tailWord_1018360
  simp only [CollatzResearch.WordTrace]
  refine ⟨18571320295331558443234267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24761760393775411257645689 18571320295331558443234267)
  ·
    refine ⟨27856980442997337664851401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18571320295331558443234267 27856980442997337664851401)
    ·
      refine ⟨20892735332248003248638551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27856980442997337664851401 20892735332248003248638551)
      ·
        refine ⟨31339102998372004872957827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20892735332248003248638551 31339102998372004872957827)
        ·
          refine ⟨47008654497558007309436741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31339102998372004872957827 47008654497558007309436741)
          ·
            refine ⟨8814122718292126370519389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47008654497558007309436741 8814122718292126370519389)
            ·
              refine ⟨3305296019359547388944771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8814122718292126370519389 3305296019359547388944771)
              ·
                refine ⟨4957944029039321083417157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305296019359547388944771 4957944029039321083417157)
                ·
                  refine ⟨929614505444872703140717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4957944029039321083417157 929614505444872703140717)
                  ·
                    refine ⟨348605439541827263677769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929614505444872703140717 348605439541827263677769)
                    ·
                      rfl

theorem cell22_1018360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 4, 3].length) (baseStart_1018360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018360 prefixEnd_1018360 := by exact prefixLift 1018360
  have htrace : WordTrace (prefixWord ++ tailWord_1018360) baseStart_1018360 baseEnd_1018360 := by
    simpa [prefixWord, tailWord_1018360, baseEnd_1018360] using wordTrace_append hprefix tailTrace_1018360
  have hstable : (prefixWord ++ tailWord_1018360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018360).length < 2 ^ (prefixWord ++ tailWord_1018360).sum := by decide
  have hdescent : baseEnd_1018360 < baseStart_1018360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018381 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1018381 : Nat := 118140960795 + 1018381 * 2 ^ 59
def prefixEnd_1018381 : Nat := 4983230072969 + 3 ^ 40 * 1018381 * 2
def baseEnd_1018381 : Nat := 348612628270990208902705

theorem tailTrace_1018381 : CollatzResearch.WordTrace tailWord_1018381 prefixEnd_1018381 348612628270990208902705 := by
  unfold tailWord_1018381
  simp only [CollatzResearch.WordTrace]
  refine ⟨37143406523587037472982997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24762271015724691648655331 37143406523587037472982997)
  ·
    refine ⟨870548590396571190773039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37143406523587037472982997 870548590396571190773039)
    ·
      refine ⟨1305822885594856786159559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870548590396571190773039 1305822885594856786159559)
      ·
        refine ⟨1958734328392285179239339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305822885594856786159559 1958734328392285179239339)
        ·
          refine ⟨2938101492588427768859009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958734328392285179239339 2938101492588427768859009)
          ·
            refine ⟨2203576119441320826644257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2938101492588427768859009 2203576119441320826644257)
            ·
              refine ⟨1652682089580990619983193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203576119441320826644257 1652682089580990619983193)
              ·
                refine ⟨1239511567185742964987395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652682089580990619983193 1239511567185742964987395)
                ·
                  refine ⟨1859267350778614447481093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239511567185742964987395 1859267350778614447481093)
                  ·
                    refine ⟨348612628270990208902705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859267350778614447481093 348612628270990208902705)
                    ·
                      rfl

theorem cell22_1018381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1018381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018381 prefixEnd_1018381 := by exact prefixLift 1018381
  have htrace : WordTrace (prefixWord ++ tailWord_1018381) baseStart_1018381 baseEnd_1018381 := by
    simpa [prefixWord, tailWord_1018381, baseEnd_1018381] using wordTrace_append hprefix tailTrace_1018381
  have hstable : (prefixWord ++ tailWord_1018381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018381).length < 2 ^ (prefixWord ++ tailWord_1018381).sum := by decide
  have hdescent : baseEnd_1018381 < baseStart_1018381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018405 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_1018405 : Nat := 118140960795 + 1018405 * 2 ^ 59
def prefixEnd_1018405 : Nat := 4983230072969 + 3 ^ 40 * 1018405 * 2
def baseEnd_1018405 : Nat := 348620843961462146302631

theorem tailTrace_1018405 : CollatzResearch.WordTrace tailWord_1018405 prefixEnd_1018405 348620843961462146302631 := by
  unfold tailWord_1018405
  simp only [CollatzResearch.WordTrace]
  refine ⟨37144281875500089571856669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24762854583666726381237779 37144281875500089571856669)
  ·
    refine ⟨13929105703312533589446251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37144281875500089571856669 13929105703312533589446251)
    ·
      refine ⟨20893658554968800384169377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13929105703312533589446251 20893658554968800384169377)
      ·
        refine ⟨15670243916226600288127033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20893658554968800384169377 15670243916226600288127033)
        ·
          refine ⟨11752682937169950216095275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15670243916226600288127033 11752682937169950216095275)
          ·
            refine ⟨17629024405754925324142913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752682937169950216095275 17629024405754925324142913)
            ·
              refine ⟨13221768304316193993107185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17629024405754925324142913 13221768304316193993107185)
              ·
                refine ⟨9916326228237145494830389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13221768304316193993107185 9916326228237145494830389)
                ·
                  refine ⟨929655583897232390140349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9916326228237145494830389 929655583897232390140349)
                  ·
                    refine ⟨348620843961462146302631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929655583897232390140349 348620843961462146302631)
                    ·
                      rfl

theorem cell22_1018405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_1018405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018405 prefixEnd_1018405 := by exact prefixLift 1018405
  have htrace : WordTrace (prefixWord ++ tailWord_1018405) baseStart_1018405 baseEnd_1018405 := by
    simpa [prefixWord, tailWord_1018405, baseEnd_1018405] using wordTrace_append hprefix tailTrace_1018405
  have hstable : (prefixWord ++ tailWord_1018405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018405).length < 2 ^ (prefixWord ++ tailWord_1018405).sum := by decide
  have hdescent : baseEnd_1018405 < baseStart_1018405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018413 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1018413 : Nat := 118140960795 + 1018413 * 2 ^ 59
def prefixEnd_1018413 : Nat := 4983230072969 + 3 ^ 40 * 1018413 * 2
def baseEnd_1018413 : Nat := 116207860841650930700869

theorem tailTrace_1018413 : CollatzResearch.WordTrace tailWord_1018413 prefixEnd_1018413 116207860841650930700869 := by
  unfold tailWord_1018413
  simp only [CollatzResearch.WordTrace]
  refine ⟨37144573659471106938147893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24763049106314071292098595 37144573659471106938147893)
  ·
    refine ⟨3482303780575416275451365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37144573659471106938147893 3482303780575416275451365)
    ·
      refine ⟨652931958857890551647131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3482303780575416275451365 652931958857890551647131)
      ·
        refine ⟨979397938286835827470697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652931958857890551647131 979397938286835827470697)
        ·
          refine ⟨734548453715126870603023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979397938286835827470697 734548453715126870603023)
          ·
            refine ⟨1101822680572690305904535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734548453715126870603023 1101822680572690305904535)
            ·
              refine ⟨1652734020859035458856803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101822680572690305904535 1652734020859035458856803)
              ·
                refine ⟨2479101031288553188285205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652734020859035458856803 2479101031288553188285205)
                ·
                  refine ⟨116207860841650930700869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2479101031288553188285205 116207860841650930700869)
                  ·
                    rfl

theorem cell22_1018413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1018413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018413 prefixEnd_1018413 := by exact prefixLift 1018413
  have htrace : WordTrace (prefixWord ++ tailWord_1018413) baseStart_1018413 baseEnd_1018413 := by
    simpa [prefixWord, tailWord_1018413, baseEnd_1018413] using wordTrace_append hprefix tailTrace_1018413
  have hstable : (prefixWord ++ tailWord_1018413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018413).length < 2 ^ (prefixWord ++ tailWord_1018413).sum := by decide
  have hdescent : baseEnd_1018413 < baseStart_1018413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018514 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_1018514 : Nat := 118140960795 + 1018514 * 2 ^ 59
def prefixEnd_1018514 : Nat := 4983230072969 + 3 ^ 40 * 1018514 * 2
def baseEnd_1018514 : Nat := 116219385629674065109099

theorem tailTrace_1018514 : CollatzResearch.WordTrace tailWord_1018514 prefixEnd_1018514 116219385629674065109099 := by
  unfold tailWord_1018514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287064358026300296893649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24765504954736800791716397 9287064358026300296893649)
  ·
    refine ⟨6965298268519725222670237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9287064358026300296893649 6965298268519725222670237)
    ·
      refine ⟨2611986850694896958501339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6965298268519725222670237 2611986850694896958501339)
      ·
        refine ⟨3917980276042345437752009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611986850694896958501339 3917980276042345437752009)
        ·
          refine ⟨2938485207031759078314007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3917980276042345437752009 2938485207031759078314007)
          ·
            refine ⟨4407727810547638617471011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938485207031759078314007 4407727810547638617471011)
            ·
              refine ⟨6611591715821457926206517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4407727810547638617471011 6611591715821457926206517)
              ·
                refine ⟨619836723358261680581861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6611591715821457926206517 619836723358261680581861)
                ·
                  refine ⟨116219385629674065109099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 619836723358261680581861 116219385629674065109099)
                  ·
                    rfl

theorem cell22_1018514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_1018514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018514 prefixEnd_1018514 := by exact prefixLift 1018514
  have htrace : WordTrace (prefixWord ++ tailWord_1018514) baseStart_1018514 baseEnd_1018514 := by
    simpa [prefixWord, tailWord_1018514, baseEnd_1018514] using wordTrace_append hprefix tailTrace_1018514
  have hstable : (prefixWord ++ tailWord_1018514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018514).length < 2 ^ (prefixWord ++ tailWord_1018514).sum := by decide
  have hdescent : baseEnd_1018514 < baseStart_1018514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018516 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1018516 : Nat := 118140960795 + 1018516 * 2 ^ 59
def prefixEnd_1018516 : Nat := 4983230072969 + 3 ^ 40 * 1018516 * 2
def baseEnd_1018516 : Nat := 348658841529894856777291

theorem tailTrace_1018516 : CollatzResearch.WordTrace tailWord_1018516 prefixEnd_1018516 348658841529894856777291 := by
  unfold tailWord_1018516
  simp only [CollatzResearch.WordTrace]
  refine ⟨18574165189048977764573701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24765553585398637019431601 18574165189048977764573701)
  ·
    refine ⟨3482655972946683330857569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18574165189048977764573701 3482655972946683330857569)
    ·
      refine ⟨2611991979710012498143177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3482655972946683330857569 2611991979710012498143177)
      ·
        refine ⟨1958993984782509373607383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2611991979710012498143177 1958993984782509373607383)
        ·
          refine ⟨2938490977173764060411075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958993984782509373607383 2938490977173764060411075)
          ·
            refine ⟨4407736465760646090616613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938490977173764060411075 4407736465760646090616613)
            ·
              refine ⟨826450587330121141990615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4407736465760646090616613 826450587330121141990615)
              ·
                refine ⟨1239675880995181712985923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826450587330121141990615 1239675880995181712985923)
                ·
                  refine ⟨1859513821492772569478885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239675880995181712985923 1859513821492772569478885)
                  ·
                    refine ⟨348658841529894856777291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859513821492772569478885 348658841529894856777291)
                    ·
                      rfl

theorem cell22_1018516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1018516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018516 prefixEnd_1018516 := by exact prefixLift 1018516
  have htrace : WordTrace (prefixWord ++ tailWord_1018516) baseStart_1018516 baseEnd_1018516 := by
    simpa [prefixWord, tailWord_1018516, baseEnd_1018516] using wordTrace_append hprefix tailTrace_1018516
  have hstable : (prefixWord ++ tailWord_1018516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018516).length < 2 ^ (prefixWord ++ tailWord_1018516).sum := by decide
  have hdescent : baseEnd_1018516 < baseStart_1018516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018529 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_1018529 : Nat := 118140960795 + 1018529 * 2 ^ 59
def prefixEnd_1018529 : Nat := 4983230072969 + 3 ^ 40 * 1018529 * 2
def baseEnd_1018529 : Nat := 348663291695567156202251

theorem tailTrace_1018529 : CollatzResearch.WordTrace tailWord_1018529 prefixEnd_1018529 348663291695567156202251 := by
  unfold tailWord_1018529
  simp only [CollatzResearch.WordTrace]
  refine ⟨37148804527050858749370641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24765869684700572499580427 37148804527050858749370641)
  ·
    refine ⟨27861603395288144062027981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37148804527050858749370641 27861603395288144062027981)
    ·
      refine ⟨10448101273233054023260493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27861603395288144062027981 10448101273233054023260493)
      ·
        refine ⟨3918037977462395258722685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10448101273233054023260493 3918037977462395258722685)
        ·
          refine ⟨1469264241548398222021007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3918037977462395258722685 1469264241548398222021007)
          ·
            refine ⟨2203896362322597333031511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469264241548398222021007 2203896362322597333031511)
            ·
              refine ⟨3305844543483895999547267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2203896362322597333031511 3305844543483895999547267)
              ·
                refine ⟨4958766815225843999320901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305844543483895999547267 4958766815225843999320901)
                ·
                  refine ⟨929768777854845749872669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4958766815225843999320901 929768777854845749872669)
                  ·
                    refine ⟨348663291695567156202251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929768777854845749872669 348663291695567156202251)
                    ·
                      rfl

theorem cell22_1018529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_1018529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018529 prefixEnd_1018529 := by exact prefixLift 1018529
  have htrace : WordTrace (prefixWord ++ tailWord_1018529) baseStart_1018529 baseEnd_1018529 := by
    simpa [prefixWord, tailWord_1018529, baseEnd_1018529] using wordTrace_append hprefix tailTrace_1018529
  have hstable : (prefixWord ++ tailWord_1018529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018529).length < 2 ^ (prefixWord ++ tailWord_1018529).sum := by decide
  have hdescent : baseEnd_1018529 < baseStart_1018529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018615 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 8]
def baseStart_1018615 : Nat := 118140960795 + 1018615 * 2 ^ 59
def prefixEnd_1018615 : Nat := 4983230072969 + 3 ^ 40 * 1018615 * 2
def baseEnd_1018615 : Nat := 116230910417697199517329

theorem tailTrace_1018615 : CollatzResearch.WordTrace tailWord_1018615 prefixEnd_1018615 116230910417697199517329 := by
  unfold tailWord_1018615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37151941204739295437001299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24767960803159530291334199 37151941204739295437001299)
  ·
    refine ⟨55727911807108943155501949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37151941204739295437001299 55727911807108943155501949)
    ·
      refine ⟨20897966927665853683313231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55727911807108943155501949 20897966927665853683313231)
      ·
        refine ⟨31346950391498780524969847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20897966927665853683313231 31346950391498780524969847)
        ·
          refine ⟨47020425587248170787454771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31346950391498780524969847 47020425587248170787454771)
          ·
            refine ⟨70530638380872256181182157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47020425587248170787454771 70530638380872256181182157)
            ·
              refine ⟨26448989392827096067943309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70530638380872256181182157 26448989392827096067943309)
              ·
                refine ⟨9918371022310161025478741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26448989392827096067943309 9918371022310161025478741)
                ·
                  refine ⟨116230910417697199517329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9918371022310161025478741 116230910417697199517329)
                  ·
                    rfl

theorem cell22_1018615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_1018615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018615 prefixEnd_1018615 := by exact prefixLift 1018615
  have htrace : WordTrace (prefixWord ++ tailWord_1018615) baseStart_1018615 baseEnd_1018615 := by
    simpa [prefixWord, tailWord_1018615, baseEnd_1018615] using wordTrace_append hprefix tailTrace_1018615
  have hstable : (prefixWord ++ tailWord_1018615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018615).length < 2 ^ (prefixWord ++ tailWord_1018615).sum := by decide
  have hdescent : baseEnd_1018615 < baseStart_1018615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018642 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1018642 : Nat := 118140960795 + 1018642 * 2 ^ 59
def prefixEnd_1018642 : Nat := 4983230072969 + 3 ^ 40 * 1018642 * 2
def baseEnd_1018642 : Nat := 348701973904872528126905

theorem tailTrace_1018642 : CollatzResearch.WordTrace tailWord_1018642 prefixEnd_1018642 348701973904872528126905 := by
  unfold tailWord_1018642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288231493910369762058545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24768617317094319365489453 9288231493910369762058545)
  ·
    refine ⟨6966173620432777321543909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9288231493910369762058545 6966173620432777321543909)
    ·
      refine ⟨1306157553831145747789483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6966173620432777321543909 1306157553831145747789483)
      ·
        refine ⟨1959236330746718621684225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306157553831145747789483 1959236330746718621684225)
        ·
          refine ⟨1469427248060038966263169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1959236330746718621684225 1469427248060038966263169)
          ·
            refine ⟨1102070436045029224697377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1469427248060038966263169 1102070436045029224697377)
            ·
              refine ⟨826552827033771918523033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102070436045029224697377 826552827033771918523033)
              ·
                refine ⟨619914620275328938892275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826552827033771918523033 619914620275328938892275)
                ·
                  refine ⟨929871930412993408338413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619914620275328938892275 929871930412993408338413)
                  ·
                    refine ⟨348701973904872528126905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929871930412993408338413 348701973904872528126905)
                    ·
                      rfl

theorem cell22_1018642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1018642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018642 prefixEnd_1018642 := by exact prefixLift 1018642
  have htrace : WordTrace (prefixWord ++ tailWord_1018642) baseStart_1018642 baseEnd_1018642 := by
    simpa [prefixWord, tailWord_1018642, baseEnd_1018642] using wordTrace_append hprefix tailTrace_1018642
  have hstable : (prefixWord ++ tailWord_1018642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018642).length < 2 ^ (prefixWord ++ tailWord_1018642).sum := by decide
  have hdescent : baseEnd_1018642 < baseStart_1018642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018664 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1018664 : Nat := 118140960795 + 1018664 * 2 ^ 59
def prefixEnd_1018664 : Nat := 4983230072969 + 3 ^ 40 * 1018664 * 2
def baseEnd_1018664 : Nat := 348709504954471804076837

theorem tailTrace_1018664 : CollatzResearch.WordTrace tailWord_1018664 prefixEnd_1018664 348709504954471804076837 := by
  unfold tailWord_1018664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18576864190780888402767523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24769152254374517870356697 18576864190780888402767523)
  ·
    refine ⟨27865296286171332604151285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18576864190780888402767523 27865296286171332604151285)
    ·
      refine ⟨2612371526828562431639183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27865296286171332604151285 2612371526828562431639183)
      ·
        refine ⟨3918557290242843647458775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612371526828562431639183 3918557290242843647458775)
        ·
          refine ⟨5877835935364265471188163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918557290242843647458775 5877835935364265471188163)
          ·
            refine ⟨8816753903046398206782245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877835935364265471188163 8816753903046398206782245)
            ·
              refine ⟨1653141356821199663771671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8816753903046398206782245 1653141356821199663771671)
              ·
                refine ⟨2479712035231799495657507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653141356821199663771671 2479712035231799495657507)
                ·
                  refine ⟨3719568052847699243486261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479712035231799495657507 3719568052847699243486261)
                  ·
                    refine ⟨348709504954471804076837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3719568052847699243486261 348709504954471804076837)
                    ·
                      rfl

theorem cell22_1018664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1018664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018664 prefixEnd_1018664 := by exact prefixLift 1018664
  have htrace : WordTrace (prefixWord ++ tailWord_1018664) baseStart_1018664 baseEnd_1018664 := by
    simpa [prefixWord, tailWord_1018664, baseEnd_1018664] using wordTrace_append hprefix tailTrace_1018664
  have hstable : (prefixWord ++ tailWord_1018664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018664).length < 2 ^ (prefixWord ++ tailWord_1018664).sum := by decide
  have hdescent : baseEnd_1018664 < baseStart_1018664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018666 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_1018666 : Nat := 118140960795 + 1018666 * 2 ^ 59
def prefixEnd_1018666 : Nat := 4983230072969 + 3 ^ 40 * 1018666 * 2
def baseEnd_1018666 : Nat := 116236729865114821842277

theorem tailTrace_1018666 : CollatzResearch.WordTrace tailWord_1018666 prefixEnd_1018666 116236729865114821842277 := by
  unfold tailWord_1018666
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288450331888632786776963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24769200885036354098071901 9288450331888632786776963)
  ·
    refine ⟨13932675497832949180165445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9288450331888632786776963 13932675497832949180165445)
    ·
      refine ⟨2612376655843677971281021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13932675497832949180165445 2612376655843677971281021)
      ·
        refine ⟨979641245941379239230383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2612376655843677971281021 979641245941379239230383)
        ·
          refine ⟨1469461868912068858845575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979641245941379239230383 1469461868912068858845575)
          ·
            refine ⟨2204192803368103288268363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469461868912068858845575 2204192803368103288268363)
            ·
              refine ⟨3306289205052154932402545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204192803368103288268363 3306289205052154932402545)
              ·
                refine ⟨2479716903789116199301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306289205052154932402545 2479716903789116199301909)
                ·
                  refine ⟨116236729865114821842277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2479716903789116199301909 116236729865114821842277)
                  ·
                    rfl

theorem cell22_1018666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_1018666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018666 prefixEnd_1018666 := by exact prefixLift 1018666
  have htrace : WordTrace (prefixWord ++ tailWord_1018666) baseStart_1018666 baseEnd_1018666 := by
    simpa [prefixWord, tailWord_1018666, baseEnd_1018666] using wordTrace_append hprefix tailTrace_1018666
  have hstable : (prefixWord ++ tailWord_1018666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018666).length < 2 ^ (prefixWord ++ tailWord_1018666).sum := by decide
  have hdescent : baseEnd_1018666 < baseStart_1018666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018685 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_1018685 : Nat := 118140960795 + 1018685 * 2 ^ 59
def prefixEnd_1018685 : Nat := 4983230072969 + 3 ^ 40 * 1018685 * 2
def baseEnd_1018685 : Nat := 348716693683634749301773

theorem tailTrace_1018685 : CollatzResearch.WordTrace tailWord_1018685 prefixEnd_1018685 348716693683634749301773 := by
  unfold tailWord_1018685
  simp only [CollatzResearch.WordTrace]
  refine ⟨37154494314485697392049509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24769662876323798261366339 37154494314485697392049509)
  ·
    refine ⟨6966467683966068261009283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37154494314485697392049509 6966467683966068261009283)
    ·
      refine ⟨10449701525949102391513925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6966467683966068261009283 10449701525949102391513925)
      ·
        refine ⟨1959319036115456698408861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10449701525949102391513925 1959319036115456698408861)
        ·
          refine ⟨734744638543296261903323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1959319036115456698408861 734744638543296261903323)
          ·
            refine ⟨1102116957814944392854985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734744638543296261903323 1102116957814944392854985)
            ·
              refine ⟨826587718361208294641239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102116957814944392854985 826587718361208294641239)
              ·
                refine ⟨1239881577541812441961859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826587718361208294641239 1239881577541812441961859)
                ·
                  refine ⟨1859822366312718662942789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239881577541812441961859 1859822366312718662942789)
                  ·
                    refine ⟨348716693683634749301773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859822366312718662942789 348716693683634749301773)
                    ·
                      rfl

theorem cell22_1018685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_1018685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018685 prefixEnd_1018685 := by exact prefixLift 1018685
  have htrace : WordTrace (prefixWord ++ tailWord_1018685) baseStart_1018685 baseEnd_1018685 := by
    simpa [prefixWord, tailWord_1018685, baseEnd_1018685] using wordTrace_append hprefix tailTrace_1018685
  have hstable : (prefixWord ++ tailWord_1018685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018685).length < 2 ^ (prefixWord ++ tailWord_1018685).sum := by decide
  have hdescent : baseEnd_1018685 < baseStart_1018685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018760 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1018760 : Nat := 118140960795 + 1018760 * 2 ^ 59
def prefixEnd_1018760 : Nat := 4983230072969 + 3 ^ 40 * 1018760 * 2
def baseEnd_1018760 : Nat := 348742367716359553676543

theorem tailTrace_1018760 : CollatzResearch.WordTrace tailWord_1018760 prefixEnd_1018760 348742367716359553676543 := by
  unfold tailWord_1018760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18578614894606992600514867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24771486526142656800686489 18578614894606992600514867)
  ·
    refine ⟨27867922341910488900772301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18578614894606992600514867 27867922341910488900772301)
    ·
      refine ⟨10450470878216433337789613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27867922341910488900772301 10450470878216433337789613)
      ·
        refine ⟨3918926579331162501671105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10450470878216433337789613 3918926579331162501671105)
        ·
          refine ⟨2939194934498371876253329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3918926579331162501671105 2939194934498371876253329)
          ·
            refine ⟨2204396200873778907189997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939194934498371876253329 2204396200873778907189997)
            ·
              refine ⟨826648575327667090196249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2204396200873778907189997 826648575327667090196249)
              ·
                refine ⟨619986431495750317647187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826648575327667090196249 619986431495750317647187)
                ·
                  refine ⟨929979647243625476470781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619986431495750317647187 929979647243625476470781)
                  ·
                    refine ⟨348742367716359553676543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 929979647243625476470781 348742367716359553676543)
                    ·
                      rfl

theorem cell22_1018760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1018760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018760 prefixEnd_1018760 := by exact prefixLift 1018760
  have htrace : WordTrace (prefixWord ++ tailWord_1018760) baseStart_1018760 baseEnd_1018760 := by
    simpa [prefixWord, tailWord_1018760, baseEnd_1018760] using wordTrace_append hprefix tailTrace_1018760
  have hstable : (prefixWord ++ tailWord_1018760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018760).length < 2 ^ (prefixWord ++ tailWord_1018760).sum := by decide
  have hdescent : baseEnd_1018760 < baseStart_1018760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018786 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1018786 : Nat := 118140960795 + 1018786 * 2 ^ 59
def prefixEnd_1018786 : Nat := 4983230072969 + 3 ^ 40 * 1018786 * 2
def baseEnd_1018786 : Nat := 348751268047704152526463

theorem tailTrace_1018786 : CollatzResearch.WordTrace tailWord_1018786 prefixEnd_1018786 348751268047704152526463 := by
  unfold tailWord_1018786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289544521779947910369053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24772118724746527760984141 9289544521779947910369053)
  ·
    refine ⟨3483579195667480466388395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9289544521779947910369053 3483579195667480466388395)
    ·
      refine ⟨5225368793501220699582593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483579195667480466388395 5225368793501220699582593)
      ·
        refine ⟨3919026595125915524686945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5225368793501220699582593 3919026595125915524686945)
        ·
          refine ⟨2939269946344436643515209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3919026595125915524686945 2939269946344436643515209)
          ·
            refine ⟨2204452459758327482636407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939269946344436643515209 2204452459758327482636407)
            ·
              refine ⟨3306678689637491223954611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204452459758327482636407 3306678689637491223954611)
              ·
                refine ⟨4960018034456236835931917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306678689637491223954611 4960018034456236835931917)
                ·
                  refine ⟨1860006762921088813474469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4960018034456236835931917 1860006762921088813474469)
                  ·
                    refine ⟨348751268047704152526463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860006762921088813474469 348751268047704152526463)
                    ·
                      rfl

theorem cell22_1018786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1018786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018786 prefixEnd_1018786 := by exact prefixLift 1018786
  have htrace : WordTrace (prefixWord ++ tailWord_1018786) baseStart_1018786 baseEnd_1018786 := by
    simpa [prefixWord, tailWord_1018786, baseEnd_1018786] using wordTrace_append hprefix tailTrace_1018786
  have hstable : (prefixWord ++ tailWord_1018786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018786).length < 2 ^ (prefixWord ++ tailWord_1018786).sum := by decide
  have hdescent : baseEnd_1018786 < baseStart_1018786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018799 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 4, 3]
def baseStart_1018799 : Nat := 118140960795 + 1018799 * 2 ^ 59
def prefixEnd_1018799 : Nat := 4983230072969 + 3 ^ 40 * 1018799 * 2
def baseEnd_1018799 : Nat := 348755718213376451951423

theorem tailTrace_1018799 : CollatzResearch.WordTrace tailWord_1018799 prefixEnd_1018799 348755718213376451951423 := by
  unfold tailWord_1018799
  simp only [CollatzResearch.WordTrace]
  refine ⟨37158652236072694861699451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24772434824048463241132967 37158652236072694861699451)
  ·
    refine ⟨55737978354109042292549177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37158652236072694861699451 55737978354109042292549177)
    ·
      refine ⟨41803483765581781719411883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55737978354109042292549177 41803483765581781719411883)
      ·
        refine ⟨62705225648372672579117825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41803483765581781719411883 62705225648372672579117825)
        ·
          refine ⟨47028919236279504434338369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62705225648372672579117825 47028919236279504434338369)
          ·
            refine ⟨35271689427209628325753777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47028919236279504434338369 35271689427209628325753777)
            ·
              refine ⟨26453767070407221244315333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35271689427209628325753777 26453767070407221244315333)
              ·
                refine ⟨4960081325701353983309125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26453767070407221244315333 4960081325701353983309125)
                ·
                  refine ⟨930015248569003871870461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4960081325701353983309125 930015248569003871870461)
                  ·
                    refine ⟨348755718213376451951423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 930015248569003871870461 348755718213376451951423)
                    ·
                      rfl

theorem cell22_1018799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_1018799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018799 prefixEnd_1018799 := by exact prefixLift 1018799
  have htrace : WordTrace (prefixWord ++ tailWord_1018799) baseStart_1018799 baseEnd_1018799 := by
    simpa [prefixWord, tailWord_1018799, baseEnd_1018799] using wordTrace_append hprefix tailTrace_1018799
  have hstable : (prefixWord ++ tailWord_1018799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018799).length < 2 ^ (prefixWord ++ tailWord_1018799).sum := by decide
  have hdescent : baseEnd_1018799 < baseStart_1018799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018812 : List Nat := [2, 2, 2, 16]
def baseStart_1018812 : Nat := 118140960795 + 1018812 * 2 ^ 59
def prefixEnd_1018812 : Nat := 4983230072969 + 3 ^ 40 * 1018812 * 2
def baseEnd_1018812 : Nat := 478409010122151922327

theorem tailTrace_1018812 : CollatzResearch.WordTrace tailWord_1018812 prefixEnd_1018812 478409010122151922327 := by
  unfold tailWord_1018812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18579563192512799040961345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24772750923350398721281793 18579563192512799040961345)
  ·
    refine ⟨13934672394384599280721009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18579563192512799040961345 13934672394384599280721009)
    ·
      refine ⟨10451004295788449460540757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13934672394384599280721009 10451004295788449460540757)
      ·
        refine ⟨478409010122151922327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 10451004295788449460540757 478409010122151922327)
        ·
          rfl

theorem cell22_1018812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 16].length) (baseStart_1018812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018812 prefixEnd_1018812 := by exact prefixLift 1018812
  have htrace : WordTrace (prefixWord ++ tailWord_1018812) baseStart_1018812 baseEnd_1018812 := by
    simpa [prefixWord, tailWord_1018812, baseEnd_1018812] using wordTrace_append hprefix tailTrace_1018812
  have hstable : (prefixWord ++ tailWord_1018812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018812).length < 2 ^ (prefixWord ++ tailWord_1018812).sum := by decide
  have hdescent : baseEnd_1018812 < baseStart_1018812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018816 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 2, 3]
def baseStart_1018816 : Nat := 118140960795 + 1018816 * 2 ^ 59
def prefixEnd_1018816 : Nat := 4983230072969 + 3 ^ 40 * 1018816 * 2
def baseEnd_1018816 : Nat := 348761537660794074276371

theorem tailTrace_1018816 : CollatzResearch.WordTrace tailWord_1018816 prefixEnd_1018816 348761537660794074276371 := by
  unfold tailWord_1018816
  simp only [CollatzResearch.WordTrace]
  refine ⟨18579636138505553382534151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24772848184674071176712201 18579636138505553382534151)
  ·
    refine ⟨27869454207758330073801227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18579636138505553382534151 27869454207758330073801227)
    ·
      refine ⟨41804181311637495110701841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27869454207758330073801227 41804181311637495110701841)
      ·
        refine ⟨31353135983728121333026381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41804181311637495110701841 31353135983728121333026381)
        ·
          refine ⟨11757425993898045499884893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31353135983728121333026381 11757425993898045499884893)
          ·
            refine ⟨4409034747711767062456835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11757425993898045499884893 4409034747711767062456835)
            ·
              refine ⟨6613552121567650593685253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409034747711767062456835 6613552121567650593685253)
              ·
                refine ⟨1240041022793934486315985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6613552121567650593685253 1240041022793934486315985)
                ·
                  refine ⟨930030767095450864736989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1240041022793934486315985 930030767095450864736989)
                  ·
                    refine ⟨348761537660794074276371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 930030767095450864736989 348761537660794074276371)
                    ·
                      rfl

theorem cell22_1018816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 3].length) (baseStart_1018816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018816 prefixEnd_1018816 := by exact prefixLift 1018816
  have htrace : WordTrace (prefixWord ++ tailWord_1018816) baseStart_1018816 baseEnd_1018816 := by
    simpa [prefixWord, tailWord_1018816, baseEnd_1018816] using wordTrace_append hprefix tailTrace_1018816
  have hstable : (prefixWord ++ tailWord_1018816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018816).length < 2 ^ (prefixWord ++ tailWord_1018816).sum := by decide
  have hdescent : baseEnd_1018816 < baseStart_1018816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018822 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1018822 : Nat := 118140960795 + 1018822 * 2 ^ 59
def prefixEnd_1018822 : Nat := 4983230072969 + 3 ^ 40 * 1018822 * 2
def baseEnd_1018822 : Nat := 348763591583412058626353

theorem tailTrace_1018822 : CollatzResearch.WordTrace tailWord_1018822 prefixEnd_1018822 348763591583412058626353 := by
  unfold tailWord_1018822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161234097343417805930835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24772994076659579859857813 1161234097343417805930835)
  ·
    refine ⟨1741851146015126708896253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1161234097343417805930835 1741851146015126708896253)
    ·
      refine ⟨653194179755672515836095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1741851146015126708896253 653194179755672515836095)
      ·
        refine ⟨979791269633508773754143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653194179755672515836095 979791269633508773754143)
        ·
          refine ⟨1469686904450263160631215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979791269633508773754143 1469686904450263160631215)
          ·
            refine ⟨2204530356675394740946823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469686904450263160631215 2204530356675394740946823)
            ·
              refine ⟨3306795535013092111420235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204530356675394740946823 3306795535013092111420235)
              ·
                refine ⟨4960193302519638167130353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306795535013092111420235 4960193302519638167130353)
                ·
                  refine ⟨3720144976889728625347765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960193302519638167130353 3720144976889728625347765)
                  ·
                    refine ⟨348763591583412058626353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3720144976889728625347765 348763591583412058626353)
                    ·
                      rfl

theorem cell22_1018822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1018822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018822 prefixEnd_1018822 := by exact prefixLift 1018822
  have htrace : WordTrace (prefixWord ++ tailWord_1018822) baseStart_1018822 baseEnd_1018822 := by
    simpa [prefixWord, tailWord_1018822, baseEnd_1018822] using wordTrace_append hprefix tailTrace_1018822
  have hstable : (prefixWord ++ tailWord_1018822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018822).length < 2 ^ (prefixWord ++ tailWord_1018822).sum := by decide
  have hdescent : baseEnd_1018822 < baseStart_1018822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018936 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 6]
def baseStart_1018936 : Nat := 118140960795 + 1018936 * 2 ^ 59
def prefixEnd_1018936 : Nat := 4983230072969 + 3 ^ 40 * 1018936 * 2
def baseEnd_1018936 : Nat := 116267538704384587092001

theorem tailTrace_1018936 : CollatzResearch.WordTrace tailWord_1018936 prefixEnd_1018936 116267538704384587092001 := by
  unfold tailWord_1018936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581824518288183629718331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24775766024384244839624441 18581824518288183629718331)
  ·
    refine ⟨27872736777432275444577497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18581824518288183629718331 27872736777432275444577497)
    ·
      refine ⟨20904552583074206583433123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27872736777432275444577497 20904552583074206583433123)
      ·
        refine ⟨31356828874611309875149685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20904552583074206583433123 31356828874611309875149685)
        ·
          refine ⟨2939702706994810300795283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31356828874611309875149685 2939702706994810300795283)
          ·
            refine ⟨4409554060492215451192925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939702706994810300795283 4409554060492215451192925)
            ·
              refine ⟨1653582772684580794197347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4409554060492215451192925 1653582772684580794197347)
              ·
                refine ⟨2480374159026871191296021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653582772684580794197347 2480374159026871191296021)
                ·
                  refine ⟨116267538704384587092001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2480374159026871191296021 116267538704384587092001)
                  ·
                    rfl

theorem cell22_1018936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 6].length) (baseStart_1018936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018936 prefixEnd_1018936 := by exact prefixLift 1018936
  have htrace : WordTrace (prefixWord ++ tailWord_1018936) baseStart_1018936 baseEnd_1018936 := by
    simpa [prefixWord, tailWord_1018936, baseEnd_1018936] using wordTrace_append hprefix tailTrace_1018936
  have hstable : (prefixWord ++ tailWord_1018936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018936).length < 2 ^ (prefixWord ++ tailWord_1018936).sum := by decide
  have hdescent : baseEnd_1018936 < baseStart_1018936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1018949 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1018949 : Nat := 118140960795 + 1018949 * 2 ^ 59
def prefixEnd_1018949 : Nat := 4983230072969 + 3 ^ 40 * 1018949 * 2
def baseEnd_1018949 : Nat := 348807066278826060700963

theorem tailTrace_1018949 : CollatzResearch.WordTrace tailWord_1018949 prefixEnd_1018949 348807066278826060700963 := by
  unfold tailWord_1018949
  simp only [CollatzResearch.WordTrace]
  refine ⟨37164123185529270479659901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24776082123686180319773267 37164123185529270479659901)
  ·
    refine ⟨13936546194573476429872463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37164123185529270479659901 13936546194573476429872463)
    ·
      refine ⟨20904819291860214644808695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13936546194573476429872463 20904819291860214644808695)
      ·
        refine ⟨31357228937790321967213043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20904819291860214644808695 31357228937790321967213043)
        ·
          refine ⟨47035843406685482950819565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31357228937790321967213043 47035843406685482950819565)
          ·
            refine ⟨17638441277507056106557337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47035843406685482950819565 17638441277507056106557337)
            ·
              refine ⟨13228830958130292079918003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17638441277507056106557337 13228830958130292079918003)
              ·
                refine ⟨19843246437195438119877005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228830958130292079918003 19843246437195438119877005)
                ·
                  refine ⟨7441217413948289294953877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19843246437195438119877005 7441217413948289294953877)
                  ·
                    refine ⟨348807066278826060700963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7441217413948289294953877 348807066278826060700963)
                    ·
                      rfl

theorem cell22_1018949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1018949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1018949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1018949 prefixEnd_1018949 := by exact prefixLift 1018949
  have htrace : WordTrace (prefixWord ++ tailWord_1018949) baseStart_1018949 baseEnd_1018949 := by
    simpa [prefixWord, tailWord_1018949, baseEnd_1018949] using wordTrace_append hprefix tailTrace_1018949
  have hstable : (prefixWord ++ tailWord_1018949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1018949).length < 2 ^ (prefixWord ++ tailWord_1018949).sum := by decide
  have hdescent : baseEnd_1018949 < baseStart_1018949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1018949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019041 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1019041 : Nat := 118140960795 + 1019041 * 2 ^ 59
def prefixEnd_1019041 : Nat := 4983230072969 + 3 ^ 40 * 1019041 * 2
def baseEnd_1019041 : Nat := 348838559758968487400681

theorem tailTrace_1019041 : CollatzResearch.WordTrace tailWord_1019041 prefixEnd_1019041 348838559758968487400681 := by
  unfold tailWord_1019041
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167478701195970192008977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24778319134130646794672651 37167478701195970192008977)
  ·
    refine ⟨27875609025896977644006733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37167478701195970192008977 27875609025896977644006733)
    ·
      refine ⟨10453353384711366616502525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27875609025896977644006733 10453353384711366616502525)
      ·
        refine ⟨3920007519266762481188447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10453353384711366616502525 3920007519266762481188447)
        ·
          refine ⟨5880011278900143721782671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920007519266762481188447 5880011278900143721782671)
          ·
            refine ⟨8820016918350215582674007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880011278900143721782671 8820016918350215582674007)
            ·
              refine ⟨13230025377525323374011011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820016918350215582674007 13230025377525323374011011)
              ·
                refine ⟨19845038066287985061016517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230025377525323374011011 19845038066287985061016517)
                ·
                  refine ⟨3720944637428997198940597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19845038066287985061016517 3720944637428997198940597)
                  ·
                    refine ⟨348838559758968487400681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3720944637428997198940597 348838559758968487400681)
                    ·
                      rfl

theorem cell22_1019041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1019041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019041 prefixEnd_1019041 := by exact prefixLift 1019041
  have htrace : WordTrace (prefixWord ++ tailWord_1019041) baseStart_1019041 baseEnd_1019041 := by
    simpa [prefixWord, tailWord_1019041, baseEnd_1019041] using wordTrace_append hprefix tailTrace_1019041
  have hstable : (prefixWord ++ tailWord_1019041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019041).length < 2 ^ (prefixWord ++ tailWord_1019041).sum := by decide
  have hdescent : baseEnd_1019041 < baseStart_1019041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019047 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1019047 : Nat := 118140960795 + 1019047 * 2 ^ 59
def prefixEnd_1019047 : Nat := 4983230072969 + 3 ^ 40 * 1019047 * 2
def baseEnd_1019047 : Nat := 348840613681586471750663

theorem tailTrace_1019047 : CollatzResearch.WordTrace tailWord_1019047 prefixEnd_1019047 348840613681586471750663 := by
  unfold tailWord_1019047
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167697539174233216727395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24778465026116155477818263 37167697539174233216727395)
  ·
    refine ⟨55751546308761349825091093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37167697539174233216727395 55751546308761349825091093)
    ·
      refine ⟨2613353733223188273051145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55751546308761349825091093 2613353733223188273051145)
      ·
        refine ⟨1960015299917391204788359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2613353733223188273051145 1960015299917391204788359)
        ·
          refine ⟨2940022949876086807182539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960015299917391204788359 2940022949876086807182539)
          ·
            refine ⟨4410034424814130210773809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940022949876086807182539 4410034424814130210773809)
            ·
              refine ⟨3307525818610597658080357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410034424814130210773809 3307525818610597658080357)
              ·
                refine ⟨620161090989487060890067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3307525818610597658080357 620161090989487060890067)
                ·
                  refine ⟨930241636484230591335101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 620161090989487060890067 930241636484230591335101)
                  ·
                    refine ⟨348840613681586471750663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 930241636484230591335101 348840613681586471750663)
                    ·
                      rfl

theorem cell22_1019047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1019047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019047 prefixEnd_1019047 := by exact prefixLift 1019047
  have htrace : WordTrace (prefixWord ++ tailWord_1019047) baseStart_1019047 baseEnd_1019047 := by
    simpa [prefixWord, tailWord_1019047, baseEnd_1019047] using wordTrace_append hprefix tailTrace_1019047
  have hstable : (prefixWord ++ tailWord_1019047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019047).length < 2 ^ (prefixWord ++ tailWord_1019047).sum := by decide
  have hdescent : baseEnd_1019047 < baseStart_1019047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019071 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 6]
def baseStart_1019071 : Nat := 118140960795 + 1019071 * 2 ^ 59
def prefixEnd_1019071 : Nat := 4983230072969 + 3 ^ 40 * 1019071 * 2
def baseEnd_1019071 : Nat := 116282943124019469716863

theorem tailTrace_1019071 : CollatzResearch.WordTrace tailWord_1019071 prefixEnd_1019071 116282943124019469716863 := by
  unfold tailWord_1019071
  simp only [CollatzResearch.WordTrace]
  refine ⟨37168572891087285315601067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24779048594058190210400711 37168572891087285315601067)
  ·
    refine ⟨55752859336630927973401601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37168572891087285315601067 55752859336630927973401601)
    ·
      refine ⟨41814644502473195980051201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55752859336630927973401601 41814644502473195980051201)
      ·
        refine ⟨31360983376854896985038401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41814644502473195980051201 31360983376854896985038401)
        ·
          refine ⟨23520737532641172738778801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31360983376854896985038401 23520737532641172738778801)
          ·
            refine ⟨17640553149480879554084101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23520737532641172738778801 17640553149480879554084101)
            ·
              refine ⟨3307603715527664916390769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17640553149480879554084101 3307603715527664916390769)
              ·
                refine ⟨2480702786645748687293077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307603715527664916390769 2480702786645748687293077)
                ·
                  refine ⟨116282943124019469716863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2480702786645748687293077 116282943124019469716863)
                  ·
                    rfl

theorem cell22_1019071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 6].length) (baseStart_1019071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019071 prefixEnd_1019071 := by exact prefixLift 1019071
  have htrace : WordTrace (prefixWord ++ tailWord_1019071) baseStart_1019071 baseEnd_1019071 := by
    simpa [prefixWord, tailWord_1019071, baseEnd_1019071] using wordTrace_append hprefix tailTrace_1019071
  have hstable : (prefixWord ++ tailWord_1019071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019071).length < 2 ^ (prefixWord ++ tailWord_1019071).sum := by decide
  have hdescent : baseEnd_1019071 < baseStart_1019071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019103 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 4, 3]
def baseStart_1019103 : Nat := 118140960795 + 1019103 * 2 ^ 59
def prefixEnd_1019103 : Nat := 4983230072969 + 3 ^ 40 * 1019103 * 2
def baseEnd_1019103 : Nat := 348859783626020992350491

theorem tailTrace_1019103 : CollatzResearch.WordTrace tailWord_1019103 prefixEnd_1019103 348859783626020992350491 := by
  unfold tailWord_1019103
  simp only [CollatzResearch.WordTrace]
  refine ⟨37169740026971354780765963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24779826684647569853843975 37169740026971354780765963)
  ·
    refine ⟨55754610040457032171148945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37169740026971354780765963 55754610040457032171148945)
    ·
      refine ⟨41815957530342774128361709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55754610040457032171148945 41815957530342774128361709)
      ·
        refine ⟨15680984073878540298135641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41815957530342774128361709 15680984073878540298135641)
        ·
          refine ⟨11760738055408905223601731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15680984073878540298135641 11760738055408905223601731)
          ·
            refine ⟨17641107083113357835402597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11760738055408905223601731 17641107083113357835402597)
            ·
              refine ⟨3307707578083754594137987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17641107083113357835402597 3307707578083754594137987)
              ·
                refine ⟨4961561367125631891206981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307707578083754594137987 4961561367125631891206981)
                ·
                  refine ⟨930292756336055979601309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4961561367125631891206981 930292756336055979601309)
                  ·
                    refine ⟨348859783626020992350491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 930292756336055979601309 348859783626020992350491)
                    ·
                      rfl

theorem cell22_1019103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_1019103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019103 prefixEnd_1019103 := by exact prefixLift 1019103
  have htrace : WordTrace (prefixWord ++ tailWord_1019103) baseStart_1019103 baseEnd_1019103 := by
    simpa [prefixWord, tailWord_1019103, baseEnd_1019103] using wordTrace_append hprefix tailTrace_1019103
  have hstable : (prefixWord ++ tailWord_1019103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019103).length < 2 ^ (prefixWord ++ tailWord_1019103).sum := by decide
  have hdescent : baseEnd_1019103 < baseStart_1019103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019116 : List Nat := [2, 2, 1, 1, 2, 4, 1, 9]
def baseStart_1019116 : Nat := 118140960795 + 1019116 * 2 ^ 59
def prefixEnd_1019116 : Nat := 4983230072969 + 3 ^ 40 * 1019116 * 2
def baseEnd_1019116 : Nat := 38762692643521476863939

theorem tailTrace_1019116 : CollatzResearch.WordTrace tailWord_1019116 prefixEnd_1019116 38762692643521476863939 := by
  unfold tailWord_1019116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585107087962129000494601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24780142783949505333992801 18585107087962129000494601)
  ·
    refine ⟨13938830315971596750370951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18585107087962129000494601 13938830315971596750370951)
    ·
      refine ⟨20908245473957395125556427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13938830315971596750370951 20908245473957395125556427)
      ·
        refine ⟨31362368210936092688334641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20908245473957395125556427 31362368210936092688334641)
        ·
          refine ⟨23521776158202069516250981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31362368210936092688334641 23521776158202069516250981)
          ·
            refine ⟨4410333029662888034297059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23521776158202069516250981 4410333029662888034297059)
            ·
              refine ⟨6615499544494332051445589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410333029662888034297059 6615499544494332051445589)
              ·
                refine ⟨38762692643521476863939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6615499544494332051445589 38762692643521476863939)
                ·
                  rfl

theorem cell22_1019116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 9].length) (baseStart_1019116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019116 prefixEnd_1019116 := by exact prefixLift 1019116
  have htrace : WordTrace (prefixWord ++ tailWord_1019116) baseStart_1019116 baseEnd_1019116 := by
    simpa [prefixWord, tailWord_1019116, baseEnd_1019116] using wordTrace_append hprefix tailTrace_1019116
  have hstable : (prefixWord ++ tailWord_1019116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019116).length < 2 ^ (prefixWord ++ tailWord_1019116).sum := by decide
  have hdescent : baseEnd_1019116 < baseStart_1019116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019124 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1019124 : Nat := 118140960795 + 1019124 * 2 ^ 59
def prefixEnd_1019124 : Nat := 4983230072969 + 3 ^ 40 * 1019124 * 2
def baseEnd_1019124 : Nat := 348866972355183937575427

theorem tailTrace_1019124 : CollatzResearch.WordTrace tailWord_1019124 prefixEnd_1019124 348866972355183937575427 := by
  unfold tailWord_1019124
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585252979947637683640213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24780337306596850244853617 18585252979947637683640213)
  ·
    refine ⟨871183733435045516420635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18585252979947637683640213 871183733435045516420635)
    ·
      refine ⟨1306775600152568274630953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871183733435045516420635 1306775600152568274630953)
      ·
        refine ⟨980081700114426205973215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306775600152568274630953 980081700114426205973215)
        ·
          refine ⟨1470122550171639308959823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980081700114426205973215 1470122550171639308959823)
          ·
            refine ⟨2205183825257458963439735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470122550171639308959823 2205183825257458963439735)
            ·
              refine ⟨3307775737886188445159603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205183825257458963439735 3307775737886188445159603)
              ·
                refine ⟨4961663606829282667739405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307775737886188445159603 4961663606829282667739405)
                ·
                  refine ⟨1860623852560981000402277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4961663606829282667739405 1860623852560981000402277)
                  ·
                    refine ⟨348866972355183937575427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860623852560981000402277 348866972355183937575427)
                    ·
                      rfl

theorem cell22_1019124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1019124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019124 prefixEnd_1019124 := by exact prefixLift 1019124
  have htrace : WordTrace (prefixWord ++ tailWord_1019124) baseStart_1019124 baseEnd_1019124 := by
    simpa [prefixWord, tailWord_1019124, baseEnd_1019124] using wordTrace_append hprefix tailTrace_1019124
  have hstable : (prefixWord ++ tailWord_1019124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019124).length < 2 ^ (prefixWord ++ tailWord_1019124).sum := by decide
  have hdescent : baseEnd_1019124 < baseStart_1019124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019223 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 6]
def baseStart_1019223 : Nat := 118140960795 + 1019223 * 2 ^ 59
def prefixEnd_1019223 : Nat := 4983230072969 + 3 ^ 40 * 1019223 * 2
def baseEnd_1019223 : Nat := 116300287359460226450041

theorem tailTrace_1019223 : CollatzResearch.WordTrace tailWord_1019223 prefixEnd_1019223 116300287359460226450041 := by
  unfold tailWord_1019223
  simp only [CollatzResearch.WordTrace]
  refine ⟨37174116786536615275134323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24782744524357743516756215 37174116786536615275134323)
  ·
    refine ⟨55761175179804922912701485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37174116786536615275134323 55761175179804922912701485)
    ·
      refine ⟨20910440692426846092263057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55761175179804922912701485 20910440692426846092263057)
      ·
        refine ⟨15682830519320134569197293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20910440692426846092263057 15682830519320134569197293)
        ·
          refine ⟨5881061444745050463448985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15682830519320134569197293 5881061444745050463448985)
          ·
            refine ⟨4410796083558787847586739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5881061444745050463448985 4410796083558787847586739)
            ·
              refine ⟨6616194125338181771380109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410796083558787847586739 6616194125338181771380109)
              ·
                refine ⟨2481072797001818164267541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6616194125338181771380109 2481072797001818164267541)
                ·
                  refine ⟨116300287359460226450041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2481072797001818164267541 116300287359460226450041)
                  ·
                    rfl

theorem cell22_1019223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 6].length) (baseStart_1019223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019223 prefixEnd_1019223 := by exact prefixLift 1019223
  have htrace : WordTrace (prefixWord ++ tailWord_1019223) baseStart_1019223 baseEnd_1019223 := by
    simpa [prefixWord, tailWord_1019223, baseEnd_1019223] using wordTrace_append hprefix tailTrace_1019223
  have hstable : (prefixWord ++ tailWord_1019223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019223).length < 2 ^ (prefixWord ++ tailWord_1019223).sum := by decide
  have hdescent : baseEnd_1019223 < baseStart_1019223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019268 : List Nat := [2, 3, 2, 1, 1, 3, 10]
def baseStart_1019268 : Nat := 118140960795 + 1019268 * 2 ^ 59
def prefixEnd_1019268 : Nat := 4983230072969 + 3 ^ 40 * 1019268 * 2
def baseEnd_1019268 : Nat := 12922824685111687480555

theorem tailTrace_1019268 : CollatzResearch.WordTrace tailWord_1019268 prefixEnd_1019268 12922824685111687480555 := by
  unfold tailWord_1019268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587879035686793980261229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24783838714249058640348305 18587879035686793980261229)
  ·
    refine ⟨6970454638382547742597961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18587879035686793980261229 6970454638382547742597961)
    ·
      refine ⟨5227840978786910806948471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6970454638382547742597961 5227840978786910806948471)
      ·
        refine ⟨7841761468180366210422707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227840978786910806948471 7841761468180366210422707)
        ·
          refine ⟨11762642202270549315634061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841761468180366210422707 11762642202270549315634061)
          ·
            refine ⟨4410990825851455993362773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11762642202270549315634061 4410990825851455993362773)
            ·
              refine ⟨12922824685111687480555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4410990825851455993362773 12922824685111687480555)
              ·
                rfl

theorem cell22_1019268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 10].length) (baseStart_1019268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019268 prefixEnd_1019268 := by exact prefixLift 1019268
  have htrace : WordTrace (prefixWord ++ tailWord_1019268) baseStart_1019268 baseEnd_1019268 := by
    simpa [prefixWord, tailWord_1019268, baseEnd_1019268] using wordTrace_append hprefix tailTrace_1019268
  have hstable : (prefixWord ++ tailWord_1019268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019268).length < 2 ^ (prefixWord ++ tailWord_1019268).sum := by decide
  have hdescent : baseEnd_1019268 < baseStart_1019268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019289 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 2, 3]
def baseStart_1019289 : Nat := 118140960795 + 1019289 * 2 ^ 59
def prefixEnd_1019289 : Nat := 4983230072969 + 3 ^ 40 * 1019289 * 2
def baseEnd_1019289 : Nat := 348923455227178507199921

theorem tailTrace_1019289 : CollatzResearch.WordTrace tailWord_1019289 prefixEnd_1019289 348923455227178507199921 := by
  unfold tailWord_1019289
  simp only [CollatzResearch.WordTrace]
  refine ⟨37176524004297508547036921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24784349336198339031357947 37176524004297508547036921)
  ·
    refine ⟨27882393003223131410277691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37176524004297508547036921 27882393003223131410277691)
    ·
      refine ⟨41823589504834697115416537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27882393003223131410277691 41823589504834697115416537)
      ·
        refine ⟨31367692128626022836562403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41823589504834697115416537 31367692128626022836562403)
        ·
          refine ⟨47051538192939034254843605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31367692128626022836562403 47051538192939034254843605)
          ·
            refine ⟨1102770426397008615347897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 47051538192939034254843605 1102770426397008615347897)
            ·
              refine ⟨827077819797756461510923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102770426397008615347897 827077819797756461510923)
              ·
                refine ⟨1240616729696634692266385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827077819797756461510923 1240616729696634692266385)
                ·
                  refine ⟨930462547272476019199789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1240616729696634692266385 930462547272476019199789)
                  ·
                    refine ⟨348923455227178507199921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 930462547272476019199789 348923455227178507199921)
                    ·
                      rfl

theorem cell22_1019289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_1019289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019289 prefixEnd_1019289 := by exact prefixLift 1019289
  have htrace : WordTrace (prefixWord ++ tailWord_1019289) baseStart_1019289 baseEnd_1019289 := by
    simpa [prefixWord, tailWord_1019289, baseEnd_1019289] using wordTrace_append hprefix tailTrace_1019289
  have hstable : (prefixWord ++ tailWord_1019289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019289).length < 2 ^ (prefixWord ++ tailWord_1019289).sum := by decide
  have hdescent : baseEnd_1019289 < baseStart_1019289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019300 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_1019300 : Nat := 118140960795 + 1019300 * 2 ^ 59
def prefixEnd_1019300 : Nat := 4983230072969 + 3 ^ 40 * 1019300 * 2
def baseEnd_1019300 : Nat := 348927220751978145174887

theorem tailTrace_1019300 : CollatzResearch.WordTrace tailWord_1019300 prefixEnd_1019300 348927220751978145174887 := by
  unfold tailWord_1019300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588462603628828712843677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24784616804838438283791569 18588462603628828712843677)
  ·
    refine ⟨6970673476360810767316379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18588462603628828712843677 6970673476360810767316379)
    ·
      refine ⟨10456010214541216150974569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970673476360810767316379 10456010214541216150974569)
      ·
        refine ⟨7842007660905912113230927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10456010214541216150974569 7842007660905912113230927)
        ·
          refine ⟨11763011491358868169846391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842007660905912113230927 11763011491358868169846391)
          ·
            refine ⟨17644517237038302254769587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763011491358868169846391 17644517237038302254769587)
            ·
              refine ⟨26466775855557453382154381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644517237038302254769587 26466775855557453382154381)
              ·
                refine ⟨9925040945834045018307893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26466775855557453382154381 9925040945834045018307893)
                ·
                  refine ⟨930472588671941720466365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9925040945834045018307893 930472588671941720466365)
                  ·
                    refine ⟨348927220751978145174887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 930472588671941720466365 348927220751978145174887)
                    ·
                      rfl

theorem cell22_1019300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_1019300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019300 prefixEnd_1019300 := by exact prefixLift 1019300
  have htrace : WordTrace (prefixWord ++ tailWord_1019300) baseStart_1019300 baseEnd_1019300 := by
    simpa [prefixWord, tailWord_1019300, baseEnd_1019300] using wordTrace_append hprefix tailTrace_1019300
  have hstable : (prefixWord ++ tailWord_1019300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019300).length < 2 ^ (prefixWord ++ tailWord_1019300).sum := by decide
  have hdescent : baseEnd_1019300 < baseStart_1019300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019304 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1019304 : Nat := 118140960795 + 1019304 * 2 ^ 59
def prefixEnd_1019304 : Nat := 4983230072969 + 3 ^ 40 * 1019304 * 2
def baseEnd_1019304 : Nat := 348928590033723468074875

theorem tailTrace_1019304 : CollatzResearch.WordTrace tailWord_1019304 prefixEnd_1019304 348928590033723468074875 := by
  unfold tailWord_1019304
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588535549621583054416483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24784714066162110739221977 18588535549621583054416483)
  ·
    refine ⟨27882803324432374581624725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18588535549621583054416483 27882803324432374581624725)
    ·
      refine ⟨1307006405832767558513659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27882803324432374581624725 1307006405832767558513659)
      ·
        refine ⟨1960509608749151337770489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307006405832767558513659 1960509608749151337770489)
        ·
          refine ⟨1470382206561863503327867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960509608749151337770489 1470382206561863503327867)
          ·
            refine ⟨2205573309842795254991801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470382206561863503327867 2205573309842795254991801)
            ·
              refine ⟨1654179982382096441243851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205573309842795254991801 1654179982382096441243851)
              ·
                refine ⟨2481269973573144661865777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654179982382096441243851 2481269973573144661865777)
                ·
                  refine ⟨1860952480179858496399333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2481269973573144661865777 1860952480179858496399333)
                  ·
                    refine ⟨348928590033723468074875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860952480179858496399333 348928590033723468074875)
                    ·
                      rfl

theorem cell22_1019304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1019304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019304 prefixEnd_1019304 := by exact prefixLift 1019304
  have htrace : WordTrace (prefixWord ++ tailWord_1019304) baseStart_1019304 baseEnd_1019304 := by
    simpa [prefixWord, tailWord_1019304, baseEnd_1019304] using wordTrace_append hprefix tailTrace_1019304
  have hstable : (prefixWord ++ tailWord_1019304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019304).length < 2 ^ (prefixWord ++ tailWord_1019304).sum := by decide
  have hdescent : baseEnd_1019304 < baseStart_1019304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019377 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_1019377 : Nat := 118140960795 + 1019377 * 2 ^ 59
def prefixEnd_1019377 : Nat := 4983230072969 + 3 ^ 40 * 1019377 * 2
def baseEnd_1019377 : Nat := 348953579425575610999651

theorem tailTrace_1019377 : CollatzResearch.WordTrace tailWord_1019377 prefixEnd_1019377 348953579425575610999651 := by
  unfold tailWord_1019377
  simp only [CollatzResearch.WordTrace]
  refine ⟨37179733627978699576240385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24786489085319133050826923 37179733627978699576240385)
  ·
    refine ⟨27884800220984024682180289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37179733627978699576240385 27884800220984024682180289)
    ·
      refine ⟨20913600165738018511635217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27884800220984024682180289 20913600165738018511635217)
      ·
        refine ⟨15685200124303513883726413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20913600165738018511635217 15685200124303513883726413)
        ·
          refine ⟨5881950046613817706397405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15685200124303513883726413 5881950046613817706397405)
          ·
            refine ⟨2205731267480181639899027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5881950046613817706397405 2205731267480181639899027)
            ·
              refine ⟨3308596901220272459848541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205731267480181639899027 3308596901220272459848541)
              ·
                refine ⟨1240723837957602172443203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3308596901220272459848541 1240723837957602172443203)
                ·
                  refine ⟨1861085756936403258664805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240723837957602172443203 1861085756936403258664805)
                  ·
                    refine ⟨348953579425575610999651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1861085756936403258664805 348953579425575610999651)
                    ·
                      rfl

theorem cell22_1019377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_1019377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019377 prefixEnd_1019377 := by exact prefixLift 1019377
  have htrace : WordTrace (prefixWord ++ tailWord_1019377) baseStart_1019377 baseEnd_1019377 := by
    simpa [prefixWord, tailWord_1019377, baseEnd_1019377] using wordTrace_append hprefix tailTrace_1019377
  have hstable : (prefixWord ++ tailWord_1019377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019377).length < 2 ^ (prefixWord ++ tailWord_1019377).sum := by decide
  have hdescent : baseEnd_1019377 < baseStart_1019377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019420 : List Nat := [2, 2, 3, 1, 2, 1, 3, 8]
def baseStart_1019420 : Nat := 118140960795 + 1019420 * 2 ^ 59
def prefixEnd_1019420 : Nat := 4983230072969 + 3 ^ 40 * 1019420 * 2
def baseEnd_1019420 : Nat := 38774255467148648019391

theorem tailTrace_1019420 : CollatzResearch.WordTrace tailWord_1019420 prefixEnd_1019420 38774255467148648019391 := by
  unfold tailWord_1019420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18590650983411458960027857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24787534644548611946703809 18590650983411458960027857)
  ·
    refine ⟨13942988237558594220020893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18590650983411458960027857 13942988237558594220020893)
    ·
      refine ⟨5228620589084472832507835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13942988237558594220020893 5228620589084472832507835)
      ·
        refine ⟨7842930883626709248761753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228620589084472832507835 7842930883626709248761753)
        ·
          refine ⟨5882198162720031936571315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842930883626709248761753 5882198162720031936571315)
          ·
            refine ⟨8823297244080047904856973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882198162720031936571315 8823297244080047904856973)
            ·
              refine ⟨3308736466530017964321365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8823297244080047904856973 3308736466530017964321365)
              ·
                refine ⟨38774255467148648019391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3308736466530017964321365 38774255467148648019391)
                ·
                  rfl

theorem cell22_1019420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_1019420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019420 prefixEnd_1019420 := by exact prefixLift 1019420
  have htrace : WordTrace (prefixWord ++ tailWord_1019420) baseStart_1019420 baseEnd_1019420 := by
    simpa [prefixWord, tailWord_1019420, baseEnd_1019420] using wordTrace_append hprefix tailTrace_1019420
  have hstable : (prefixWord ++ tailWord_1019420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019420).length < 2 ^ (prefixWord ++ tailWord_1019420).sum := by decide
  have hdescent : baseEnd_1019420 < baseStart_1019420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019450 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_1019450 : Nat := 118140960795 + 1019450 * 2 ^ 59
def prefixEnd_1019450 : Nat := 4983230072969 + 3 ^ 40 * 1019450 * 2
def baseEnd_1019450 : Nat := 348978568817427753924427

theorem tailTrace_1019450 : CollatzResearch.WordTrace tailWord_1019450 prefixEnd_1019450 348978568817427753924427 := by
  unfold tailWord_1019450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295599039178558260911951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24788264104476155362431869 9295599039178558260911951)
  ·
    refine ⟨13943398558767837391367927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9295599039178558260911951 13943398558767837391367927)
    ·
      refine ⟨20915097838151756087051891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13943398558767837391367927 20915097838151756087051891)
      ·
        refine ⟨31372646757227634130577837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20915097838151756087051891 31372646757227634130577837)
        ·
          refine ⟨11764742533960362798966689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31372646757227634130577837 11764742533960362798966689)
          ·
            refine ⟨8823556900470272099225017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11764742533960362798966689 8823556900470272099225017)
            ·
              refine ⟨6617667675352704074418763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8823556900470272099225017 6617667675352704074418763)
              ·
                refine ⟨9926501513029056111628145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617667675352704074418763 9926501513029056111628145)
                ·
                  refine ⟨7444876134771792083721109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9926501513029056111628145 7444876134771792083721109)
                  ·
                    refine ⟨348978568817427753924427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7444876134771792083721109 348978568817427753924427)
                    ·
                      rfl

theorem cell22_1019450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_1019450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019450 prefixEnd_1019450 := by exact prefixLift 1019450
  have htrace : WordTrace (prefixWord ++ tailWord_1019450) baseStart_1019450 baseEnd_1019450 := by
    simpa [prefixWord, tailWord_1019450, baseEnd_1019450] using wordTrace_append hprefix tailTrace_1019450
  have hstable : (prefixWord ++ tailWord_1019450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019450).length < 2 ^ (prefixWord ++ tailWord_1019450).sum := by decide
  have hdescent : baseEnd_1019450 < baseStart_1019450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019480 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1019480 : Nat := 118140960795 + 1019480 * 2 ^ 59
def prefixEnd_1019480 : Nat := 4983230072969 + 3 ^ 40 * 1019480 * 2
def baseEnd_1019480 : Nat := 348988838430517675674335

theorem tailTrace_1019480 : CollatzResearch.WordTrace tailWord_1019480 prefixEnd_1019480 348988838430517675674335 := by
  unfold tailWord_1019480
  simp only [CollatzResearch.WordTrace]
  refine ⟨18591745173302774083619947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24788993564403698778159929 18591745173302774083619947)
  ·
    refine ⟨27887617759954161125429921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18591745173302774083619947 27887617759954161125429921)
    ·
      refine ⟨20915713319965620844072441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27887617759954161125429921 20915713319965620844072441)
      ·
        refine ⟨15686784989974215633054331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20915713319965620844072441 15686784989974215633054331)
        ·
          refine ⟨23530177484961323449581497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15686784989974215633054331 23530177484961323449581497)
          ·
            refine ⟨17647633113720992587186123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23530177484961323449581497 17647633113720992587186123)
            ·
              refine ⟨26471449670581488880779185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17647633113720992587186123 26471449670581488880779185)
              ·
                refine ⟨19853587252936116660584389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26471449670581488880779185 19853587252936116660584389)
                ·
                  refine ⟨3722547609925521873859573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19853587252936116660584389 3722547609925521873859573)
                  ·
                    refine ⟨348988838430517675674335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3722547609925521873859573 348988838430517675674335)
                    ·
                      rfl

theorem cell22_1019480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1019480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019480 prefixEnd_1019480 := by exact prefixLift 1019480
  have htrace : WordTrace (prefixWord ++ tailWord_1019480) baseStart_1019480 baseEnd_1019480 := by
    simpa [prefixWord, tailWord_1019480, baseEnd_1019480] using wordTrace_append hprefix tailTrace_1019480
  have hstable : (prefixWord ++ tailWord_1019480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019480).length < 2 ^ (prefixWord ++ tailWord_1019480).sum := by decide
  have hdescent : baseEnd_1019480 < baseStart_1019480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019527 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 6]
def baseStart_1019527 : Nat := 118140960795 + 1019527 * 2 ^ 59
def prefixEnd_1019527 : Nat := 4983230072969 + 3 ^ 40 * 1019527 * 2
def baseEnd_1019527 : Nat := 116334975830341739916397

theorem tailTrace_1019527 : CollatzResearch.WordTrace tailWord_1019527 prefixEnd_1019527 116334975830341739916397 := by
  unfold tailWord_1019527
  simp only [CollatzResearch.WordTrace]
  refine ⟨37185204577435275194200835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24790136384956850129467223 37185204577435275194200835)
  ·
    refine ⟨55777806866152912791301253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37185204577435275194200835 55777806866152912791301253)
    ·
      refine ⟨10458338787403671148368985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55777806866152912791301253 10458338787403671148368985)
      ·
        refine ⟨7843754090552753361276739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10458338787403671148368985 7843754090552753361276739)
        ·
          refine ⟨11765631135829130041915109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7843754090552753361276739 11765631135829130041915109)
          ·
            refine ⟨2206055837967961882859083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11765631135829130041915109 2206055837967961882859083)
            ·
              refine ⟨3309083756951942824288625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206055837967961882859083 3309083756951942824288625)
              ·
                refine ⟨2481812817713957118216469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309083756951942824288625 2481812817713957118216469)
                ·
                  refine ⟨116334975830341739916397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2481812817713957118216469 116334975830341739916397)
                  ·
                    rfl

theorem cell22_1019527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 6].length) (baseStart_1019527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019527 prefixEnd_1019527 := by exact prefixLift 1019527
  have htrace : WordTrace (prefixWord ++ tailWord_1019527) baseStart_1019527 baseEnd_1019527 := by
    simpa [prefixWord, tailWord_1019527, baseEnd_1019527] using wordTrace_append hprefix tailTrace_1019527
  have hstable : (prefixWord ++ tailWord_1019527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019527).length < 2 ^ (prefixWord ++ tailWord_1019527).sum := by decide
  have hdescent : baseEnd_1019527 < baseStart_1019527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019544 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 4]
def baseStart_1019544 : Nat := 118140960795 + 1019544 * 2 ^ 59
def prefixEnd_1019544 : Nat := 4983230072969 + 3 ^ 40 * 1019544 * 2
def baseEnd_1019544 : Nat := 116336915646147614024713

theorem tailTrace_1019544 : CollatzResearch.WordTrace tailWord_1019544 prefixEnd_1019544 116336915646147614024713 := by
  unfold tailWord_1019544
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592912309186843548784843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24790549745582458065046457 18592912309186843548784843)
  ·
    refine ⟨27889368463780265323177265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18592912309186843548784843 27889368463780265323177265)
    ·
      refine ⟨20917026347835198992382949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27889368463780265323177265 20917026347835198992382949)
      ·
        refine ⟨3921942440219099811071803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20917026347835198992382949 3921942440219099811071803)
        ·
          refine ⟨5882913660328649716607705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921942440219099811071803 5882913660328649716607705)
          ·
            refine ⟨4412185245246487287455779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882913660328649716607705 4412185245246487287455779)
            ·
              refine ⟨6618277867869730931183669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412185245246487287455779 6618277867869730931183669)
              ·
                refine ⟨620463550112787274798469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6618277867869730931183669 620463550112787274798469)
                ·
                  refine ⟨116336915646147614024713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620463550112787274798469 116336915646147614024713)
                  ·
                    rfl

theorem cell22_1019544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_1019544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019544 prefixEnd_1019544 := by exact prefixLift 1019544
  have htrace : WordTrace (prefixWord ++ tailWord_1019544) baseStart_1019544 baseEnd_1019544 := by
    simpa [prefixWord, tailWord_1019544, baseEnd_1019544] using wordTrace_append hprefix tailTrace_1019544
  have hstable : (prefixWord ++ tailWord_1019544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019544).length < 2 ^ (prefixWord ++ tailWord_1019544).sum := by decide
  have hdescent : baseEnd_1019544 < baseStart_1019544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019555 : List Nat := [1, 1, 1, 4, 1, 1, 13]
def baseStart_1019555 : Nat := 118140960795 + 1019555 * 2 ^ 59
def prefixEnd_1019555 : Nat := 4983230072969 + 3 ^ 40 * 1019555 * 2
def baseEnd_1019555 : Nat := 12926463424564536298115

theorem tailTrace_1019555 : CollatzResearch.WordTrace tailWord_1019555 prefixEnd_1019555 12926463424564536298115 := by
  unfold tailWord_1019555
  simp only [CollatzResearch.WordTrace]
  refine ⟨37186225821333835976220119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24790817214222557317480079 37186225821333835976220119)
  ·
    refine ⟨55779338732000753964330179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37186225821333835976220119 55779338732000753964330179)
    ·
      refine ⟨83669008098001130946495269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55779338732000753964330179 83669008098001130946495269)
      ·
        refine ⟨15687939018375212052467863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83669008098001130946495269 15687939018375212052467863)
        ·
          refine ⟨23531908527562818078701795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15687939018375212052467863 23531908527562818078701795)
          ·
            refine ⟨35297862791344227118052693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23531908527562818078701795 35297862791344227118052693)
            ·
              refine ⟨12926463424564536298115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 35297862791344227118052693 12926463424564536298115)
              ·
                rfl

theorem cell22_1019555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 13].length) (baseStart_1019555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019555 prefixEnd_1019555 := by exact prefixLift 1019555
  have htrace : WordTrace (prefixWord ++ tailWord_1019555) baseStart_1019555 baseEnd_1019555 := by
    simpa [prefixWord, tailWord_1019555, baseEnd_1019555] using wordTrace_append hprefix tailTrace_1019555
  have hstable : (prefixWord ++ tailWord_1019555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019555).length < 2 ^ (prefixWord ++ tailWord_1019555).sum := by decide
  have hdescent : baseEnd_1019555 < baseStart_1019555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019557 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1019557 : Nat := 118140960795 + 1019557 * 2 ^ 59
def prefixEnd_1019557 : Nat := 4983230072969 + 3 ^ 40 * 1019557 * 2
def baseEnd_1019557 : Nat := 349015197104115141499099

theorem tailTrace_1019557 : CollatzResearch.WordTrace tailWord_1019557 prefixEnd_1019557 349015197104115141499099 := by
  unfold tailWord_1019557
  simp only [CollatzResearch.WordTrace]
  refine ⟨37186298767326590317792925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24790865844884393545195283 37186298767326590317792925)
  ·
    refine ⟨13944862037747471369172347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37186298767326590317792925 13944862037747471369172347)
    ·
      refine ⟨20917293056621207053758521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13944862037747471369172347 20917293056621207053758521)
      ·
        refine ⟨15687969792465905290318891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20917293056621207053758521 15687969792465905290318891)
        ·
          refine ⟨23531954688698857935478337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15687969792465905290318891 23531954688698857935478337)
          ·
            refine ⟨17648966016524143451608753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23531954688698857935478337 17648966016524143451608753)
            ·
              refine ⟨13236724512393107588706565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17648966016524143451608753 13236724512393107588706565)
              ·
                refine ⟨2481885846073707672882481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13236724512393107588706565 2481885846073707672882481)
                ·
                  refine ⟨1861414384555280754661861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2481885846073707672882481 1861414384555280754661861)
                  ·
                    refine ⟨349015197104115141499099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1861414384555280754661861 349015197104115141499099)
                    ·
                      rfl

theorem cell22_1019557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1019557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019557 prefixEnd_1019557 := by exact prefixLift 1019557
  have htrace : WordTrace (prefixWord ++ tailWord_1019557) baseStart_1019557 baseEnd_1019557 := by
    simpa [prefixWord, tailWord_1019557, baseEnd_1019557] using wordTrace_append hprefix tailTrace_1019557
  have hstable : (prefixWord ++ tailWord_1019557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019557).length < 2 ^ (prefixWord ++ tailWord_1019557).sum := by decide
  have hdescent : baseEnd_1019557 < baseStart_1019557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019634 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_1019634 : Nat := 118140960795 + 1019634 * 2 ^ 59
def prefixEnd_1019634 : Nat := 4983230072969 + 3 ^ 40 * 1019634 * 2
def baseEnd_1019634 : Nat := 116347185259237535774621

theorem tailTrace_1019634 : CollatzResearch.WordTrace tailWord_1019634 prefixEnd_1019634 116347185259237535774621 := by
  unfold tailWord_1019634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9297276797011908117086489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24792738125365088312230637 9297276797011908117086489)
  ·
    refine ⟨6972957597758931087814867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9297276797011908117086489 6972957597758931087814867)
    ·
      refine ⟨10459436396638396631722301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6972957597758931087814867 10459436396638396631722301)
      ·
        refine ⟨3922288648739398736895863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10459436396638396631722301 3922288648739398736895863)
        ·
          refine ⟨5883432973109098105343795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3922288648739398736895863 5883432973109098105343795)
          ·
            refine ⟨8825149459663647158015693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883432973109098105343795 8825149459663647158015693)
            ·
              refine ⟨3309431047373867684255885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8825149459663647158015693 3309431047373867684255885)
              ·
                refine ⟨1241036642765200381595957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309431047373867684255885 1241036642765200381595957)
                ·
                  refine ⟨116347185259237535774621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1241036642765200381595957 116347185259237535774621)
                  ·
                    rfl

theorem cell22_1019634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_1019634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019634 prefixEnd_1019634 := by exact prefixLift 1019634
  have htrace : WordTrace (prefixWord ++ tailWord_1019634) baseStart_1019634 baseEnd_1019634 := by
    simpa [prefixWord, tailWord_1019634, baseEnd_1019634] using wordTrace_append hprefix tailTrace_1019634
  have hstable : (prefixWord ++ tailWord_1019634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019634).length < 2 ^ (prefixWord ++ tailWord_1019634).sum := by decide
  have hdescent : baseEnd_1019634 < baseStart_1019634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019724 : List Nat := [2, 2, 1, 3, 4, 1, 9]
def baseStart_1019724 : Nat := 118140960795 + 1019724 * 2 ^ 59
def prefixEnd_1019724 : Nat := 4983230072969 + 3 ^ 40 * 1019724 * 2
def baseEnd_1019724 : Nat := 12928606096925273058281

theorem tailTrace_1019724 : CollatzResearch.WordTrace tailWord_1019724 prefixEnd_1019724 12928606096925273058281 := by
  unfold tailWord_1019724
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596194878860788919561113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24794926505147718559414817 18596194878860788919561113)
  ·
    refine ⟨13947146159145591689670835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18596194878860788919561113 13947146159145591689670835)
    ·
      refine ⟨20920719238718387534506253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947146159145591689670835 20920719238718387534506253)
      ·
        refine ⟨7845269714519395325439845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20920719238718387534506253 7845269714519395325439845)
        ·
          refine ⟨1470988071472386623519971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7845269714519395325439845 1470988071472386623519971)
          ·
            refine ⟨2206482107208579935279957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470988071472386623519971 2206482107208579935279957)
            ·
              refine ⟨12928606096925273058281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2206482107208579935279957 12928606096925273058281)
              ·
                rfl

theorem cell22_1019724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 9].length) (baseStart_1019724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019724 prefixEnd_1019724 := by exact prefixLift 1019724
  have htrace : WordTrace (prefixWord ++ tailWord_1019724) baseStart_1019724 baseEnd_1019724 := by
    simpa [prefixWord, tailWord_1019724, baseEnd_1019724] using wordTrace_append hprefix tailTrace_1019724
  have hstable : (prefixWord ++ tailWord_1019724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019724).length < 2 ^ (prefixWord ++ tailWord_1019724).sum := by decide
  have hdescent : baseEnd_1019724 < baseStart_1019724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019756 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_1019756 : Nat := 118140960795 + 1019756 * 2 ^ 59
def prefixEnd_1019756 : Nat := 4983230072969 + 3 ^ 40 * 1019756 * 2
def baseEnd_1019756 : Nat := 349083318870944955773489

theorem tailTrace_1019756 : CollatzResearch.WordTrace tailWord_1019756 prefixEnd_1019756 349083318870944955773489 := by
  unfold tailWord_1019756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596778446802823652143561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24795704595737098202858081 18596778446802823652143561)
  ·
    refine ⟨13947583835102117739107671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18596778446802823652143561 13947583835102117739107671)
    ·
      refine ⟨20921375752653176608661507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947583835102117739107671 20921375752653176608661507)
      ·
        refine ⟨31382063628979764912992261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20921375752653176608661507 31382063628979764912992261)
        ·
          refine ⟨5884136930433705921186049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31382063628979764912992261 5884136930433705921186049)
          ·
            refine ⟨4413102697825279440889537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5884136930433705921186049 4413102697825279440889537)
            ·
              refine ⟨3309827023368959580667153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4413102697825279440889537 3309827023368959580667153)
              ·
                refine ⟨2482370267526719685500365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309827023368959580667153 2482370267526719685500365)
                ·
                  refine ⟨930888850322519882062637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2482370267526719685500365 930888850322519882062637)
                  ·
                    refine ⟨349083318870944955773489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 930888850322519882062637 349083318870944955773489)
                    ·
                      rfl

theorem cell22_1019756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_1019756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019756 prefixEnd_1019756 := by exact prefixLift 1019756
  have htrace : WordTrace (prefixWord ++ tailWord_1019756) baseStart_1019756 baseEnd_1019756 := by
    simpa [prefixWord, tailWord_1019756, baseEnd_1019756] using wordTrace_append hprefix tailTrace_1019756
  have hstable : (prefixWord ++ tailWord_1019756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019756).length < 2 ^ (prefixWord ++ tailWord_1019756).sum := by decide
  have hdescent : baseEnd_1019756 < baseStart_1019756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019758 : List Nat := [4, 1, 2, 3, 1, 3, 2, 6]
def baseStart_1019758 : Nat := 118140960795 + 1019758 * 2 ^ 59
def prefixEnd_1019758 : Nat := 4983230072969 + 3 ^ 40 * 1019758 * 2
def baseEnd_1019758 : Nat := 38787111501313068580387

theorem tailTrace_1019758 : CollatzResearch.WordTrace tailWord_1019758 prefixEnd_1019758 38787111501313068580387 := by
  unfold tailWord_1019758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4649203729949800205732491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24795753226398934430573285 4649203729949800205732491)
  ·
    refine ⟨6973805594924700308598737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4649203729949800205732491 6973805594924700308598737)
    ·
      refine ⟨5230354196193525231449053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6973805594924700308598737 5230354196193525231449053)
      ·
        refine ⟨1961382823572571961793395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5230354196193525231449053 1961382823572571961793395)
        ·
          refine ⟨2942074235358857942690093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961382823572571961793395 2942074235358857942690093)
          ·
            refine ⟨1103277838259571728508785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2942074235358857942690093 1103277838259571728508785)
            ·
              refine ⟨827458378694678796381589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103277838259571728508785 827458378694678796381589)
              ·
                refine ⟨38787111501313068580387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 827458378694678796381589 38787111501313068580387)
                ·
                  rfl

theorem cell22_1019758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_1019758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019758 prefixEnd_1019758 := by exact prefixLift 1019758
  have htrace : WordTrace (prefixWord ++ tailWord_1019758) baseStart_1019758 baseEnd_1019758 := by
    simpa [prefixWord, tailWord_1019758, baseEnd_1019758] using wordTrace_append hprefix tailTrace_1019758
  have hstable : (prefixWord ++ tailWord_1019758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019758).length < 2 ^ (prefixWord ++ tailWord_1019758).sum := by decide
  have hdescent : baseEnd_1019758 < baseStart_1019758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019831 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 4]
def baseStart_1019831 : Nat := 118140960795 + 1019831 * 2 ^ 59
def prefixEnd_1019831 : Nat := 4983230072969 + 3 ^ 40 * 1019831 * 2
def baseEnd_1019831 : Nat := 116369664301223253382753

theorem tailTrace_1019831 : CollatzResearch.WordTrace tailWord_1019831 prefixEnd_1019831 116369664301223253382753 := by
  unfold tailWord_1019831
  simp only [CollatzResearch.WordTrace]
  refine ⟨37196292368333935113267347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24797528245555956742178231 37196292368333935113267347)
  ·
    refine ⟨55794438552500902669901021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37196292368333935113267347 55794438552500902669901021)
    ·
      refine ⟨20922914457187838501212883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55794438552500902669901021 20922914457187838501212883)
      ·
        refine ⟨31384371685781757751819325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20922914457187838501212883 31384371685781757751819325)
        ·
          refine ⟨11769139382168159156932247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31384371685781757751819325 11769139382168159156932247)
          ·
            refine ⟨17653709073252238735398371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769139382168159156932247 17653709073252238735398371)
            ·
              refine ⟨26480563609878358103097557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17653709073252238735398371 26480563609878358103097557)
              ·
                refine ⟨620638209606524018041349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26480563609878358103097557 620638209606524018041349)
                ·
                  refine ⟨116369664301223253382753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620638209606524018041349 116369664301223253382753)
                  ·
                    rfl

theorem cell22_1019831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 4].length) (baseStart_1019831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019831 prefixEnd_1019831 := by exact prefixLift 1019831
  have htrace : WordTrace (prefixWord ++ tailWord_1019831) baseStart_1019831 baseEnd_1019831 := by
    simpa [prefixWord, tailWord_1019831, baseEnd_1019831] using wordTrace_append hprefix tailTrace_1019831
  have hstable : (prefixWord ++ tailWord_1019831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019831).length < 2 ^ (prefixWord ++ tailWord_1019831).sum := by decide
  have hdescent : baseEnd_1019831 < baseStart_1019831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019833 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 1, 4]
def baseStart_1019833 : Nat := 118140960795 + 1019833 * 2 ^ 59
def prefixEnd_1019833 : Nat := 4983230072969 + 3 ^ 40 * 1019833 * 2
def baseEnd_1019833 : Nat := 349109677544542421598253

theorem tailTrace_1019833 : CollatzResearch.WordTrace tailWord_1019833 prefixEnd_1019833 349109677544542421598253 := by
  unfold tailWord_1019833
  simp only [CollatzResearch.WordTrace]
  refine ⟨37196365314326689454840153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24797576876217792969893435 37196365314326689454840153)
  ·
    refine ⟨27897273985745017091130115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37196365314326689454840153 27897273985745017091130115)
    ·
      refine ⟨41845910978617525636695173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27897273985745017091130115 41845910978617525636695173)
      ·
        refine ⟨7846108308490786056880345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41845910978617525636695173 7846108308490786056880345)
        ·
          refine ⟨5884581231368089542660259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846108308490786056880345 5884581231368089542660259)
          ·
            refine ⟨8826871847052134313990389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884581231368089542660259 8826871847052134313990389)
            ·
              refine ⟨827519235661137591936599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8826871847052134313990389 827519235661137591936599)
              ·
                refine ⟨1241278853491706387904899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827519235661137591936599 1241278853491706387904899)
                ·
                  refine ⟨1861918280237559581857349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241278853491706387904899 1861918280237559581857349)
                  ·
                    refine ⟨349109677544542421598253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1861918280237559581857349 349109677544542421598253)
                    ·
                      rfl

theorem cell22_1019833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_1019833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019833 prefixEnd_1019833 := by exact prefixLift 1019833
  have htrace : WordTrace (prefixWord ++ tailWord_1019833) baseStart_1019833 baseEnd_1019833 := by
    simpa [prefixWord, tailWord_1019833, baseEnd_1019833] using wordTrace_append hprefix tailTrace_1019833
  have hstable : (prefixWord ++ tailWord_1019833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019833).length < 2 ^ (prefixWord ++ tailWord_1019833).sum := by decide
  have hdescent : baseEnd_1019833 < baseStart_1019833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019848 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 4]
def baseStart_1019848 : Nat := 118140960795 + 1019848 * 2 ^ 59
def prefixEnd_1019848 : Nat := 4983230072969 + 3 ^ 40 * 1019848 * 2
def baseEnd_1019848 : Nat := 116371604117029127491069

theorem tailTrace_1019848 : CollatzResearch.WordTrace tailWord_1019848 prefixEnd_1019848 116371604117029127491069 := by
  unfold tailWord_1019848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598456204636173508318099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24797941606181564677757465 18598456204636173508318099)
  ·
    refine ⟨27897684306954260262477149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598456204636173508318099 27897684306954260262477149)
    ·
      refine ⟨10461631615107847598428931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27897684306954260262477149 10461631615107847598428931)
      ·
        refine ⟨15692447422661771397643397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10461631615107847598428931 15692447422661771397643397)
        ·
          refine ⟨2942333891749082137058137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15692447422661771397643397 2942333891749082137058137)
          ·
            refine ⟨2206750418811811602793603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942333891749082137058137 2206750418811811602793603)
            ·
              refine ⟨3310125628217717404190405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206750418811811602793603 3310125628217717404190405)
              ·
                refine ⟨620648555290822013285701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3310125628217717404190405 620648555290822013285701)
                ·
                  refine ⟨116371604117029127491069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620648555290822013285701 116371604117029127491069)
                  ·
                    rfl

theorem cell22_1019848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 4].length) (baseStart_1019848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019848 prefixEnd_1019848 := by exact prefixLift 1019848
  have htrace : WordTrace (prefixWord ++ tailWord_1019848) baseStart_1019848 baseEnd_1019848 := by
    simpa [prefixWord, tailWord_1019848, baseEnd_1019848] using wordTrace_append hprefix tailTrace_1019848
  have hstable : (prefixWord ++ tailWord_1019848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019848).length < 2 ^ (prefixWord ++ tailWord_1019848).sum := by decide
  have hdescent : baseEnd_1019848 < baseStart_1019848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1019876 : List Nat := [2, 3, 1, 1, 1, 1, 7, 6]
def baseStart_1019876 : Nat := 118140960795 + 1019876 * 2 ^ 59
def prefixEnd_1019876 : Nat := 4983230072969 + 3 ^ 40 * 1019876 * 2
def baseEnd_1019876 : Nat := 38791599702589404752569

theorem tailTrace_1019876 : CollatzResearch.WordTrace tailWord_1019876 prefixEnd_1019876 38791599702589404752569 := by
  unfold tailWord_1019876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598966826585453899327741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24798622435447271865770321 18598966826585453899327741)
  ·
    refine ⟨6974612559969545212247903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18598966826585453899327741 6974612559969545212247903)
    ·
      refine ⟨10461918839954317818371855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6974612559969545212247903 10461918839954317818371855)
      ·
        refine ⟨15692878259931476727557783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10461918839954317818371855 15692878259931476727557783)
        ·
          refine ⟨23539317389897215091336675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15692878259931476727557783 23539317389897215091336675)
          ·
            refine ⟨35308976084845822637005013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23539317389897215091336675 35308976084845822637005013)
            ·
              refine ⟨827554126988573968054805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35308976084845822637005013 827554126988573968054805)
              ·
                refine ⟨38791599702589404752569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 827554126988573968054805 38791599702589404752569)
                ·
                  rfl

theorem cell22_1019876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 6].length) (baseStart_1019876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1019876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1019876 prefixEnd_1019876 := by exact prefixLift 1019876
  have htrace : WordTrace (prefixWord ++ tailWord_1019876) baseStart_1019876 baseEnd_1019876 := by
    simpa [prefixWord, tailWord_1019876, baseEnd_1019876] using wordTrace_append hprefix tailTrace_1019876
  have hstable : (prefixWord ++ tailWord_1019876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1019876).length < 2 ^ (prefixWord ++ tailWord_1019876).sum := by decide
  have hdescent : baseEnd_1019876 < baseStart_1019876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1019876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020013 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1020013 : Nat := 118140960795 + 1020013 * 2 ^ 59
def prefixEnd_1020013 : Nat := 4983230072969 + 3 ^ 40 * 1020013 * 2
def baseEnd_1020013 : Nat := 349171295223081952097701

theorem tailTrace_1020013 : CollatzResearch.WordTrace tailWord_1020013 prefixEnd_1020013 349171295223081952097701 := by
  unfold tailWord_1020013
  simp only [CollatzResearch.WordTrace]
  refine ⟨37202930453674580196392693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24801953635783053464261795 37202930453674580196392693)
  ·
    refine ⟨3487774730031991893411815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37202930453674580196392693 3487774730031991893411815)
    ·
      refine ⟨5231662095047987840117723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487774730031991893411815 5231662095047987840117723)
      ·
        refine ⟨7847493142571981760176585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5231662095047987840117723 7847493142571981760176585)
        ·
          refine ⟨5885619856928986320132439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7847493142571981760176585 5885619856928986320132439)
          ·
            refine ⟨8828429785393479480198659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885619856928986320132439 8828429785393479480198659)
            ·
              refine ⟨13242644678090219220297989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828429785393479480198659 13242644678090219220297989)
              ·
                refine ⟨2482995877141916103805873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13242644678090219220297989 2482995877141916103805873)
                ·
                  refine ⟨1862246907856437077854405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2482995877141916103805873 1862246907856437077854405)
                  ·
                    refine ⟨349171295223081952097701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1862246907856437077854405 349171295223081952097701)
                    ·
                      rfl

theorem cell22_1020013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1020013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020013 prefixEnd_1020013 := by exact prefixLift 1020013
  have htrace : WordTrace (prefixWord ++ tailWord_1020013) baseStart_1020013 baseEnd_1020013 := by
    simpa [prefixWord, tailWord_1020013, baseEnd_1020013] using wordTrace_append hprefix tailTrace_1020013
  have hstable : (prefixWord ++ tailWord_1020013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020013).length < 2 ^ (prefixWord ++ tailWord_1020013).sum := by decide
  have hdescent : baseEnd_1020013 < baseStart_1020013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020015 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 2, 3]
def baseStart_1020015 : Nat := 118140960795 + 1020015 * 2 ^ 59
def prefixEnd_1020015 : Nat := 4983230072969 + 3 ^ 40 * 1020015 * 2
def baseEnd_1020015 : Nat := 349171979863954613547695

theorem tailTrace_1020015 : CollatzResearch.WordTrace tailWord_1020015 prefixEnd_1020015 349171979863954613547695 := by
  unfold tailWord_1020015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37203003399667334537965499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24802002266444889691976999 37203003399667334537965499)
  ·
    refine ⟨55804505099501001806948249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37203003399667334537965499 55804505099501001806948249)
    ·
      refine ⟨41853378824625751355211187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55804505099501001806948249 41853378824625751355211187)
      ·
        refine ⟨62780068236938627032816781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41853378824625751355211187 62780068236938627032816781)
        ·
          refine ⟨23542525588851985137306293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62780068236938627032816781 23542525588851985137306293)
          ·
            refine ⟨2207111773954873606622465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23542525588851985137306293 2207111773954873606622465)
            ·
              refine ⟨1655333830466155204966849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207111773954873606622465 1655333830466155204966849)
              ·
                refine ⟨1241500372849616403725137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655333830466155204966849 1241500372849616403725137)
                ·
                  refine ⟨931125279637212302793853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1241500372849616403725137 931125279637212302793853)
                  ·
                    refine ⟨349171979863954613547695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931125279637212302793853 349171979863954613547695)
                    ·
                      rfl

theorem cell22_1020015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_1020015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020015 prefixEnd_1020015 := by exact prefixLift 1020015
  have htrace : WordTrace (prefixWord ++ tailWord_1020015) baseStart_1020015 baseEnd_1020015 := by
    simpa [prefixWord, tailWord_1020015, baseEnd_1020015] using wordTrace_append hprefix tailTrace_1020015
  have hstable : (prefixWord ++ tailWord_1020015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020015).length < 2 ^ (prefixWord ++ tailWord_1020015).sum := by decide
  have hdescent : baseEnd_1020015 < baseStart_1020015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020028 : List Nat := [2, 2, 2, 1, 1, 6, 1, 7]
def baseStart_1020028 : Nat := 118140960795 + 1020028 * 2 ^ 59
def prefixEnd_1020028 : Nat := 4983230072969 + 3 ^ 40 * 1020028 * 2
def baseEnd_1020028 : Nat := 38797381114402990330295

theorem tailTrace_1020028 : CollatzResearch.WordTrace tailWord_1020028 prefixEnd_1020028 38797381114402990330295 := by
  unfold tailWord_1020028
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601738774310118879094369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24802318365746825172125825 18601738774310118879094369)
  ·
    refine ⟨13951304080732589159320777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18601738774310118879094369 13951304080732589159320777)
    ·
      refine ⟨10463478060549441869490583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13951304080732589159320777 10463478060549441869490583)
      ·
        refine ⟨15695217090824162804235875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10463478060549441869490583 15695217090824162804235875)
        ·
          refine ⟨23542825636236244206353813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15695217090824162804235875 23542825636236244206353813)
          ·
            refine ⟨1103569951698573947172835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23542825636236244206353813 1103569951698573947172835)
            ·
              refine ⟨1655354927547860920759253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103569951698573947172835 1655354927547860920759253)
              ·
                refine ⟨38797381114402990330295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1655354927547860920759253 38797381114402990330295)
                ·
                  rfl

theorem cell22_1020028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 7].length) (baseStart_1020028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020028 prefixEnd_1020028 := by exact prefixLift 1020028
  have htrace : WordTrace (prefixWord ++ tailWord_1020028) baseStart_1020028 baseEnd_1020028 := by
    simpa [prefixWord, tailWord_1020028, baseEnd_1020028] using wordTrace_append hprefix tailTrace_1020028
  have hstable : (prefixWord ++ tailWord_1020028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020028).length < 2 ^ (prefixWord ++ tailWord_1020028).sum := by decide
  have hdescent : baseEnd_1020028 < baseStart_1020028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020041 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_1020041 : Nat := 118140960795 + 1020041 * 2 ^ 59
def prefixEnd_1020041 : Nat := 4983230072969 + 3 ^ 40 * 1020041 * 2
def baseEnd_1020041 : Nat := 349180880195299212397615

theorem tailTrace_1020041 : CollatzResearch.WordTrace tailWord_1020041 prefixEnd_1020041 349180880195299212397615 := by
  unfold tailWord_1020041
  simp only [CollatzResearch.WordTrace]
  refine ⟨37203951697573140978411977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24802634465048760652274651 37203951697573140978411977)
  ·
    refine ⟨27902963773179855733808983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37203951697573140978411977 27902963773179855733808983)
    ·
      refine ⟨41854445659769783600713475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27902963773179855733808983 41854445659769783600713475)
      ·
        refine ⟨62781668489654675401070213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41854445659769783600713475 62781668489654675401070213)
        ·
          refine ⟨11771562841810251637700665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62781668489654675401070213 11771562841810251637700665)
          ·
            refine ⟨8828672131357688728275499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11771562841810251637700665 8828672131357688728275499)
            ·
              refine ⟨13243008197036533092413249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828672131357688728275499 13243008197036533092413249)
              ·
                refine ⟨9932256147777399819309937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13243008197036533092413249 9932256147777399819309937)
                ·
                  refine ⟨7449192110833049864482453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932256147777399819309937 7449192110833049864482453)
                  ·
                    refine ⟨349180880195299212397615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7449192110833049864482453 349180880195299212397615)
                    ·
                      rfl

theorem cell22_1020041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_1020041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020041 prefixEnd_1020041 := by exact prefixLift 1020041
  have htrace : WordTrace (prefixWord ++ tailWord_1020041) baseStart_1020041 baseEnd_1020041 := by
    simpa [prefixWord, tailWord_1020041, baseEnd_1020041] using wordTrace_append hprefix tailTrace_1020041
  have hstable : (prefixWord ++ tailWord_1020041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020041).length < 2 ^ (prefixWord ++ tailWord_1020041).sum := by decide
  have hdescent : baseEnd_1020041 < baseStart_1020041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020077 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_1020077 : Nat := 118140960795 + 1020077 * 2 ^ 59
def prefixEnd_1020077 : Nat := 4983230072969 + 3 ^ 40 * 1020077 * 2
def baseEnd_1020077 : Nat := 349193203731007118497505

theorem tailTrace_1020077 : CollatzResearch.WordTrace tailWord_1020077 prefixEnd_1020077 349193203731007118497505 := by
  unfold tailWord_1020077
  simp only [CollatzResearch.WordTrace]
  refine ⟨37205264725442719126722485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24803509816961812751148323 37205264725442719126722485)
  ·
    refine ⟨3487993568010254918130233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37205264725442719126722485 3487993568010254918130233)
    ·
      refine ⟨2615995176007691188597675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3487993568010254918130233 2615995176007691188597675)
      ·
        refine ⟨3923992764011536782896513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615995176007691188597675 3923992764011536782896513)
        ·
          refine ⟨2942994573008652587172385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923992764011536782896513 2942994573008652587172385)
          ·
            refine ⟨2207245929756489440379289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942994573008652587172385 2207245929756489440379289)
            ·
              refine ⟨1655434447317367080284467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207245929756489440379289 1655434447317367080284467)
              ·
                refine ⟨2483151670976050620426701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655434447317367080284467 2483151670976050620426701)
                ·
                  refine ⟨931181876616018982660013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2483151670976050620426701 931181876616018982660013)
                  ·
                    refine ⟨349193203731007118497505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931181876616018982660013 349193203731007118497505)
                    ·
                      rfl

theorem cell22_1020077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_1020077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020077 prefixEnd_1020077 := by exact prefixLift 1020077
  have htrace : WordTrace (prefixWord ++ tailWord_1020077) baseStart_1020077 baseEnd_1020077 := by
    simpa [prefixWord, tailWord_1020077, baseEnd_1020077] using wordTrace_append hprefix tailTrace_1020077
  have hstable : (prefixWord ++ tailWord_1020077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020077).length < 2 ^ (prefixWord ++ tailWord_1020077).sum := by decide
  have hdescent : baseEnd_1020077 < baseStart_1020077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020120 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_1020120 : Nat := 118140960795 + 1020120 * 2 ^ 59
def prefixEnd_1020120 : Nat := 4983230072969 + 3 ^ 40 * 1020120 * 2
def baseEnd_1020120 : Nat := 349207923509769339672373

theorem tailTrace_1020120 : CollatzResearch.WordTrace tailWord_1020120 prefixEnd_1020120 349207923509769339672373 := by
  unfold tailWord_1020120
  simp only [CollatzResearch.WordTrace]
  refine ⟨18603416532143468735268907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24804555376191291647025209 18603416532143468735268907)
  ·
    refine ⟨27905124798215203102903361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18603416532143468735268907 27905124798215203102903361)
    ·
      refine ⟨20928843598661402327177521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27905124798215203102903361 20928843598661402327177521)
      ·
        refine ⟨15696632698996051745383141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20928843598661402327177521 15696632698996051745383141)
        ·
          refine ⟨2943118631061759702259339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15696632698996051745383141 2943118631061759702259339)
          ·
            refine ⟨4414677946592639553389009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943118631061759702259339 4414677946592639553389009)
            ·
              refine ⟨3311008459944479665041757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414677946592639553389009 3311008459944479665041757)
              ·
                refine ⟨1241628172479179874390659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3311008459944479665041757 1241628172479179874390659)
                ·
                  refine ⟨1862442258718769811585989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241628172479179874390659 1862442258718769811585989)
                  ·
                    refine ⟨349207923509769339672373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1862442258718769811585989 349207923509769339672373)
                    ·
                      rfl

theorem cell22_1020120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_1020120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020120 prefixEnd_1020120 := by exact prefixLift 1020120
  have htrace : WordTrace (prefixWord ++ tailWord_1020120) baseStart_1020120 baseEnd_1020120 := by
    simpa [prefixWord, tailWord_1020120, baseEnd_1020120] using wordTrace_append hprefix tailTrace_1020120
  have hstable : (prefixWord ++ tailWord_1020120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020120).length < 2 ^ (prefixWord ++ tailWord_1020120).sum := by decide
  have hdescent : baseEnd_1020120 < baseStart_1020120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020135 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 6]
def baseStart_1020135 : Nat := 118140960795 + 1020135 * 2 ^ 59
def prefixEnd_1020135 : Nat := 4983230072969 + 3 ^ 40 * 1020135 * 2
def baseEnd_1020135 : Nat := 116404352772104766849109

theorem tailTrace_1020135 : CollatzResearch.WordTrace tailWord_1020135 prefixEnd_1020135 116404352772104766849109 := by
  unfold tailWord_1020135
  simp only [CollatzResearch.WordTrace]
  refine ⟨37207380159232595032333859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24804920106155063354889239 37207380159232595032333859)
  ·
    refine ⟨55811070238848892548500789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37207380159232595032333859 55811070238848892548500789)
    ·
      refine ⟨5232287834892083676421949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55811070238848892548500789 5232287834892083676421949)
      ·
        refine ⟨1962107938084531378658231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5232287834892083676421949 1962107938084531378658231)
        ·
          refine ⟨2943161907126797067987347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962107938084531378658231 2943161907126797067987347)
          ·
            refine ⟨4414742860690195601981021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943161907126797067987347 4414742860690195601981021)
            ·
              refine ⟨1655528572758823350742883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4414742860690195601981021 1655528572758823350742883)
              ·
                refine ⟨2483292859138235026114325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655528572758823350742883 2483292859138235026114325)
                ·
                  refine ⟨116404352772104766849109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2483292859138235026114325 116404352772104766849109)
                  ·
                    rfl

theorem cell22_1020135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 6].length) (baseStart_1020135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020135 prefixEnd_1020135 := by exact prefixLift 1020135
  have htrace : WordTrace (prefixWord ++ tailWord_1020135) baseStart_1020135 baseEnd_1020135 := by
    simpa [prefixWord, tailWord_1020135, baseEnd_1020135] using wordTrace_append hprefix tailTrace_1020135
  have hstable : (prefixWord ++ tailWord_1020135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020135).length < 2 ^ (prefixWord ++ tailWord_1020135).sum := by decide
  have hdescent : baseEnd_1020135 < baseStart_1020135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020167 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1020167 : Nat := 118140960795 + 1020167 * 2 ^ 59
def prefixEnd_1020167 : Nat := 4983230072969 + 3 ^ 40 * 1020167 * 2
def baseEnd_1020167 : Nat := 349224012570276883747229

theorem tailTrace_1020167 : CollatzResearch.WordTrace tailWord_1020167 prefixEnd_1020167 349224012570276883747229 := by
  unfold tailWord_1020167
  simp only [CollatzResearch.WordTrace]
  refine ⟨37208547295116664497498755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24805698196744442998332503 37208547295116664497498755)
  ·
    refine ⟨55812820942674996746248133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37208547295116664497498755 55812820942674996746248133)
    ·
      refine ⟨10464903926751561889921525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55812820942674996746248133 10464903926751561889921525)
      ·
        refine ⟨981084743132958927180143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10464903926751561889921525 981084743132958927180143)
        ·
          refine ⟨1471627114699438390770215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981084743132958927180143 1471627114699438390770215)
          ·
            refine ⟨2207440672049157586155323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471627114699438390770215 2207440672049157586155323)
            ·
              refine ⟨3311161008073736379232985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207440672049157586155323 3311161008073736379232985)
              ·
                refine ⟨2483370756055302284424739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311161008073736379232985 2483370756055302284424739)
                ·
                  refine ⟨3725056134082953426637109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483370756055302284424739 3725056134082953426637109)
                  ·
                    refine ⟨349224012570276883747229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3725056134082953426637109 349224012570276883747229)
                    ·
                      rfl

theorem cell22_1020167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1020167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020167 prefixEnd_1020167 := by exact prefixLift 1020167
  have htrace : WordTrace (prefixWord ++ tailWord_1020167) baseStart_1020167 baseEnd_1020167 := by
    simpa [prefixWord, tailWord_1020167, baseEnd_1020167] using wordTrace_append hprefix tailTrace_1020167
  have hstable : (prefixWord ++ tailWord_1020167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020167).length < 2 ^ (prefixWord ++ tailWord_1020167).sum := by decide
  have hdescent : baseEnd_1020167 < baseStart_1020167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020186 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_1020186 : Nat := 118140960795 + 1020186 * 2 ^ 59
def prefixEnd_1020186 : Nat := 4983230072969 + 3 ^ 40 * 1020186 * 2
def baseEnd_1020186 : Nat := 116410172219522389174057

theorem tailTrace_1020186 : CollatzResearch.WordTrace tailWord_1020186 prefixEnd_1020186 116410172219522389174057 := by
  unfold tailWord_1020186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302310070511957685610103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24806160188031887161626941 9302310070511957685610103)
  ·
    refine ⟨13953465105767936528415155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302310070511957685610103 13953465105767936528415155)
    ·
      refine ⟨20930197658651904792622733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13953465105767936528415155 20930197658651904792622733)
      ·
        refine ⟨7848824121994464297233525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20930197658651904792622733 7848824121994464297233525)
        ·
          refine ⟨735827261436981027865643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7848824121994464297233525 735827261436981027865643)
          ·
            refine ⟨1103740892155471541798465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735827261436981027865643 1103740892155471541798465)
            ·
              refine ⟨827805669116603656348849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103740892155471541798465 827805669116603656348849)
              ·
                refine ⟨620854251837452742261637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827805669116603656348849 620854251837452742261637)
                ·
                  refine ⟨116410172219522389174057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 620854251837452742261637 116410172219522389174057)
                  ·
                    rfl

theorem cell22_1020186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_1020186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020186 prefixEnd_1020186 := by exact prefixLift 1020186
  have htrace : WordTrace (prefixWord ++ tailWord_1020186) baseStart_1020186 baseEnd_1020186 := by
    simpa [prefixWord, tailWord_1020186, baseEnd_1020186] using wordTrace_append hprefix tailTrace_1020186
  have hstable : (prefixWord ++ tailWord_1020186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020186).length < 2 ^ (prefixWord ++ tailWord_1020186).sum := by decide
  have hdescent : baseEnd_1020186 < baseStart_1020186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020193 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1020193 : Nat := 118140960795 + 1020193 * 2 ^ 59
def prefixEnd_1020193 : Nat := 4983230072969 + 3 ^ 40 * 1020193 * 2
def baseEnd_1020193 : Nat := 349232912901621482597149

theorem tailTrace_1020193 : CollatzResearch.WordTrace tailWord_1020193 prefixEnd_1020193 349232912901621482597149 := by
  unfold tailWord_1020193
  simp only [CollatzResearch.WordTrace]
  refine ⟨37209495593022470937945233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24806330395348313958630155 37209495593022470937945233)
  ·
    refine ⟨27907121694766853203458925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37209495593022470937945233 27907121694766853203458925)
    ·
      refine ⟨10465170635537569951297097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27907121694766853203458925 10465170635537569951297097)
      ·
        refine ⟨7848877976653177463472823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10465170635537569951297097 7848877976653177463472823)
        ·
          refine ⟨11773316964979766195209235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848877976653177463472823 11773316964979766195209235)
          ·
            refine ⟨17659975447469649292813853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773316964979766195209235 17659975447469649292813853)
            ·
              refine ⟨6622490792801118484805195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17659975447469649292813853 6622490792801118484805195)
              ·
                refine ⟨9933736189201677727207793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622490792801118484805195 9933736189201677727207793)
                ·
                  refine ⟨7450302141901258295405845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9933736189201677727207793 7450302141901258295405845)
                  ·
                    refine ⟨349232912901621482597149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7450302141901258295405845 349232912901621482597149)
                    ·
                      rfl

theorem cell22_1020193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1020193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020193 prefixEnd_1020193 := by exact prefixLift 1020193
  have htrace : WordTrace (prefixWord ++ tailWord_1020193) baseStart_1020193 baseEnd_1020193 := by
    simpa [prefixWord, tailWord_1020193, baseEnd_1020193] using wordTrace_append hprefix tailTrace_1020193
  have hstable : (prefixWord ++ tailWord_1020193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020193).length < 2 ^ (prefixWord ++ tailWord_1020193).sum := by decide
  have hdescent : baseEnd_1020193 < baseStart_1020193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020195 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 3, 3]
def baseStart_1020195 : Nat := 118140960795 + 1020195 * 2 ^ 59
def prefixEnd_1020195 : Nat := 4983230072969 + 3 ^ 40 * 1020195 * 2
def baseEnd_1020195 : Nat := 349233597542494144047143

theorem tailTrace_1020195 : CollatzResearch.WordTrace tailWord_1020195 prefixEnd_1020195 349233597542494144047143 := by
  unfold tailWord_1020195
  simp only [CollatzResearch.WordTrace]
  refine ⟨37209568539015225279518039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24806379026010150186345359 37209568539015225279518039)
  ·
    refine ⟨55814352808522837919277059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37209568539015225279518039 55814352808522837919277059)
    ·
      refine ⟨83721529212784256878915589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55814352808522837919277059 83721529212784256878915589)
      ·
        refine ⟨15697786727397048164796673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83721529212784256878915589 15697786727397048164796673)
        ·
          refine ⟨11773340045547786123597505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15697786727397048164796673 11773340045547786123597505)
          ·
            refine ⟨8830005034160839592698129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773340045547786123597505 8830005034160839592698129)
            ·
              refine ⟨6622503775620629694523597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8830005034160839592698129 6622503775620629694523597)
              ·
                refine ⟨2483438915857736135446349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6622503775620629694523597 2483438915857736135446349)
                ·
                  refine ⟨931289593446651050792381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2483438915857736135446349 931289593446651050792381)
                  ·
                    refine ⟨349233597542494144047143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931289593446651050792381 349233597542494144047143)
                    ·
                      rfl

theorem cell22_1020195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 3].length) (baseStart_1020195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020195 prefixEnd_1020195 := by exact prefixLift 1020195
  have htrace : WordTrace (prefixWord ++ tailWord_1020195) baseStart_1020195 baseEnd_1020195 := by
    simpa [prefixWord, tailWord_1020195, baseEnd_1020195] using wordTrace_append hprefix tailTrace_1020195
  have hstable : (prefixWord ++ tailWord_1020195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020195).length < 2 ^ (prefixWord ++ tailWord_1020195).sum := by decide
  have hdescent : baseEnd_1020195 < baseStart_1020195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020197 : List Nat := [1, 3, 1, 2, 6, 1, 1, 7]
def baseStart_1020197 : Nat := 118140960795 + 1020197 * 2 ^ 59
def prefixEnd_1020197 : Nat := 4983230072969 + 3 ^ 40 * 1020197 * 2
def baseEnd_1020197 : Nat := 38803809131485200610793

theorem tailTrace_1020197 : CollatzResearch.WordTrace tailWord_1020197 prefixEnd_1020197 38803809131485200610793 := by
  unfold tailWord_1020197
  simp only [CollatzResearch.WordTrace]
  refine ⟨37209641485007979621090845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24806427656671986414060563 37209641485007979621090845)
  ·
    refine ⟨13953615556877992357909067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37209641485007979621090845 13953615556877992357909067)
    ·
      refine ⟨20930423335316988536863601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13953615556877992357909067 20930423335316988536863601)
      ·
        refine ⟨15697817501487741402647701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20930423335316988536863601 15697817501487741402647701)
        ·
          refine ⟨735835195382237878249111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15697817501487741402647701 735835195382237878249111)
          ·
            refine ⟨1103752793073356817373667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735835195382237878249111 1103752793073356817373667)
            ·
              refine ⟨1655629189610035226060501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103752793073356817373667 1655629189610035226060501)
              ·
                refine ⟨38803809131485200610793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1655629189610035226060501 38803809131485200610793)
                ·
                  rfl

theorem cell22_1020197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 7].length) (baseStart_1020197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020197 prefixEnd_1020197 := by exact prefixLift 1020197
  have htrace : WordTrace (prefixWord ++ tailWord_1020197) baseStart_1020197 baseEnd_1020197 := by
    simpa [prefixWord, tailWord_1020197, baseEnd_1020197] using wordTrace_append hprefix tailTrace_1020197
  have hstable : (prefixWord ++ tailWord_1020197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020197).length < 2 ^ (prefixWord ++ tailWord_1020197).sum := by decide
  have hdescent : baseEnd_1020197 < baseStart_1020197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020212 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1020212 : Nat := 118140960795 + 1020212 * 2 ^ 59
def prefixEnd_1020212 : Nat := 4983230072969 + 3 ^ 40 * 1020212 * 2
def baseEnd_1020212 : Nat := 349239416989911766372091

theorem tailTrace_1020212 : CollatzResearch.WordTrace tailWord_1020212 prefixEnd_1020212 349239416989911766372091 := by
  unfold tailWord_1020212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18605094289976818591443445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24806792386635758121924593 18605094289976818591443445)
  ·
    refine ⟨1744227589685326742947823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18605094289976818591443445 1744227589685326742947823)
    ·
      refine ⟨2616341384527990114421735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744227589685326742947823 2616341384527990114421735)
      ·
        refine ⟨3924512076791985171632603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616341384527990114421735 3924512076791985171632603)
        ·
          refine ⟨5886768115187977757448905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924512076791985171632603 5886768115187977757448905)
          ·
            refine ⟨4415076086390983318086679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5886768115187977757448905 4415076086390983318086679)
            ·
              refine ⟨6622614129586474977130019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415076086390983318086679 6622614129586474977130019)
              ·
                refine ⟨9933921194379712465695029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622614129586474977130019 9933921194379712465695029)
                ·
                  refine ⟨931305111973098043658909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9933921194379712465695029 931305111973098043658909)
                  ·
                    refine ⟨349239416989911766372091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931305111973098043658909 349239416989911766372091)
                    ·
                      rfl

theorem cell22_1020212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1020212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020212 prefixEnd_1020212 := by exact prefixLift 1020212
  have htrace : WordTrace (prefixWord ++ tailWord_1020212) baseStart_1020212 baseEnd_1020212 := by
    simpa [prefixWord, tailWord_1020212, baseEnd_1020212] using wordTrace_append hprefix tailTrace_1020212
  have hstable : (prefixWord ++ tailWord_1020212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020212).length < 2 ^ (prefixWord ++ tailWord_1020212).sum := by decide
  have hdescent : baseEnd_1020212 < baseStart_1020212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020223 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_1020223 : Nat := 118140960795 + 1020223 * 2 ^ 59
def prefixEnd_1020223 : Nat := 4983230072969 + 3 ^ 40 * 1020223 * 2
def baseEnd_1020223 : Nat := 349243182514711404347057

theorem tailTrace_1020223 : CollatzResearch.WordTrace tailWord_1020223 prefixEnd_1020223 349243182514711404347057 := by
  unfold tailWord_1020223
  simp only [CollatzResearch.WordTrace]
  refine ⟨37210589782913786061537323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24807059855275857374358215 37210589782913786061537323)
  ·
    refine ⟨55815884674370679092305985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37210589782913786061537323 55815884674370679092305985)
    ·
      refine ⟨41861913505778009319229489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55815884674370679092305985 41861913505778009319229489)
      ·
        refine ⟨31396435129333506989422117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41861913505778009319229489 31396435129333506989422117)
        ·
          refine ⟨5886831586750032560516647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31396435129333506989422117 5886831586750032560516647)
          ·
            refine ⟨8830247380125048840774971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886831586750032560516647 8830247380125048840774971)
            ·
              refine ⟨13245371070187573261162457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8830247380125048840774971 13245371070187573261162457)
              ·
                refine ⟨9934028302640679945871843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13245371070187573261162457 9934028302640679945871843)
                ·
                  refine ⟨14901042453961019918807765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934028302640679945871843 14901042453961019918807765)
                  ·
                    refine ⟨349243182514711404347057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14901042453961019918807765 349243182514711404347057)
                    ·
                      rfl

theorem cell22_1020223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_1020223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020223 prefixEnd_1020223 := by exact prefixLift 1020223
  have htrace : WordTrace (prefixWord ++ tailWord_1020223) baseStart_1020223 baseEnd_1020223 := by
    simpa [prefixWord, tailWord_1020223, baseEnd_1020223] using wordTrace_append hprefix tailTrace_1020223
  have hstable : (prefixWord ++ tailWord_1020223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020223).length < 2 ^ (prefixWord ++ tailWord_1020223).sum := by decide
  have hdescent : baseEnd_1020223 < baseStart_1020223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020272 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_1020272 : Nat := 118140960795 + 1020272 * 2 ^ 59
def prefixEnd_1020272 : Nat := 4983230072969 + 3 ^ 40 * 1020272 * 2
def baseEnd_1020272 : Nat := 349259956216091609871907

theorem tailTrace_1020272 : CollatzResearch.WordTrace tailWord_1020272 prefixEnd_1020272 349259956216091609871907 := by
  unfold tailWord_1020272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606188479868133715035535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24808251306490844953380713 18606188479868133715035535)
  ·
    refine ⟨27909282719802200572553303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18606188479868133715035535 27909282719802200572553303)
    ·
      refine ⟨41863924079703300858829955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27909282719802200572553303 41863924079703300858829955)
      ·
        refine ⟨62795886119554951288244933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41863924079703300858829955 62795886119554951288244933)
        ·
          refine ⟨11774228647416553366545925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62795886119554951288244933 11774228647416553366545925)
          ·
            refine ⟨2207667871390603756227361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11774228647416553366545925 2207667871390603756227361)
            ·
              refine ⟨1655750903542952817170521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2207667871390603756227361 1655750903542952817170521)
              ·
                refine ⟨1241813177657214612877891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655750903542952817170521 1241813177657214612877891)
                ·
                  refine ⟨1862719766485821919316837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241813177657214612877891 1862719766485821919316837)
                  ·
                    refine ⟨349259956216091609871907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1862719766485821919316837 349259956216091609871907)
                    ·
                      rfl

theorem cell22_1020272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_1020272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020272 prefixEnd_1020272 := by exact prefixLift 1020272
  have htrace : WordTrace (prefixWord ++ tailWord_1020272) baseStart_1020272 baseEnd_1020272 := by
    simpa [prefixWord, tailWord_1020272, baseEnd_1020272] using wordTrace_append hprefix tailTrace_1020272
  have hstable : (prefixWord ++ tailWord_1020272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020272).length < 2 ^ (prefixWord ++ tailWord_1020272).sum := by decide
  have hdescent : baseEnd_1020272 < baseStart_1020272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020300 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_1020300 : Nat := 118140960795 + 1020300 * 2 ^ 59
def prefixEnd_1020300 : Nat := 4983230072969 + 3 ^ 40 * 1020300 * 2
def baseEnd_1020300 : Nat := 349269541188308870171821

theorem tailTrace_1020300 : CollatzResearch.WordTrace tailWord_1020300 prefixEnd_1020300 349269541188308870171821 := by
  unfold tailWord_1020300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606699101817414106045177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24808932135756552141393569 18606699101817414106045177)
  ·
    refine ⟨13955024326363060579533883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18606699101817414106045177 13955024326363060579533883)
    ·
      refine ⟨20932536489544590869300825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13955024326363060579533883 20932536489544590869300825)
      ·
        refine ⟨15699402367158443151975619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20932536489544590869300825 15699402367158443151975619)
        ·
          refine ⟨23549103550737664727963429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15699402367158443151975619 23549103550737664727963429)
          ·
            refine ⟨4415456915763312136493143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23549103550737664727963429 4415456915763312136493143)
            ·
              refine ⟨6623185373644968204739715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415456915763312136493143 6623185373644968204739715)
              ·
                refine ⟨9934778060467452307109573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623185373644968204739715 9934778060467452307109573)
                ·
                  refine ⟨1862770886337647307583045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9934778060467452307109573 1862770886337647307583045)
                  ·
                    refine ⟨349269541188308870171821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1862770886337647307583045 349269541188308870171821)
                    ·
                      rfl

theorem cell22_1020300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_1020300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020300 prefixEnd_1020300 := by exact prefixLift 1020300
  have htrace : WordTrace (prefixWord ++ tailWord_1020300) baseStart_1020300 baseEnd_1020300 := by
    simpa [prefixWord, tailWord_1020300, baseEnd_1020300] using wordTrace_append hprefix tailTrace_1020300
  have hstable : (prefixWord ++ tailWord_1020300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020300).length < 2 ^ (prefixWord ++ tailWord_1020300).sum := by decide
  have hdescent : baseEnd_1020300 < baseStart_1020300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020310 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1020310 : Nat := 118140960795 + 1020310 * 2 ^ 59
def prefixEnd_1020310 : Nat := 4983230072969 + 3 ^ 40 * 1020310 * 2
def baseEnd_1020310 : Nat := 116424321464224059140597

theorem tailTrace_1020310 : CollatzResearch.WordTrace tailWord_1020310 prefixEnd_1020310 116424321464224059140597 := by
  unfold tailWord_1020310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325860183349912494997149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24809175289065733279969589 2325860183349912494997149)
  ·
    refine ⟨872197568756217185623931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2325860183349912494997149 872197568756217185623931)
    ·
      refine ⟨1308296353134325778435897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 872197568756217185623931 1308296353134325778435897)
      ·
        refine ⟨981222264850744333826923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1308296353134325778435897 981222264850744333826923)
        ·
          refine ⟨1471833397276116500740385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981222264850744333826923 1471833397276116500740385)
          ·
            refine ⟨1103875047957087375555289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471833397276116500740385 1103875047957087375555289)
            ·
              refine ⟨827906285967815531666467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103875047957087375555289 827906285967815531666467)
              ·
                refine ⟨1241859428951723297499701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827906285967815531666467 1241859428951723297499701)
                ·
                  refine ⟨116424321464224059140597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1241859428951723297499701 116424321464224059140597)
                  ·
                    rfl

theorem cell22_1020310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1020310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020310 prefixEnd_1020310 := by exact prefixLift 1020310
  have htrace : WordTrace (prefixWord ++ tailWord_1020310) baseStart_1020310 baseEnd_1020310 := by
    simpa [prefixWord, tailWord_1020310, baseEnd_1020310] using wordTrace_append hprefix tailTrace_1020310
  have hstable : (prefixWord ++ tailWord_1020310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020310).length < 2 ^ (prefixWord ++ tailWord_1020310).sum := by decide
  have hdescent : baseEnd_1020310 < baseStart_1020310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020435 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_1020435 : Nat := 118140960795 + 1020435 * 2 ^ 59
def prefixEnd_1020435 : Nat := 4983230072969 + 3 ^ 40 * 1020435 * 2
def baseEnd_1020435 : Nat := 349315754447213518046407

theorem tailTrace_1020435 : CollatzResearch.WordTrace tailWord_1020435 prefixEnd_1020435 349315754447213518046407 := by
  unfold tailWord_1020435
  simp only [CollatzResearch.WordTrace]
  refine ⟨37218322058145746268254759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24812214705430497512169839 37218322058145746268254759)
  ·
    refine ⟨55827483087218619402382139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37218322058145746268254759 55827483087218619402382139)
    ·
      refine ⟨83741224630827929103573209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55827483087218619402382139 83741224630827929103573209)
      ·
        refine ⟨62805918473120946827679907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83741224630827929103573209 62805918473120946827679907)
        ·
          refine ⟨94208877709681420241519861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62805918473120946827679907 94208877709681420241519861)
          ·
            refine ⟨8832082285282633147642487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94208877709681420241519861 8832082285282633147642487)
            ·
              refine ⟨13248123427923949721463731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8832082285282633147642487 13248123427923949721463731)
              ·
                refine ⟨19872185141885924582195597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13248123427923949721463731 19872185141885924582195597)
                ·
                  refine ⟨7452069428207221718323349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19872185141885924582195597 7452069428207221718323349)
                  ·
                    refine ⟨349315754447213518046407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7452069428207221718323349 349315754447213518046407)
                    ·
                      rfl

theorem cell22_1020435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_1020435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020435 prefixEnd_1020435 := by exact prefixLift 1020435
  have htrace : WordTrace (prefixWord ++ tailWord_1020435) baseStart_1020435 baseEnd_1020435 := by
    simpa [prefixWord, tailWord_1020435, baseEnd_1020435] using wordTrace_append hprefix tailTrace_1020435
  have hstable : (prefixWord ++ tailWord_1020435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020435).length < 2 ^ (prefixWord ++ tailWord_1020435).sum := by decide
  have hdescent : baseEnd_1020435 < baseStart_1020435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020456 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 4]
def baseStart_1020456 : Nat := 118140960795 + 1020456 * 2 ^ 59
def prefixEnd_1020456 : Nat := 4983230072969 + 3 ^ 40 * 1020456 * 2
def baseEnd_1020456 : Nat := 116440981058792154423781

theorem tailTrace_1020456 : CollatzResearch.WordTrace tailWord_1020456 prefixEnd_1020456 116440981058792154423781 := by
  unfold tailWord_1020456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609543995534833427384611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24812725327379777903179481 18609543995534833427384611)
  ·
    refine ⟨27914315993302250141076917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18609543995534833427384611 27914315993302250141076917)
    ·
      refine ⟨2616967124372085950725961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27914315993302250141076917 2616967124372085950725961)
      ·
        refine ⟨1962725343279064463044471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2616967124372085950725961 1962725343279064463044471)
        ·
          refine ⟨2944088014918596694566707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962725343279064463044471 2944088014918596694566707)
          ·
            refine ⟨4416132022377895041850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944088014918596694566707 4416132022377895041850061)
            ·
              refine ⟨1656049508391710640693773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4416132022377895041850061 1656049508391710640693773)
              ·
                refine ⟨621018565646891490260165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1656049508391710640693773 621018565646891490260165)
                ·
                  refine ⟨116440981058792154423781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621018565646891490260165 116440981058792154423781)
                  ·
                    rfl

theorem cell22_1020456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_1020456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020456 prefixEnd_1020456 := by exact prefixLift 1020456
  have htrace : WordTrace (prefixWord ++ tailWord_1020456) baseStart_1020456 baseEnd_1020456 := by
    simpa [prefixWord, tailWord_1020456, baseEnd_1020456] using wordTrace_append hprefix tailTrace_1020456
  have hstable : (prefixWord ++ tailWord_1020456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020456).length < 2 ^ (prefixWord ++ tailWord_1020456).sum := by decide
  have hdescent : baseEnd_1020456 < baseStart_1020456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020516 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_1020516 : Nat := 118140960795 + 1020516 * 2 ^ 59
def prefixEnd_1020516 : Nat := 4983230072969 + 3 ^ 40 * 1020516 * 2
def baseEnd_1020516 : Nat := 349343482402556306771159

theorem tailTrace_1020516 : CollatzResearch.WordTrace tailWord_1020516 prefixEnd_1020516 349343482402556306771159 := by
  unfold tailWord_1020516
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610638185426148550976701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24814184247234864734635601 18610638185426148550976701)
  ·
    refine ⟨6978989319534805706616263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18610638185426148550976701 6978989319534805706616263)
    ·
      refine ⟨10468483979302208559924395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978989319534805706616263 10468483979302208559924395)
      ·
        refine ⟨15702725968953312839886593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10468483979302208559924395 15702725968953312839886593)
        ·
          refine ⟨11777044476714984629914945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15702725968953312839886593 11777044476714984629914945)
          ·
            refine ⟨8832783357536238472436209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11777044476714984629914945 8832783357536238472436209)
            ·
              refine ⟨6624587518152178854327157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832783357536238472436209 6624587518152178854327157)
              ·
                refine ⟨621055079826766767593171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6624587518152178854327157 621055079826766767593171)
                ·
                  refine ⟨931582619740150151389757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621055079826766767593171 931582619740150151389757)
                  ·
                    refine ⟨349343482402556306771159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931582619740150151389757 349343482402556306771159)
                    ·
                      rfl

theorem cell22_1020516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_1020516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020516 prefixEnd_1020516 := by exact prefixLift 1020516
  have htrace : WordTrace (prefixWord ++ tailWord_1020516) baseStart_1020516 baseEnd_1020516 := by
    simpa [prefixWord, tailWord_1020516, baseEnd_1020516] using wordTrace_append hprefix tailTrace_1020516
  have hstable : (prefixWord ++ tailWord_1020516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020516).length < 2 ^ (prefixWord ++ tailWord_1020516).sum := by decide
  have hdescent : baseEnd_1020516 < baseStart_1020516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020574 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1020574 : Nat := 118140960795 + 1020574 * 2 ^ 59
def prefixEnd_1020574 : Nat := 4983230072969 + 3 ^ 40 * 1020574 * 2
def baseEnd_1020574 : Nat := 116454445662621162940327

theorem tailTrace_1020574 : CollatzResearch.WordTrace tailWord_1020574 prefixEnd_1020574 116454445662621162940327 := by
  unfold tailWord_1020574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652923975580271625945597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24815594536428115338376517 4652923975580271625945597)
  ·
    refine ⟨1744846490842601859729599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4652923975580271625945597 1744846490842601859729599)
    ·
      refine ⟨2617269736263902789594399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744846490842601859729599 2617269736263902789594399)
      ·
        refine ⟨3925904604395854184391599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617269736263902789594399 3925904604395854184391599)
        ·
          refine ⟨5888856906593781276587399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925904604395854184391599 5888856906593781276587399)
          ·
            refine ⟨8833285359890671914881099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888856906593781276587399 8833285359890671914881099)
            ·
              refine ⟨13249928039836007872321649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833285359890671914881099 13249928039836007872321649)
              ·
                refine ⟨9937446029877005904241237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13249928039836007872321649 9937446029877005904241237)
                ·
                  refine ⟨116454445662621162940327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9937446029877005904241237 116454445662621162940327)
                  ·
                    rfl

theorem cell22_1020574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1020574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020574 prefixEnd_1020574 := by exact prefixLift 1020574
  have htrace : WordTrace (prefixWord ++ tailWord_1020574) baseStart_1020574 baseEnd_1020574 := by
    simpa [prefixWord, tailWord_1020574, baseEnd_1020574] using wordTrace_append hprefix tailTrace_1020574
  have hstable : (prefixWord ++ tailWord_1020574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020574).length < 2 ^ (prefixWord ++ tailWord_1020574).sum := by decide
  have hdescent : baseEnd_1020574 < baseStart_1020574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020576 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_1020576 : Nat := 118140960795 + 1020576 * 2 ^ 59
def prefixEnd_1020576 : Nat := 4983230072969 + 3 ^ 40 * 1020576 * 2
def baseEnd_1020576 : Nat := 349364021628736150270975

theorem tailTrace_1020576 : CollatzResearch.WordTrace tailWord_1020576 prefixEnd_1020576 349364021628736150270975 := by
  unfold tailWord_1020576
  simp only [CollatzResearch.WordTrace]
  refine ⟨18611732375317463674568791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24815643167089951566091721 18611732375317463674568791)
  ·
    refine ⟨27917598562976195511853187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18611732375317463674568791 27917598562976195511853187)
    ·
      refine ⟨41876397844464293267779781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27917598562976195511853187 41876397844464293267779781)
      ·
        refine ⟨7851824595837054987708709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41876397844464293267779781 7851824595837054987708709)
        ·
          refine ⟨1472217111719447810195383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7851824595837054987708709 1472217111719447810195383)
          ·
            refine ⟨2208325667579171715293075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472217111719447810195383 2208325667579171715293075)
            ·
              refine ⟨3312488501368757572939613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208325667579171715293075 3312488501368757572939613)
              ·
                refine ⟨1242183188013284089852355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312488501368757572939613 1242183188013284089852355)
                ·
                  refine ⟨1863274782019926134778533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242183188013284089852355 1863274782019926134778533)
                  ·
                    refine ⟨349364021628736150270975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1863274782019926134778533 349364021628736150270975)
                    ·
                      rfl

theorem cell22_1020576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_1020576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020576 prefixEnd_1020576 := by exact prefixLift 1020576
  have htrace : WordTrace (prefixWord ++ tailWord_1020576) baseStart_1020576 baseEnd_1020576 := by
    simpa [prefixWord, tailWord_1020576, baseEnd_1020576] using wordTrace_append hprefix tailTrace_1020576
  have hstable : (prefixWord ++ tailWord_1020576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020576).length < 2 ^ (prefixWord ++ tailWord_1020576).sum := by decide
  have hdescent : baseEnd_1020576 < baseStart_1020576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020602 : List Nat := [3, 1, 1, 1, 2, 3, 2, 9]
def baseStart_1020602 : Nat := 118140960795 + 1020602 * 2 ^ 59
def prefixEnd_1020602 : Nat := 4983230072969 + 3 ^ 40 * 1020602 * 2
def baseEnd_1020602 : Nat := 38819213551120083235655

theorem tailTrace_1020602 : CollatzResearch.WordTrace tailWord_1020602 prefixEnd_1020602 38819213551120083235655 := by
  unfold tailWord_1020602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306103262135183447396015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24816275365693822526389373 9306103262135183447396015)
  ·
    refine ⟨13959154893202775171094023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9306103262135183447396015 13959154893202775171094023)
    ·
      refine ⟨20938732339804162756641035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13959154893202775171094023 20938732339804162756641035)
      ·
        refine ⟨31408098509706244134961553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20938732339804162756641035 31408098509706244134961553)
        ·
          refine ⟨23556073882279683101221165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31408098509706244134961553 23556073882279683101221165)
          ·
            refine ⟨8833527705854881162957937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23556073882279683101221165 8833527705854881162957937)
            ·
              refine ⟨6625145779391160872218453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8833527705854881162957937 6625145779391160872218453)
              ·
                refine ⟨38819213551120083235655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6625145779391160872218453 38819213551120083235655)
                ·
                  rfl

theorem cell22_1020602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_1020602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020602 prefixEnd_1020602 := by exact prefixLift 1020602
  have htrace : WordTrace (prefixWord ++ tailWord_1020602) baseStart_1020602 baseEnd_1020602 := by
    simpa [prefixWord, tailWord_1020602, baseEnd_1020602] using wordTrace_append hprefix tailTrace_1020602
  have hstable : (prefixWord ++ tailWord_1020602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020602).length < 2 ^ (prefixWord ++ tailWord_1020602).sum := by decide
  have hdescent : baseEnd_1020602 < baseStart_1020602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020636 : List Nat := [2, 2, 5, 1, 1, 3, 8]
def baseStart_1020636 : Nat := 118140960795 + 1020636 * 2 ^ 59
def prefixEnd_1020636 : Nat := 4983230072969 + 3 ^ 40 * 1020636 * 2
def baseEnd_1020636 : Nat := 12940168920552444213733

theorem tailTrace_1020636 : CollatzResearch.WordTrace tailWord_1020636 prefixEnd_1020636 12940168920552444213733 := by
  unfold tailWord_1020636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18612826565208778798160881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24817102086945038397547841 18612826565208778798160881)
  ·
    refine ⟨13959619923906584098620661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18612826565208778798160881 13959619923906584098620661)
    ·
      refine ⟨1308714367866242259245687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13959619923906584098620661 1308714367866242259245687)
      ·
        refine ⟨1963071551799363388868531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308714367866242259245687 1963071551799363388868531)
        ·
          refine ⟨2944607327699045083302797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963071551799363388868531 2944607327699045083302797)
          ·
            refine ⟨1104227747887141906238549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2944607327699045083302797 1104227747887141906238549)
            ·
              refine ⟨12940168920552444213733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1104227747887141906238549 12940168920552444213733)
              ·
                rfl

theorem cell22_1020636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 8].length) (baseStart_1020636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020636 prefixEnd_1020636 := by exact prefixLift 1020636
  have htrace : WordTrace (prefixWord ++ tailWord_1020636) baseStart_1020636 baseEnd_1020636 := by
    simpa [prefixWord, tailWord_1020636, baseEnd_1020636] using wordTrace_append hprefix tailTrace_1020636
  have hstable : (prefixWord ++ tailWord_1020636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020636).length < 2 ^ (prefixWord ++ tailWord_1020636).sum := by decide
  have hdescent : baseEnd_1020636 < baseStart_1020636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020664 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 5]
def baseStart_1020664 : Nat := 118140960795 + 1020664 * 2 ^ 59
def prefixEnd_1020664 : Nat := 4983230072969 + 3 ^ 40 * 1020664 * 2
def baseEnd_1020664 : Nat := 116464715275711084690235

theorem tailTrace_1020664 : CollatzResearch.WordTrace tailWord_1020664 prefixEnd_1020664 116464715275711084690235 := by
  unfold tailWord_1020664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613337187158059189170523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24817782916210745585560697 18613337187158059189170523)
  ·
    refine ⟨27920005780737088783755785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18613337187158059189170523 27920005780737088783755785)
    ·
      refine ⟨20940004335552816587816839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27920005780737088783755785 20940004335552816587816839)
      ·
        refine ⟨31410006503329224881725259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20940004335552816587816839 31410006503329224881725259)
        ·
          refine ⟨47115009754993837322587889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31410006503329224881725259 47115009754993837322587889)
          ·
            refine ⟨35336257316245377991940917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47115009754993837322587889 35336257316245377991940917)
            ·
              refine ⟨3312774123398004186744461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35336257316245377991940917 3312774123398004186744461)
              ·
                refine ⟨1242290296274251570029173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312774123398004186744461 1242290296274251570029173)
                ·
                  refine ⟨116464715275711084690235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1242290296274251570029173 116464715275711084690235)
                  ·
                    rfl

theorem cell22_1020664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 5].length) (baseStart_1020664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020664 prefixEnd_1020664 := by exact prefixLift 1020664
  have htrace : WordTrace (prefixWord ++ tailWord_1020664) baseStart_1020664 baseEnd_1020664 := by
    simpa [prefixWord, tailWord_1020664, baseEnd_1020664] using wordTrace_append hprefix tailTrace_1020664
  have hstable : (prefixWord ++ tailWord_1020664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020664).length < 2 ^ (prefixWord ++ tailWord_1020664).sum := by decide
  have hdescent : baseEnd_1020664 < baseStart_1020664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020709 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 6]
def baseStart_1020709 : Nat := 118140960795 + 1020709 * 2 ^ 59
def prefixEnd_1020709 : Nat := 4983230072969 + 3 ^ 40 * 1020709 * 2
def baseEnd_1020709 : Nat := 116469850082256045565189

theorem tailTrace_1020709 : CollatzResearch.WordTrace tailWord_1020709 prefixEnd_1020709 116469850082256045565189 := by
  unfold tailWord_1020709
  simp only [CollatzResearch.WordTrace]
  refine ⟨37228315659153091063729181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24818877106102060709152787 37228315659153091063729181)
  ·
    refine ⟨13960618372182409148898443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37228315659153091063729181 13960618372182409148898443)
    ·
      refine ⟨20940927558273613723347665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13960618372182409148898443 20940927558273613723347665)
      ·
        refine ⟨15705695668705210292510749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20940927558273613723347665 15705695668705210292510749)
        ·
          refine ⟨5889635875764453859691531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15705695668705210292510749 5889635875764453859691531)
          ·
            refine ⟨8834453813646680789537297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889635875764453859691531 8834453813646680789537297)
            ·
              refine ⟨6625840360235010592152973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8834453813646680789537297 6625840360235010592152973)
              ·
                refine ⟨2484690135088128972057365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6625840360235010592152973 2484690135088128972057365)
                ·
                  refine ⟨116469850082256045565189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2484690135088128972057365 116469850082256045565189)
                  ·
                    rfl

theorem cell22_1020709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_1020709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020709 prefixEnd_1020709 := by exact prefixLift 1020709
  have htrace : WordTrace (prefixWord ++ tailWord_1020709) baseStart_1020709 baseEnd_1020709 := by
    simpa [prefixWord, tailWord_1020709, baseEnd_1020709] using wordTrace_append hprefix tailTrace_1020709
  have hstable : (prefixWord ++ tailWord_1020709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020709).length < 2 ^ (prefixWord ++ tailWord_1020709).sum := by decide
  have hdescent : baseEnd_1020709 < baseStart_1020709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020739 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 1, 6]
def baseStart_1020739 : Nat := 118140960795 + 1020739 * 2 ^ 59
def prefixEnd_1020739 : Nat := 4983230072969 + 3 ^ 40 * 1020739 * 2
def baseEnd_1020739 : Nat := 349419819859858058445475

theorem tailTrace_1020739 : CollatzResearch.WordTrace tailWord_1020739 prefixEnd_1020739 349419819859858058445475 := by
  unfold tailWord_1020739
  simp only [CollatzResearch.WordTrace]
  refine ⟨37229409849044406187321271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24819606566029604124880847 37229409849044406187321271)
  ·
    refine ⟨55844114773566609280981907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37229409849044406187321271 55844114773566609280981907)
    ·
      refine ⟨83766172160349913921472861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55844114773566609280981907 83766172160349913921472861)
      ·
        refine ⟨31412314560131217720552323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83766172160349913921472861 31412314560131217720552323)
        ·
          refine ⟨47118471840196826580828485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31412314560131217720552323 47118471840196826580828485)
          ·
            refine ⟨8834713470036904983905341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47118471840196826580828485 8834713470036904983905341)
            ·
              refine ⟨3313017551263839368964503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8834713470036904983905341 3313017551263839368964503)
              ·
                refine ⟨4969526326895759053446755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313017551263839368964503 4969526326895759053446755)
                ·
                  refine ⟨7454289490343638580170133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969526326895759053446755 7454289490343638580170133)
                  ·
                    refine ⟨349419819859858058445475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7454289490343638580170133 349419819859858058445475)
                    ·
                      rfl

theorem cell22_1020739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 6].length) (baseStart_1020739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020739 prefixEnd_1020739 := by exact prefixLift 1020739
  have htrace : WordTrace (prefixWord ++ tailWord_1020739) baseStart_1020739 baseEnd_1020739 := by
    simpa [prefixWord, tailWord_1020739, baseEnd_1020739] using wordTrace_append hprefix tailTrace_1020739
  have hstable : (prefixWord ++ tailWord_1020739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020739).length < 2 ^ (prefixWord ++ tailWord_1020739).sum := by decide
  have hdescent : baseEnd_1020739 < baseStart_1020739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020754 : List Nat := [3, 2, 2, 1, 1, 2, 11]
def baseStart_1020754 : Nat := 118140960795 + 1020754 * 2 ^ 59
def prefixEnd_1020754 : Nat := 4983230072969 + 3 ^ 40 * 1020754 * 2
def baseEnd_1020754 : Nat := 12941664987644556271127

theorem tailTrace_1020754 : CollatzResearch.WordTrace tailWord_1020754 prefixEnd_1020754 12941664987644556271127 := by
  unfold tailWord_1020754
  simp only [CollatzResearch.WordTrace]
  refine ⟨9307489235997515937279329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24819971295993375832744877 9307489235997515937279329)
  ·
    refine ⟨6980616926998136952959497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9307489235997515937279329 6980616926998136952959497)
    ·
      refine ⟨5235462695248602714719623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6980616926998136952959497 5235462695248602714719623)
      ·
        refine ⟨7853194042872904072079435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235462695248602714719623 7853194042872904072079435)
        ·
          refine ⟨11779791064309356108119153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853194042872904072079435 11779791064309356108119153)
          ·
            refine ⟨8834843298232017081089365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11779791064309356108119153 8834843298232017081089365)
            ·
              refine ⟨12941664987644556271127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8834843298232017081089365 12941664987644556271127)
              ·
                rfl

theorem cell22_1020754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 11].length) (baseStart_1020754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020754 prefixEnd_1020754 := by exact prefixLift 1020754
  have htrace : WordTrace (prefixWord ++ tailWord_1020754) baseStart_1020754 baseEnd_1020754 := by
    simpa [prefixWord, tailWord_1020754, baseEnd_1020754] using wordTrace_append hprefix tailTrace_1020754
  have hstable : (prefixWord ++ tailWord_1020754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020754).length < 2 ^ (prefixWord ++ tailWord_1020754).sum := by decide
  have hdescent : baseEnd_1020754 < baseStart_1020754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020775 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1020775 : Nat := 118140960795 + 1020775 * 2 ^ 59
def prefixEnd_1020775 : Nat := 4983230072969 + 3 ^ 40 * 1020775 * 2
def baseEnd_1020775 : Nat := 349432143395565964545365

theorem tailTrace_1020775 : CollatzResearch.WordTrace tailWord_1020775 prefixEnd_1020775 349432143395565964545365 := by
  unfold tailWord_1020775
  simp only [CollatzResearch.WordTrace]
  refine ⟨37230722876913984335631779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24820481917942656223754519 37230722876913984335631779)
  ·
    refine ⟨55846084315370976503447669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37230722876913984335631779 55846084315370976503447669)
    ·
      refine ⟨5235570404566029047198219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55846084315370976503447669 5235570404566029047198219)
      ·
        refine ⟨7853355606849043570797329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235570404566029047198219 7853355606849043570797329)
        ·
          refine ⟨5890016705136782678097997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7853355606849043570797329 5890016705136782678097997)
          ·
            refine ⟨2208756264426293504286749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5890016705136782678097997 2208756264426293504286749)
            ·
              refine ⟨828283599159860064107531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2208756264426293504286749 828283599159860064107531)
              ·
                refine ⟨1242425398739790096161297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828283599159860064107531 1242425398739790096161297)
                ·
                  refine ⟨931819049054842572120973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1242425398739790096161297 931819049054842572120973)
                  ·
                    refine ⟨349432143395565964545365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 931819049054842572120973 349432143395565964545365)
                    ·
                      rfl

theorem cell22_1020775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1020775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020775 prefixEnd_1020775 := by exact prefixLift 1020775
  have htrace : WordTrace (prefixWord ++ tailWord_1020775) baseStart_1020775 baseEnd_1020775 := by
    simpa [prefixWord, tailWord_1020775, baseEnd_1020775] using wordTrace_append hprefix tailTrace_1020775
  have hstable : (prefixWord ++ tailWord_1020775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020775).length < 2 ^ (prefixWord ++ tailWord_1020775).sum := by decide
  have hdescent : baseEnd_1020775 < baseStart_1020775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020784 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 2, 6]
def baseStart_1020784 : Nat := 118140960795 + 1020784 * 2 ^ 59
def prefixEnd_1020784 : Nat := 4983230072969 + 3 ^ 40 * 1020784 * 2
def baseEnd_1020784 : Nat := 349435224279492941070337

theorem tailTrace_1020784 : CollatzResearch.WordTrace tailWord_1020784 prefixEnd_1020784 349435224279492941070337 := by
  unfold tailWord_1020784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615525566940689436354703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24820700755920919248472937 18615525566940689436354703)
  ·
    refine ⟨27923288350411034154532055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18615525566940689436354703 27923288350411034154532055)
    ·
      refine ⟨41884932525616551231798083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27923288350411034154532055 41884932525616551231798083)
      ·
        refine ⟨62827398788424826847697125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41884932525616551231798083 62827398788424826847697125)
        ·
          refine ⟨11780137272829655033943211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62827398788424826847697125 11780137272829655033943211)
          ·
            refine ⟨17670205909244482550914817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780137272829655033943211 17670205909244482550914817)
            ·
              refine ⟨13252654431933361913186113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17670205909244482550914817 13252654431933361913186113)
              ·
                refine ⟨9939490823950021434889585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252654431933361913186113 9939490823950021434889585)
                ·
                  refine ⟨7454618117962516076167189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939490823950021434889585 7454618117962516076167189)
                  ·
                    refine ⟨349435224279492941070337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7454618117962516076167189 349435224279492941070337)
                    ·
                      rfl

theorem cell22_1020784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_1020784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020784 prefixEnd_1020784 := by exact prefixLift 1020784
  have htrace : WordTrace (prefixWord ++ tailWord_1020784) baseStart_1020784 baseEnd_1020784 := by
    simpa [prefixWord, tailWord_1020784, baseEnd_1020784] using wordTrace_append hprefix tailTrace_1020784
  have hstable : (prefixWord ++ tailWord_1020784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020784).length < 2 ^ (prefixWord ++ tailWord_1020784).sum := by decide
  have hdescent : baseEnd_1020784 < baseStart_1020784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020799 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 7]
def baseStart_1020799 : Nat := 118140960795 + 1020799 * 2 ^ 59
def prefixEnd_1020799 : Nat := 4983230072969 + 3 ^ 40 * 1020799 * 2
def baseEnd_1020799 : Nat := 116480119695345967315097

theorem tailTrace_1020799 : CollatzResearch.WordTrace tailWord_1020799 prefixEnd_1020799 116480119695345967315097 := by
  unfold tailWord_1020799
  simp only [CollatzResearch.WordTrace]
  refine ⟨37231598228827036434505451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24821065485884690956336967 37231598228827036434505451)
  ·
    refine ⟨55847397343240554651758177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37231598228827036434505451 55847397343240554651758177)
    ·
      refine ⟨41885548007430415988818633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55847397343240554651758177 41885548007430415988818633)
      ·
        refine ⟨31414161005572811991613975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41885548007430415988818633 31414161005572811991613975)
        ·
          refine ⟨47121241508359217987420963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31414161005572811991613975 47121241508359217987420963)
          ·
            refine ⟨70681862262538826981131445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47121241508359217987420963 70681862262538826981131445)
            ·
              refine ⟨6626424587113015029481073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70681862262538826981131445 6626424587113015029481073)
              ·
                refine ⟨4969818440334761272110805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6626424587113015029481073 4969818440334761272110805)
                ·
                  refine ⟨116480119695345967315097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4969818440334761272110805 116480119695345967315097)
                  ·
                    rfl

theorem cell22_1020799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 7].length) (baseStart_1020799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020799 prefixEnd_1020799 := by exact prefixLift 1020799
  have htrace : WordTrace (prefixWord ++ tailWord_1020799) baseStart_1020799 baseEnd_1020799 := by
    simpa [prefixWord, tailWord_1020799, baseEnd_1020799] using wordTrace_append hprefix tailTrace_1020799
  have hstable : (prefixWord ++ tailWord_1020799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020799).length < 2 ^ (prefixWord ++ tailWord_1020799).sum := by decide
  have hdescent : baseEnd_1020799 < baseStart_1020799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020833 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 5]
def baseStart_1020833 : Nat := 118140960795 + 1020833 * 2 ^ 59
def prefixEnd_1020833 : Nat := 4983230072969 + 3 ^ 40 * 1020833 * 2
def baseEnd_1020833 : Nat := 116483999326957715531729

theorem tailTrace_1020833 : CollatzResearch.WordTrace tailWord_1020833 prefixEnd_1020833 116483999326957715531729 := by
  unfold tailWord_1020833
  simp only [CollatzResearch.WordTrace]
  refine ⟨37232838310703860241243153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24821892207135906827495435 37232838310703860241243153)
  ·
    refine ⟨27924628733027895180932365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37232838310703860241243153 27924628733027895180932365)
    ·
      refine ⟨10471735774885460692849637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27924628733027895180932365 10471735774885460692849637)
      ·
        refine ⟨1963450457791023879909307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10471735774885460692849637 1963450457791023879909307)
        ·
          refine ⟨2945175686686535819863961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1963450457791023879909307 2945175686686535819863961)
          ·
            refine ⟨2208881765014901864897971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2945175686686535819863961 2208881765014901864897971)
            ·
              refine ⟨3313322647522352797346957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208881765014901864897971 3313322647522352797346957)
              ·
                refine ⟨1242495992820882299005109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3313322647522352797346957 1242495992820882299005109)
                ·
                  refine ⟨116483999326957715531729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1242495992820882299005109 116483999326957715531729)
                  ·
                    rfl

theorem cell22_1020833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_1020833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020833 prefixEnd_1020833 := by exact prefixLift 1020833
  have htrace : WordTrace (prefixWord ++ tailWord_1020833) baseStart_1020833 baseEnd_1020833 := by
    simpa [prefixWord, tailWord_1020833, baseEnd_1020833] using wordTrace_append hprefix tailTrace_1020833
  have hstable : (prefixWord ++ tailWord_1020833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020833).length < 2 ^ (prefixWord ++ tailWord_1020833).sum := by decide
  have hdescent : baseEnd_1020833 < baseStart_1020833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020859 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 9]
def baseStart_1020859 : Nat := 118140960795 + 1020859 * 2 ^ 59
def prefixEnd_1020859 : Nat := 4983230072969 + 3 ^ 40 * 1020859 * 2
def baseEnd_1020859 : Nat := 349460898312217745445107

theorem tailTrace_1020859 : CollatzResearch.WordTrace tailWord_1020859 prefixEnd_1020859 349460898312217745445107 := by
  unfold tailWord_1020859
  simp only [CollatzResearch.WordTrace]
  refine ⟨37233786608609666681689631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24822524405739777787793087 37233786608609666681689631)
  ·
    refine ⟨55850679912914500022534447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37233786608609666681689631 55850679912914500022534447)
    ·
      refine ⟨83776019869371750033801671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55850679912914500022534447 83776019869371750033801671)
      ·
        refine ⟨125664029804057625050702507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83776019869371750033801671 125664029804057625050702507)
        ·
          refine ⟨188496044706086437576053761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125664029804057625050702507 188496044706086437576053761)
          ·
            refine ⟨141372033529564828182040321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188496044706086437576053761 141372033529564828182040321)
            ·
              refine ⟨106029025147173621136530241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141372033529564828182040321 106029025147173621136530241)
              ·
                refine ⟨79521768860380215852397681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106029025147173621136530241 79521768860380215852397681)
                ·
                  refine ⟨59641326645285161889298261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79521768860380215852397681 59641326645285161889298261)
                  ·
                    refine ⟨349460898312217745445107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59641326645285161889298261 349460898312217745445107)
                    ·
                      rfl

theorem cell22_1020859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_1020859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020859 prefixEnd_1020859 := by exact prefixLift 1020859
  have htrace : WordTrace (prefixWord ++ tailWord_1020859) baseStart_1020859 baseEnd_1020859 := by
    simpa [prefixWord, tailWord_1020859, baseEnd_1020859] using wordTrace_append hprefix tailTrace_1020859
  have hstable : (prefixWord ++ tailWord_1020859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020859).length < 2 ^ (prefixWord ++ tailWord_1020859).sum := by decide
  have hdescent : baseEnd_1020859 < baseStart_1020859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020876 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1020876 : Nat := 118140960795 + 1020876 * 2 ^ 59
def prefixEnd_1020876 : Nat := 4983230072969 + 3 ^ 40 * 1020876 * 2
def baseEnd_1020876 : Nat := 349466717759635367770055

theorem tailTrace_1020876 : CollatzResearch.WordTrace tailWord_1020876 prefixEnd_1020876 349466717759635367770055 := by
  unfold tailWord_1020876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18617203324774039292529241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24822937766365385723372321 18617203324774039292529241)
  ·
    refine ⟨13962902493580529469396931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18617203324774039292529241 13962902493580529469396931)
    ·
      refine ⟨20944353740370794204095397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13962902493580529469396931 20944353740370794204095397)
      ·
        refine ⟨3927066326319523913267887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20944353740370794204095397 3927066326319523913267887)
        ·
          refine ⟨5890599489479285869901831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927066326319523913267887 5890599489479285869901831)
          ·
            refine ⟨8835899234218928804852747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890599489479285869901831 8835899234218928804852747)
            ·
              refine ⟨13253848851328393207279121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835899234218928804852747 13253848851328393207279121)
              ·
                refine ⟨9940386638496294905459341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13253848851328393207279121 9940386638496294905459341)
                ·
                  refine ⟨3727644989436110589547253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9940386638496294905459341 3727644989436110589547253)
                  ·
                    refine ⟨349466717759635367770055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3727644989436110589547253 349466717759635367770055)
                    ·
                      rfl

theorem cell22_1020876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1020876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020876 prefixEnd_1020876 := by exact prefixLift 1020876
  have htrace : WordTrace (prefixWord ++ tailWord_1020876) baseStart_1020876 baseEnd_1020876 := by
    simpa [prefixWord, tailWord_1020876, baseEnd_1020876] using wordTrace_append hprefix tailTrace_1020876
  have hstable : (prefixWord ++ tailWord_1020876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020876).length < 2 ^ (prefixWord ++ tailWord_1020876).sum := by decide
  have hdescent : baseEnd_1020876 < baseStart_1020876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020893 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1020893 : Nat := 118140960795 + 1020893 * 2 ^ 59
def prefixEnd_1020893 : Nat := 4983230072969 + 3 ^ 40 * 1020893 * 2
def baseEnd_1020893 : Nat := 349472537207052990095003

theorem tailTrace_1020893 : CollatzResearch.WordTrace tailWord_1020893 prefixEnd_1020893 349472537207052990095003 := by
  unfold tailWord_1020893
  simp only [CollatzResearch.WordTrace]
  refine ⟨37235026690486490488427333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24823351126990993658951555 37235026690486490488427333)
  ·
    refine ⟨6981567504466216966580125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37235026690486490488427333 6981567504466216966580125)
    ·
      refine ⟨2618087814174831362467547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6981567504466216966580125 2618087814174831362467547)
      ·
        refine ⟨3927131721262247043701321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618087814174831362467547 3927131721262247043701321)
        ·
          refine ⟨2945348790946685282775991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927131721262247043701321 2945348790946685282775991)
          ·
            refine ⟨4418023186420027924163987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945348790946685282775991 4418023186420027924163987)
            ·
              refine ⟨6627034779630041886245981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418023186420027924163987 6627034779630041886245981)
              ·
                refine ⟨2485138042361265707342243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6627034779630041886245981 2485138042361265707342243)
                ·
                  refine ⟨3727707063541898561013365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485138042361265707342243 3727707063541898561013365)
                  ·
                    refine ⟨349472537207052990095003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3727707063541898561013365 349472537207052990095003)
                    ·
                      rfl

theorem cell22_1020893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1020893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020893 prefixEnd_1020893 := by exact prefixLift 1020893
  have htrace : WordTrace (prefixWord ++ tailWord_1020893) baseStart_1020893 baseEnd_1020893 := by
    simpa [prefixWord, tailWord_1020893, baseEnd_1020893] using wordTrace_append hprefix tailTrace_1020893
  have hstable : (prefixWord ++ tailWord_1020893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020893).length < 2 ^ (prefixWord ++ tailWord_1020893).sum := by decide
  have hdescent : baseEnd_1020893 < baseStart_1020893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020914 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_1020914 : Nat := 118140960795 + 1020914 * 2 ^ 59
def prefixEnd_1020914 : Nat := 4983230072969 + 3 ^ 40 * 1020914 * 2
def baseEnd_1020914 : Nat := 349479725936215935319939

theorem tailTrace_1020914 : CollatzResearch.WordTrace tailWord_1020914 prefixEnd_1020914 349479725936215935319939 := by
  unfold tailWord_1020914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308948155852602768735449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24823861748940274049961197 9308948155852602768735449)
  ·
    refine ⟨6981711116889452076551587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9308948155852602768735449 6981711116889452076551587)
    ·
      refine ⟨10472566675334178114827381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6981711116889452076551587 10472566675334178114827381)
      ·
        refine ⟨981803125812579198265067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10472566675334178114827381 981803125812579198265067)
        ·
          refine ⟨1472704688718868797397601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981803125812579198265067 1472704688718868797397601)
          ·
            refine ⟨1104528516539151598048201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472704688718868797397601 1104528516539151598048201)
            ·
              refine ⟨828396387404363698536151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104528516539151598048201 828396387404363698536151)
              ·
                refine ⟨1242594581106545547804227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828396387404363698536151 1242594581106545547804227)
                ·
                  refine ⟨1863891871659818321706341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242594581106545547804227 1863891871659818321706341)
                  ·
                    refine ⟨349479725936215935319939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1863891871659818321706341 349479725936215935319939)
                    ·
                      rfl

theorem cell22_1020914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_1020914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020914 prefixEnd_1020914 := by exact prefixLift 1020914
  have htrace : WordTrace (prefixWord ++ tailWord_1020914) baseStart_1020914 baseEnd_1020914 := by
    simpa [prefixWord, tailWord_1020914, baseEnd_1020914] using wordTrace_append hprefix tailTrace_1020914
  have hstable : (prefixWord ++ tailWord_1020914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020914).length < 2 ^ (prefixWord ++ tailWord_1020914).sum := by decide
  have hdescent : baseEnd_1020914 < baseStart_1020914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020957 : List Nat := [1, 4, 2, 2, 4, 1, 2, 6]
def baseStart_1020957 : Nat := 118140960795 + 1020957 * 2 ^ 59
def prefixEnd_1020957 : Nat := 4983230072969 + 3 ^ 40 * 1020957 * 2
def baseEnd_1020957 : Nat := 38832716190553128499423

theorem tailTrace_1020957 : CollatzResearch.WordTrace tailWord_1020957 prefixEnd_1020957 38832716190553128499423 := by
  unfold tailWord_1020957
  simp only [CollatzResearch.WordTrace]
  refine ⟨37237360962254629418757125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24824907308169752945838083 37237360962254629418757125)
  ·
    refine ⟨6982005180422743016016961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37237360962254629418757125 6982005180422743016016961)
    ·
      refine ⟨5236503885317057262012721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6982005180422743016016961 5236503885317057262012721)
      ·
        refine ⟨3927377913987792946509541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5236503885317057262012721 3927377913987792946509541)
        ·
          refine ⟨736383358872711177470539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3927377913987792946509541 736383358872711177470539)
          ·
            refine ⟨1104575038309066766205809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736383358872711177470539 1104575038309066766205809)
            ·
              refine ⟨828431278731800074654357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104575038309066766205809 828431278731800074654357)
              ·
                refine ⟨38832716190553128499423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 828431278731800074654357 38832716190553128499423)
                ·
                  rfl

theorem cell22_1020957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 6].length) (baseStart_1020957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020957 prefixEnd_1020957 := by exact prefixLift 1020957
  have htrace : WordTrace (prefixWord ++ tailWord_1020957) baseStart_1020957 baseEnd_1020957 := by
    simpa [prefixWord, tailWord_1020957, baseEnd_1020957] using wordTrace_append hprefix tailTrace_1020957
  have hstable : (prefixWord ++ tailWord_1020957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020957).length < 2 ^ (prefixWord ++ tailWord_1020957).sum := by decide
  have hdescent : baseEnd_1020957 < baseStart_1020957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1020989 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_1020989 : Nat := 118140960795 + 1020989 * 2 ^ 59
def prefixEnd_1020989 : Nat := 4983230072969 + 3 ^ 40 * 1020989 * 2
def baseEnd_1020989 : Nat := 349505399968940739694709

theorem tailTrace_1020989 : CollatzResearch.WordTrace tailWord_1020989 prefixEnd_1020989 349505399968940739694709 := by
  unfold tailWord_1020989
  simp only [CollatzResearch.WordTrace]
  refine ⟨37238528098138698883922021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24825685398759132589281347 37238528098138698883922021)
  ·
    refine ⟨6982224018401006040735379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37238528098138698883922021 6982224018401006040735379)
    ·
      refine ⟨10473336027601509061103069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982224018401006040735379 10473336027601509061103069)
      ·
        refine ⟨3927501010350565897913651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10473336027601509061103069 3927501010350565897913651)
        ·
          refine ⟨5891251515525848846870477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927501010350565897913651 5891251515525848846870477)
          ·
            refine ⟨2209219318322193317576429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5891251515525848846870477 2209219318322193317576429)
            ·
              refine ⟨828457244370822494091161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2209219318322193317576429 828457244370822494091161)
              ·
                refine ⟨621342933278116870568371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828457244370822494091161 621342933278116870568371)
                ·
                  refine ⟨932014399917175305852557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621342933278116870568371 932014399917175305852557)
                  ·
                    refine ⟨349505399968940739694709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932014399917175305852557 349505399968940739694709)
                    ·
                      rfl

theorem cell22_1020989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_1020989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1020989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1020989 prefixEnd_1020989 := by exact prefixLift 1020989
  have htrace : WordTrace (prefixWord ++ tailWord_1020989) baseStart_1020989 baseEnd_1020989 := by
    simpa [prefixWord, tailWord_1020989, baseEnd_1020989] using wordTrace_append hprefix tailTrace_1020989
  have hstable : (prefixWord ++ tailWord_1020989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1020989).length < 2 ^ (prefixWord ++ tailWord_1020989).sum := by decide
  have hdescent : baseEnd_1020989 < baseStart_1020989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1020989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021107 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 1, 3]
def baseStart_1021107 : Nat := 118140960795 + 1021107 * 2 ^ 59
def prefixEnd_1021107 : Nat := 4983230072969 + 3 ^ 40 * 1021107 * 2
def baseEnd_1021107 : Nat := 349545793780427765244347

theorem tailTrace_1021107 : CollatzResearch.WordTrace tailWord_1021107 prefixEnd_1021107 349545793780427765244347 := by
  unfold tailWord_1021107
  simp only [CollatzResearch.WordTrace]
  refine ⟨37242831911711205036717575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24828554607807470024478383 37242831911711205036717575)
  ·
    refine ⟨55864247867566807555076363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37242831911711205036717575 55864247867566807555076363)
    ·
      refine ⟨83796371801350211332614545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55864247867566807555076363 83796371801350211332614545)
      ·
        refine ⟨62847278851012658499460909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83796371801350211332614545 62847278851012658499460909)
        ·
          refine ⟨23567729569129746937297841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62847278851012658499460909 23567729569129746937297841)
          ·
            refine ⟨17675797176847310202973381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23567729569129746937297841 17675797176847310202973381)
            ·
              refine ⟨3314211970658870663057509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17675797176847310202973381 3314211970658870663057509)
              ·
                refine ⟨621414744498538249323283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3314211970658870663057509 621414744498538249323283)
                ·
                  refine ⟨932122116747807373984925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621414744498538249323283 932122116747807373984925)
                  ·
                    refine ⟨349545793780427765244347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932122116747807373984925 349545793780427765244347)
                    ·
                      rfl

theorem cell22_1021107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 3].length) (baseStart_1021107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021107 prefixEnd_1021107 := by exact prefixLift 1021107
  have htrace : WordTrace (prefixWord ++ tailWord_1021107) baseStart_1021107 baseEnd_1021107 := by
    simpa [prefixWord, tailWord_1021107, baseEnd_1021107] using wordTrace_append hprefix tailTrace_1021107
  have hstable : (prefixWord ++ tailWord_1021107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021107).length < 2 ^ (prefixWord ++ tailWord_1021107).sum := by decide
  have hdescent : baseEnd_1021107 < baseStart_1021107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021141 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_1021141 : Nat := 118140960795 + 1021141 * 2 ^ 59
def prefixEnd_1021141 : Nat := 4983230072969 + 3 ^ 40 * 1021141 * 2
def baseEnd_1021141 : Nat := 349557432675263009894243

theorem tailTrace_1021141 : CollatzResearch.WordTrace tailWord_1021141 prefixEnd_1021141 349557432675263009894243 := by
  unfold tailWord_1021141
  simp only [CollatzResearch.WordTrace]
  refine ⟨37244071993588028843455277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24829381329058685895636851 37244071993588028843455277)
  ·
    refine ⟨13966526997595510816295729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37244071993588028843455277 13966526997595510816295729)
    ·
      refine ⟨10474895248196633112221797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13966526997595510816295729 10474895248196633112221797)
      ·
        refine ⟨1964042859036868708541587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10474895248196633112221797 1964042859036868708541587)
        ·
          refine ⟨2946064288555303062812381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964042859036868708541587 2946064288555303062812381)
          ·
            refine ⟨1104774108208238648554643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2946064288555303062812381 1104774108208238648554643)
            ·
              refine ⟨1657161162312357972831965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104774108208238648554643 1657161162312357972831965)
              ·
                refine ⟨621435435867134239811987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1657161162312357972831965 621435435867134239811987)
                ·
                  refine ⟨932153153800701359717981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621435435867134239811987 932153153800701359717981)
                  ·
                    refine ⟨349557432675263009894243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932153153800701359717981 349557432675263009894243)
                    ·
                      rfl

theorem cell22_1021141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_1021141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021141 prefixEnd_1021141 := by exact prefixLift 1021141
  have htrace : WordTrace (prefixWord ++ tailWord_1021141) baseStart_1021141 baseEnd_1021141 := by
    simpa [prefixWord, tailWord_1021141, baseEnd_1021141] using wordTrace_append hprefix tailTrace_1021141
  have hstable : (prefixWord ++ tailWord_1021141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021141).length < 2 ^ (prefixWord ++ tailWord_1021141).sum := by decide
  have hdescent : baseEnd_1021141 < baseStart_1021141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021193 : List Nat := [1, 2, 1, 1, 3, 3, 1, 10]
def baseStart_1021193 : Nat := 118140960795 + 1021193 * 2 ^ 59
def prefixEnd_1021193 : Nat := 4983230072969 + 3 ^ 40 * 1021193 * 2
def baseEnd_1021193 : Nat := 38841692593105800843787

theorem tailTrace_1021193 : CollatzResearch.WordTrace tailWord_1021193 prefixEnd_1021193 38841692593105800843787 := by
  unfold tailWord_1021193
  simp only [CollatzResearch.WordTrace]
  refine ⟨37245968589399641724348233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24830645726266427816232155 37245968589399641724348233)
  ·
    refine ⟨27934476442049731293261175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37245968589399641724348233 27934476442049731293261175)
    ·
      refine ⟨41901714663074596939891763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27934476442049731293261175 41901714663074596939891763)
      ·
        refine ⟨62852571994611895409837645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41901714663074596939891763 62852571994611895409837645)
        ·
          refine ⟨23569714497979460778689117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62852571994611895409837645 23569714497979460778689117)
          ·
            refine ⟨8838642936742297792008419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23569714497979460778689117 8838642936742297792008419)
            ·
              refine ⟨13257964405113446688012629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838642936742297792008419 13257964405113446688012629)
              ·
                refine ⟨38841692593105800843787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13257964405113446688012629 38841692593105800843787)
                ·
                  rfl

theorem cell22_1021193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 10].length) (baseStart_1021193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021193 prefixEnd_1021193 := by exact prefixLift 1021193
  have htrace : WordTrace (prefixWord ++ tailWord_1021193) baseStart_1021193 baseEnd_1021193 := by
    simpa [prefixWord, tailWord_1021193, baseEnd_1021193] using wordTrace_append hprefix tailTrace_1021193
  have hstable : (prefixWord ++ tailWord_1021193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021193).length < 2 ^ (prefixWord ++ tailWord_1021193).sum := by decide
  have hdescent : baseEnd_1021193 < baseStart_1021193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021195 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 2, 4]
def baseStart_1021195 : Nat := 118140960795 + 1021195 * 2 ^ 59
def prefixEnd_1021195 : Nat := 4983230072969 + 3 ^ 40 * 1021195 * 2
def baseEnd_1021195 : Nat := 349575917978824869044077

theorem tailTrace_1021195 : CollatzResearch.WordTrace tailWord_1021195 prefixEnd_1021195 349575917978824869044077 := by
  unfold tailWord_1021195
  simp only [CollatzResearch.WordTrace]
  refine ⟨37246041535392396065921039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24830694356928264043947359 37246041535392396065921039)
  ·
    refine ⟨55869062303088594098881559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37246041535392396065921039 55869062303088594098881559)
    ·
      refine ⟨83803593454632891148322339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55869062303088594098881559 83803593454632891148322339)
      ·
        refine ⟨125705390181949336722483509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83803593454632891148322339 125705390181949336722483509)
        ·
          refine ⟨11784880329557750317732829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125705390181949336722483509 11784880329557750317732829)
          ·
            refine ⟨4419330123584156369149811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11784880329557750317732829 4419330123584156369149811)
            ·
              refine ⟨6628995185376234553724717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419330123584156369149811 6628995185376234553724717)
              ·
                refine ⟨2485873194516087957646769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6628995185376234553724717 2485873194516087957646769)
                ·
                  refine ⟨1864404895887065968235077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485873194516087957646769 1864404895887065968235077)
                  ·
                    refine ⟨349575917978824869044077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1864404895887065968235077 349575917978824869044077)
                    ·
                      rfl

theorem cell22_1021195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 4].length) (baseStart_1021195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021195 prefixEnd_1021195 := by exact prefixLift 1021195
  have htrace : WordTrace (prefixWord ++ tailWord_1021195) baseStart_1021195 baseEnd_1021195 := by
    simpa [prefixWord, tailWord_1021195, baseEnd_1021195] using wordTrace_append hprefix tailTrace_1021195
  have hstable : (prefixWord ++ tailWord_1021195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021195).length < 2 ^ (prefixWord ++ tailWord_1021195).sum := by decide
  have hdescent : baseEnd_1021195 < baseStart_1021195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021216 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 4]
def baseStart_1021216 : Nat := 118140960795 + 1021216 * 2 ^ 59
def prefixEnd_1021216 : Nat := 4983230072969 + 3 ^ 40 * 1021216 * 2
def baseEnd_1021216 : Nat := 116527702235995938089671

theorem tailTrace_1021216 : CollatzResearch.WordTrace tailWord_1021216 prefixEnd_1021216 116527702235995938089671 := by
  unfold tailWord_1021216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623403734158158326217751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24831204978877544434957001 18623403734158158326217751)
  ·
    refine ⟨27935105601237237489326627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18623403734158158326217751 27935105601237237489326627)
    ·
      refine ⟨41902658401855856233989941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27935105601237237489326627 41902658401855856233989941)
      ·
        refine ⟨3928374225173986521936557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41902658401855856233989941 3928374225173986521936557)
        ·
          refine ⟨1473140334440244945726209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3928374225173986521936557 1473140334440244945726209)
          ·
            refine ⟨1104855250830183709294657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473140334440244945726209 1104855250830183709294657)
            ·
              refine ⟨828641438122637781970993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104855250830183709294657 828641438122637781970993)
              ·
                refine ⟨621481078591978336478245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828641438122637781970993 621481078591978336478245)
                ·
                  refine ⟨116527702235995938089671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 621481078591978336478245 116527702235995938089671)
                  ·
                    rfl

theorem cell22_1021216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 4].length) (baseStart_1021216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021216 prefixEnd_1021216 := by exact prefixLift 1021216
  have htrace : WordTrace (prefixWord ++ tailWord_1021216) baseStart_1021216 baseEnd_1021216 := by
    simpa [prefixWord, tailWord_1021216, baseEnd_1021216] using wordTrace_append hprefix tailTrace_1021216
  have hstable : (prefixWord ++ tailWord_1021216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021216).length < 2 ^ (prefixWord ++ tailWord_1021216).sum := by decide
  have hdescent : baseEnd_1021216 < baseStart_1021216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021242 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_1021242 : Nat := 118140960795 + 1021242 * 2 ^ 59
def prefixEnd_1021242 : Nat := 4983230072969 + 3 ^ 40 * 1021242 * 2
def baseEnd_1021242 : Nat := 349592007039332413118933

theorem tailTrace_1021242 : CollatzResearch.WordTrace tailWord_1021242 prefixEnd_1021242 349592007039332413118933 := by
  unfold tailWord_1021242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311938941555530773220495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24831837177481415395254653 9311938941555530773220495)
  ·
    refine ⟨13967908412333296159830743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9311938941555530773220495 13967908412333296159830743)
    ·
      refine ⟨20951862618499944239746115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13967908412333296159830743 20951862618499944239746115)
      ·
        refine ⟨31427793927749916359619173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20951862618499944239746115 31427793927749916359619173)
        ·
          refine ⟨5892711361453109317428595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31427793927749916359619173 5892711361453109317428595)
          ·
            refine ⟨8839067042179663976142893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892711361453109317428595 8839067042179663976142893)
            ·
              refine ⟨3314650140817373991053585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8839067042179663976142893 3314650140817373991053585)
              ·
                refine ⟨2485987605613030493290189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3314650140817373991053585 2485987605613030493290189)
                ·
                  refine ⟨932245352104886434983821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2485987605613030493290189 932245352104886434983821)
                  ·
                    refine ⟨349592007039332413118933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932245352104886434983821 349592007039332413118933)
                    ·
                      rfl

theorem cell22_1021242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_1021242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021242 prefixEnd_1021242 := by exact prefixLift 1021242
  have htrace : WordTrace (prefixWord ++ tailWord_1021242) baseStart_1021242 baseEnd_1021242 := by
    simpa [prefixWord, tailWord_1021242, baseEnd_1021242] using wordTrace_append hprefix tailTrace_1021242
  have hstable : (prefixWord ++ tailWord_1021242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021242).length < 2 ^ (prefixWord ++ tailWord_1021242).sum := by decide
  have hdescent : baseEnd_1021242 < baseStart_1021242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021375 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 4, 6]
def baseStart_1021375 : Nat := 118140960795 + 1021375 * 2 ^ 59
def prefixEnd_1021375 : Nat := 4983230072969 + 3 ^ 40 * 1021375 * 2
def baseEnd_1021375 : Nat := 349637535657364399543525

theorem tailTrace_1021375 : CollatzResearch.WordTrace tailWord_1021375 prefixEnd_1021375 349637535657364399543525 := by
  unfold tailWord_1021375
  simp only [CollatzResearch.WordTrace]
  refine ⟨37252606674740286807473579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24835071116493524538315719 37252606674740286807473579)
  ·
    refine ⟨55878910012110430211210369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37252606674740286807473579 55878910012110430211210369)
    ·
      refine ⟨41909182509082822658407777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55878910012110430211210369 41909182509082822658407777)
      ·
        refine ⟨31431886881812116993805833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41909182509082822658407777 31431886881812116993805833)
        ·
          refine ⟨23573915161359087745354375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31431886881812116993805833 23573915161359087745354375)
          ·
            refine ⟨35360872742038631618031563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23573915161359087745354375 35360872742038631618031563)
            ·
              refine ⟨53041309113057947427047345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35360872742038631618031563 53041309113057947427047345)
              ·
                refine ⟨39780981834793460570285509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53041309113057947427047345 39780981834793460570285509)
                ·
                  refine ⟨7458934094023773856928533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39780981834793460570285509 7458934094023773856928533)
                  ·
                    refine ⟨349637535657364399543525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7458934094023773856928533 349637535657364399543525)
                    ·
                      rfl

theorem cell22_1021375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_1021375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021375 prefixEnd_1021375 := by exact prefixLift 1021375
  have htrace : WordTrace (prefixWord ++ tailWord_1021375) baseStart_1021375 baseEnd_1021375 := by
    simpa [prefixWord, tailWord_1021375, baseEnd_1021375] using wordTrace_append hprefix tailTrace_1021375
  have hstable : (prefixWord ++ tailWord_1021375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021375).length < 2 ^ (prefixWord ++ tailWord_1021375).sum := by decide
  have hdescent : baseEnd_1021375 < baseStart_1021375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021396 : List Nat := [2, 4, 1, 2, 4, 1, 1, 7]
def baseStart_1021396 : Nat := 118140960795 + 1021396 * 2 ^ 59
def prefixEnd_1021396 : Nat := 4983230072969 + 3 ^ 40 * 1021396 * 2
def baseEnd_1021396 : Nat := 38849413820725260529829

theorem tailTrace_1021396 : CollatzResearch.WordTrace tailWord_1021396 prefixEnd_1021396 38849413820725260529829 := by
  unfold tailWord_1021396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18626686303832103696994021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24835581738442804929325361 18626686303832103696994021)
  ·
    refine ⟨3492503681968519443186379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18626686303832103696994021 3492503681968519443186379)
    ·
      refine ⟨5238755522952779164779569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3492503681968519443186379 5238755522952779164779569)
      ·
        refine ⟨3929066642214584373584677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5238755522952779164779569 3929066642214584373584677)
        ·
          refine ⟨736699995415234570047127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3929066642214584373584677 736699995415234570047127)
          ·
            refine ⟨1105049993122851855070691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736699995415234570047127 1105049993122851855070691)
            ·
              refine ⟨1657574989684277782606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105049993122851855070691 1657574989684277782606037)
              ·
                refine ⟨38849413820725260529829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1657574989684277782606037 38849413820725260529829)
                ·
                  rfl

theorem cell22_1021396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 7].length) (baseStart_1021396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021396 prefixEnd_1021396 := by exact prefixLift 1021396
  have htrace : WordTrace (prefixWord ++ tailWord_1021396) baseStart_1021396 baseEnd_1021396 := by
    simpa [prefixWord, tailWord_1021396, baseEnd_1021396] using wordTrace_append hprefix tailTrace_1021396
  have hstable : (prefixWord ++ tailWord_1021396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021396).length < 2 ^ (prefixWord ++ tailWord_1021396).sum := by decide
  have hdescent : baseEnd_1021396 < baseStart_1021396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021407 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 5]
def baseStart_1021407 : Nat := 118140960795 + 1021407 * 2 ^ 59
def prefixEnd_1021407 : Nat := 4983230072969 + 3 ^ 40 * 1021407 * 2
def baseEnd_1021407 : Nat := 116549496637108994247809

theorem tailTrace_1021407 : CollatzResearch.WordTrace tailWord_1021407 prefixEnd_1021407 116549496637108994247809 := by
  unfold tailWord_1021407
  simp only [CollatzResearch.WordTrace]
  refine ⟨37253773810624356272638475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24835849207082904181758983 37253773810624356272638475)
  ·
    refine ⟨55880660715936534408957713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37253773810624356272638475 55880660715936534408957713)
    ·
      refine ⟨41910495536952400806718285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55880660715936534408957713 41910495536952400806718285)
      ·
        refine ⟨15716435826357150302519357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41910495536952400806718285 15716435826357150302519357)
        ·
          refine ⟨5893663434883931363444759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15716435826357150302519357 5893663434883931363444759)
          ·
            refine ⟨8840495152325897045167139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893663434883931363444759 8840495152325897045167139)
            ·
              refine ⟨13260742728488845567750709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840495152325897045167139 13260742728488845567750709)
              ·
                refine ⟨1243194630795829271976629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13260742728488845567750709 1243194630795829271976629)
                ·
                  refine ⟨116549496637108994247809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1243194630795829271976629 116549496637108994247809)
                  ·
                    rfl

theorem cell22_1021407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 5].length) (baseStart_1021407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021407 prefixEnd_1021407 := by exact prefixLift 1021407
  have htrace : WordTrace (prefixWord ++ tailWord_1021407) baseStart_1021407 baseEnd_1021407 := by
    simpa [prefixWord, tailWord_1021407, baseEnd_1021407] using wordTrace_append hprefix tailTrace_1021407
  have hstable : (prefixWord ++ tailWord_1021407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021407).length < 2 ^ (prefixWord ++ tailWord_1021407).sum := by decide
  have hdescent : baseEnd_1021407 < baseStart_1021407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021422 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1021422 : Nat := 118140960795 + 1021422 * 2 ^ 59
def prefixEnd_1021422 : Nat := 4983230072969 + 3 ^ 40 * 1021422 * 2
def baseEnd_1021422 : Nat := 349653624717871943618381

theorem tailTrace_1021422 : CollatzResearch.WordTrace tailWord_1021422 prefixEnd_1021422 349653624717871943618381 := by
  unfold tailWord_1021422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656790113196251729304315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24836213937046675889623013 4656790113196251729304315)
  ·
    refine ⟨6985185169794377593956473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656790113196251729304315 6985185169794377593956473)
    ·
      refine ⟨5238888877345783195467355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6985185169794377593956473 5238888877345783195467355)
      ·
        refine ⟨7858333316018674793201033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238888877345783195467355 7858333316018674793201033)
        ·
          refine ⟨5893749987014006094900775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7858333316018674793201033 5893749987014006094900775)
          ·
            refine ⟨8840624980521009142351163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893749987014006094900775 8840624980521009142351163)
            ·
              refine ⟨13260937470781513713526745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840624980521009142351163 13260937470781513713526745)
              ·
                refine ⟨9945703103086135285145059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13260937470781513713526745 9945703103086135285145059)
                ·
                  refine ⟨14918554654629202927717589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9945703103086135285145059 14918554654629202927717589)
                  ·
                    refine ⟨349653624717871943618381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14918554654629202927717589 349653624717871943618381)
                    ·
                      rfl

theorem cell22_1021422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1021422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021422 prefixEnd_1021422 := by exact prefixLift 1021422
  have htrace : WordTrace (prefixWord ++ tailWord_1021422) baseStart_1021422 baseEnd_1021422 := by
    simpa [prefixWord, tailWord_1021422, baseEnd_1021422] using wordTrace_append hprefix tailTrace_1021422
  have hstable : (prefixWord ++ tailWord_1021422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021422).length < 2 ^ (prefixWord ++ tailWord_1021422).sum := by decide
  have hdescent : baseEnd_1021422 < baseStart_1021422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021441 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 5]
def baseStart_1021441 : Nat := 118140960795 + 1021441 * 2 ^ 59
def prefixEnd_1021441 : Nat := 4983230072969 + 3 ^ 40 * 1021441 * 2
def baseEnd_1021441 : Nat := 116553376268720742464441

theorem tailTrace_1021441 : CollatzResearch.WordTrace tailWord_1021441 prefixEnd_1021441 116553376268720742464441 := by
  unfold tailWord_1021441
  simp only [CollatzResearch.WordTrace]
  refine ⟨37255013892501180079376177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24836675928334120052917451 37255013892501180079376177)
  ·
    refine ⟨27941260419375885059532133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37255013892501180079376177 27941260419375885059532133)
    ·
      refine ⟨5238986328632978448662275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27941260419375885059532133 5238986328632978448662275)
      ·
        refine ⟨7858479492949467672993413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238986328632978448662275 7858479492949467672993413)
        ·
          refine ⟨1473464904928025188686265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7858479492949467672993413 1473464904928025188686265)
          ·
            refine ⟨1105098678696018891514699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473464904928025188686265 1105098678696018891514699)
            ·
              refine ⟨1657648018044028337272049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105098678696018891514699 1657648018044028337272049)
              ·
                refine ⟨1243236013533021252954037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657648018044028337272049 1243236013533021252954037)
                ·
                  refine ⟨116553376268720742464441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1243236013533021252954037 116553376268720742464441)
                  ·
                    rfl

theorem cell22_1021441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_1021441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021441 prefixEnd_1021441 := by exact prefixLift 1021441
  have htrace : WordTrace (prefixWord ++ tailWord_1021441) baseStart_1021441 baseEnd_1021441 := by
    simpa [prefixWord, tailWord_1021441, baseEnd_1021441] using wordTrace_append hprefix tailTrace_1021441
  have hstable : (prefixWord ++ tailWord_1021441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021441).length < 2 ^ (prefixWord ++ tailWord_1021441).sum := by decide
  have hdescent : baseEnd_1021441 < baseStart_1021441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021497 : List Nat := [1, 2, 1, 5, 1, 2, 10]
def baseStart_1021497 : Nat := 118140960795 + 1021497 * 2 ^ 59
def prefixEnd_1021497 : Nat := 4983230072969 + 3 ^ 40 * 1021497 * 2
def baseEnd_1021497 : Nat := 12951085138910990666413

theorem tailTrace_1021497 : CollatzResearch.WordTrace tailWord_1021497 prefixEnd_1021497 12951085138910990666413 := by
  unfold tailWord_1021497
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257056380298301643414745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24838037586865534428943163 37257056380298301643414745)
  ·
    refine ⟨27942792285223726232561059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37257056380298301643414745 27942792285223726232561059)
    ·
      refine ⟨41914188427835589348841589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27942792285223726232561059 41914188427835589348841589)
      ·
        refine ⟨3929455165109586501453899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41914188427835589348841589 3929455165109586501453899)
        ·
          refine ⟨5894182747664379752180849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929455165109586501453899 5894182747664379752180849)
          ·
            refine ⟨4420637060748284814135637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894182747664379752180849 4420637060748284814135637)
            ·
              refine ⟨12951085138910990666413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4420637060748284814135637 12951085138910990666413)
              ·
                rfl

theorem cell22_1021497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 10].length) (baseStart_1021497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021497 prefixEnd_1021497 := by exact prefixLift 1021497
  have htrace : WordTrace (prefixWord ++ tailWord_1021497) baseStart_1021497 baseEnd_1021497 := by
    simpa [prefixWord, tailWord_1021497, baseEnd_1021497] using wordTrace_append hprefix tailTrace_1021497
  have hstable : (prefixWord ++ tailWord_1021497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021497).length < 2 ^ (prefixWord ++ tailWord_1021497).sum := by decide
  have hdescent : baseEnd_1021497 < baseStart_1021497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021529 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_1021529 : Nat := 118140960795 + 1021529 * 2 ^ 59
def prefixEnd_1021529 : Nat := 4983230072969 + 3 ^ 40 * 1021529 * 2
def baseEnd_1021529 : Nat := 349690253004559331193053

theorem tailTrace_1021529 : CollatzResearch.WordTrace tailWord_1021529 prefixEnd_1021529 349690253004559331193053 := by
  unfold tailWord_1021529
  simp only [CollatzResearch.WordTrace]
  refine ⟨37258223516182371108579641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24838815677454914072386427 37258223516182371108579641)
  ·
    refine ⟨27943667637136778331434731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37258223516182371108579641 27943667637136778331434731)
    ·
      refine ⟨41915501455705167497152097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27943667637136778331434731 41915501455705167497152097)
      ·
        refine ⟨31436626091778875622864073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41915501455705167497152097 31436626091778875622864073)
        ·
          refine ⟨23577469568834156717148055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31436626091778875622864073 23577469568834156717148055)
          ·
            refine ⟨35366204353251235075722083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23577469568834156717148055 35366204353251235075722083)
            ·
              refine ⟨53049306529876852613583125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35366204353251235075722083 53049306529876852613583125)
              ·
                refine ⟨2486686243587977466261709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53049306529876852613583125 2486686243587977466261709)
                ·
                  refine ⟨932507341345491549848141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2486686243587977466261709 932507341345491549848141)
                  ·
                    refine ⟨349690253004559331193053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932507341345491549848141 349690253004559331193053)
                    ·
                      rfl

theorem cell22_1021529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_1021529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021529 prefixEnd_1021529 := by exact prefixLift 1021529
  have htrace : WordTrace (prefixWord ++ tailWord_1021529) baseStart_1021529 baseEnd_1021529 := by
    simpa [prefixWord, tailWord_1021529, baseEnd_1021529] using wordTrace_append hprefix tailTrace_1021529
  have hstable : (prefixWord ++ tailWord_1021529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021529).length < 2 ^ (prefixWord ++ tailWord_1021529).sum := by decide
  have hdescent : baseEnd_1021529 < baseStart_1021529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021649 : List Nat := [1, 2, 2, 1, 2, 5, 1, 8]
def baseStart_1021649 : Nat := 118140960795 + 1021649 * 2 ^ 59
def prefixEnd_1021649 : Nat := 4983230072969 + 3 ^ 40 * 1021649 * 2
def baseEnd_1021649 : Nat := 38859036828546557576965

theorem tailTrace_1021649 : CollatzResearch.WordTrace tailWord_1021649 prefixEnd_1021649 38859036828546557576965 := by
  unfold tailWord_1021649
  simp only [CollatzResearch.WordTrace]
  refine ⟨37262600275747631602948001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24841733517165087735298667 37262600275747631602948001)
  ·
    refine ⟨27946950206810723702211001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37262600275747631602948001 27946950206810723702211001)
    ·
      refine ⟨20960212655108042776658251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27946950206810723702211001 20960212655108042776658251)
      ·
        refine ⟨31440318982662064164987377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20960212655108042776658251 31440318982662064164987377)
        ·
          refine ⟨23580239236996548123740533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31440318982662064164987377 23580239236996548123740533)
          ·
            refine ⟨2210647428468426386600675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23580239236996548123740533 2210647428468426386600675)
            ·
              refine ⟨3315971142702639579901013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210647428468426386600675 3315971142702639579901013)
              ·
                refine ⟨38859036828546557576965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3315971142702639579901013 38859036828546557576965)
                ·
                  rfl

theorem cell22_1021649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 8].length) (baseStart_1021649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021649 prefixEnd_1021649 := by exact prefixLift 1021649
  have htrace : WordTrace (prefixWord ++ tailWord_1021649) baseStart_1021649 baseEnd_1021649 := by
    simpa [prefixWord, tailWord_1021649, baseEnd_1021649] using wordTrace_append hprefix tailTrace_1021649
  have hstable : (prefixWord ++ tailWord_1021649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021649).length < 2 ^ (prefixWord ++ tailWord_1021649).sum := by decide
  have hdescent : baseEnd_1021649 < baseStart_1021649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021679 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1021679 : Nat := 118140960795 + 1021679 * 2 ^ 59
def prefixEnd_1021679 : Nat := 4983230072969 + 3 ^ 40 * 1021679 * 2
def baseEnd_1021679 : Nat := 349741601070008939942593

theorem tailTrace_1021679 : CollatzResearch.WordTrace tailWord_1021679 prefixEnd_1021679 349741601070008939942593 := by
  unfold tailWord_1021679
  simp only [CollatzResearch.WordTrace]
  refine ⟨37263694465638946726540091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24842462977092631151026727 37263694465638946726540091)
  ·
    refine ⟨55895541698458420089810137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37263694465638946726540091 55895541698458420089810137)
    ·
      refine ⟨41921656273843815067357603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55895541698458420089810137 41921656273843815067357603)
      ·
        refine ⟨62882484410765722601036405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41921656273843815067357603 62882484410765722601036405)
        ·
          refine ⟨5895232913509286493847163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62882484410765722601036405 5895232913509286493847163)
          ·
            refine ⟨8842849370263929740770745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895232913509286493847163 8842849370263929740770745)
            ·
              refine ⟨6632137027697947305578059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8842849370263929740770745 6632137027697947305578059)
              ·
                refine ⟨9948205541546920958367089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632137027697947305578059 9948205541546920958367089)
                ·
                  refine ⟨7461154156160190718775317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9948205541546920958367089 7461154156160190718775317)
                  ·
                    refine ⟨349741601070008939942593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7461154156160190718775317 349741601070008939942593)
                    ·
                      rfl

theorem cell22_1021679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1021679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021679 prefixEnd_1021679 := by exact prefixLift 1021679
  have htrace : WordTrace (prefixWord ++ tailWord_1021679) baseStart_1021679 baseEnd_1021679 := by
    simpa [prefixWord, tailWord_1021679, baseEnd_1021679] using wordTrace_append hprefix tailTrace_1021679
  have hstable : (prefixWord ++ tailWord_1021679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021679).length < 2 ^ (prefixWord ++ tailWord_1021679).sum := by decide
  have hdescent : baseEnd_1021679 < baseStart_1021679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021698 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1021698 : Nat := 118140960795 + 1021698 * 2 ^ 59
def prefixEnd_1021698 : Nat := 4983230072969 + 3 ^ 40 * 1021698 * 2
def baseEnd_1021698 : Nat := 349748105158299223717535

theorem tailTrace_1021698 : CollatzResearch.WordTrace tailWord_1021698 prefixEnd_1021698 349748105158299223717535 := by
  unfold tailWord_1021698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9316096863142528242870437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24842924968380075314321165 9316096863142528242870437)
  ·
    refine ⟨1746768161839224045538207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9316096863142528242870437 1746768161839224045538207)
    ·
      refine ⟨2620152242758836068307311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746768161839224045538207 2620152242758836068307311)
      ·
        refine ⟨3930228364138254102460967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620152242758836068307311 3930228364138254102460967)
        ·
          refine ⟨5895342546207381153691451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930228364138254102460967 5895342546207381153691451)
          ·
            refine ⟨8843013819311071730537177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895342546207381153691451 8843013819311071730537177)
            ·
              refine ⟨6632260364483303797902883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843013819311071730537177 6632260364483303797902883)
              ·
                refine ⟨9948390546724955696854325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632260364483303797902883 9948390546724955696854325)
                ·
                  refine ⟨932661613755464596580093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9948390546724955696854325 932661613755464596580093)
                  ·
                    refine ⟨349748105158299223717535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932661613755464596580093 349748105158299223717535)
                    ·
                      rfl

theorem cell22_1021698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1021698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021698 prefixEnd_1021698 := by exact prefixLift 1021698
  have htrace : WordTrace (prefixWord ++ tailWord_1021698) baseStart_1021698 baseEnd_1021698 := by
    simpa [prefixWord, tailWord_1021698, baseEnd_1021698] using wordTrace_append hprefix tailTrace_1021698
  have hstable : (prefixWord ++ tailWord_1021698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021698).length < 2 ^ (prefixWord ++ tailWord_1021698).sum := by decide
  have hdescent : baseEnd_1021698 < baseStart_1021698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021732 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 1, 3]
def baseStart_1021732 : Nat := 118140960795 + 1021732 * 2 ^ 59
def prefixEnd_1021732 : Nat := 4983230072969 + 3 ^ 40 * 1021732 * 2
def baseEnd_1021732 : Nat := 349759744053134468367431

theorem tailTrace_1021732 : CollatzResearch.WordTrace tailWord_1021732 prefixEnd_1021732 349759744053134468367431 := by
  unfold tailWord_1021732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632813767223468389109725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24843751689631291185479633 18632813767223468389109725)
  ·
    refine ⟨6987305162708800645916147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18632813767223468389109725 6987305162708800645916147)
    ·
      refine ⟨10480957744063200968874221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6987305162708800645916147 10480957744063200968874221)
      ·
        refine ⟨3930359154023700363327833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10480957744063200968874221 3930359154023700363327833)
        ·
          refine ⟨2947769365517775272495875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930359154023700363327833 2947769365517775272495875)
          ·
            refine ⟨4421654048276662908743813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947769365517775272495875 4421654048276662908743813)
            ·
              refine ⟨829060134051874295389465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4421654048276662908743813 829060134051874295389465)
              ·
                refine ⟨621795100538905721542099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 829060134051874295389465 621795100538905721542099)
                ·
                  refine ⟨932692650808358582313149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 621795100538905721542099 932692650808358582313149)
                  ·
                    refine ⟨349759744053134468367431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932692650808358582313149 349759744053134468367431)
                    ·
                      rfl

theorem cell22_1021732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_1021732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021732 prefixEnd_1021732 := by exact prefixLift 1021732
  have htrace : WordTrace (prefixWord ++ tailWord_1021732) baseStart_1021732 baseEnd_1021732 := by
    simpa [prefixWord, tailWord_1021732, baseEnd_1021732] using wordTrace_append hprefix tailTrace_1021732
  have hstable : (prefixWord ++ tailWord_1021732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021732).length < 2 ^ (prefixWord ++ tailWord_1021732).sum := by decide
  have hdescent : baseEnd_1021732 < baseStart_1021732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021758 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1021758 : Nat := 118140960795 + 1021758 * 2 ^ 59
def prefixEnd_1021758 : Nat := 4983230072969 + 3 ^ 40 * 1021758 * 2
def baseEnd_1021758 : Nat := 349768644384479067217351

theorem tailTrace_1021758 : CollatzResearch.WordTrace tailWord_1021758 prefixEnd_1021758 349768644384479067217351 := by
  unfold tailWord_1021758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4658321979044092902333241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24844383888235162145777285 4658321979044092902333241)
  ·
    refine ⟨3493741484283069676749931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4658321979044092902333241 3493741484283069676749931)
    ·
      refine ⟨5240612226424604515124897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3493741484283069676749931 5240612226424604515124897)
      ·
        refine ⟨3930459169818453386343673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5240612226424604515124897 3930459169818453386343673)
        ·
          refine ⟨2947844377363840039757755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930459169818453386343673 2947844377363840039757755)
          ·
            refine ⟨4421766566045760059636633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947844377363840039757755 4421766566045760059636633)
            ·
              refine ⟨3316324924534320044727475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4421766566045760059636633 3316324924534320044727475)
              ·
                refine ⟨4974487386801480067091213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316324924534320044727475 4974487386801480067091213)
                ·
                  refine ⟨1865432770050555025159205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4974487386801480067091213 1865432770050555025159205)
                  ·
                    refine ⟨349768644384479067217351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1865432770050555025159205 349768644384479067217351)
                    ·
                      rfl

theorem cell22_1021758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1021758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021758 prefixEnd_1021758 := by exact prefixLift 1021758
  have htrace : WordTrace (prefixWord ++ tailWord_1021758) baseStart_1021758 baseEnd_1021758 := by
    simpa [prefixWord, tailWord_1021758, baseEnd_1021758] using wordTrace_append hprefix tailTrace_1021758
  have hstable : (prefixWord ++ tailWord_1021758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021758).length < 2 ^ (prefixWord ++ tailWord_1021758).sum := by decide
  have hdescent : baseEnd_1021758 < baseStart_1021758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021786 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1021786 : Nat := 118140960795 + 1021786 * 2 ^ 59
def prefixEnd_1021786 : Nat := 4983230072969 + 3 ^ 40 * 1021786 * 2
def baseEnd_1021786 : Nat := 349778229356696327517265

theorem tailTrace_1021786 : CollatzResearch.WordTrace tailWord_1021786 prefixEnd_1021786 349778229356696327517265 := by
  unfold tailWord_1021786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9316899269062826000171303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24845064717500869333790141 9316899269062826000171303)
  ·
    refine ⟨13975348903594239000256955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9316899269062826000171303 13975348903594239000256955)
    ·
      refine ⟨20963023355391358500385433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13975348903594239000256955 20963023355391358500385433)
      ·
        refine ⟨15722267516543518875289075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20963023355391358500385433 15722267516543518875289075)
        ·
          refine ⟨23583401274815278312933613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15722267516543518875289075 23583401274815278312933613)
          ·
            refine ⟨8843775478055729367350105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23583401274815278312933613 8843775478055729367350105)
            ·
              refine ⟨6632831608541797025512579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843775478055729367350105 6632831608541797025512579)
              ·
                refine ⟨9949247412812695538268869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632831608541797025512579 9949247412812695538268869)
                ·
                  refine ⟨1865483889902380413425413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9949247412812695538268869 1865483889902380413425413)
                  ·
                    refine ⟨349778229356696327517265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1865483889902380413425413 349778229356696327517265)
                    ·
                      rfl

theorem cell22_1021786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1021786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021786 prefixEnd_1021786 := by exact prefixLift 1021786
  have htrace : WordTrace (prefixWord ++ tailWord_1021786) baseStart_1021786 baseEnd_1021786 := by
    simpa [prefixWord, tailWord_1021786, baseEnd_1021786] using wordTrace_append hprefix tailTrace_1021786
  have hstable : (prefixWord ++ tailWord_1021786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021786).length < 2 ^ (prefixWord ++ tailWord_1021786).sum := by decide
  have hdescent : baseEnd_1021786 < baseStart_1021786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021850 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_1021850 : Nat := 118140960795 + 1021850 * 2 ^ 59
def prefixEnd_1021850 : Nat := 4983230072969 + 3 ^ 40 * 1021850 * 2
def baseEnd_1021850 : Nat := 349800137864621493917069

theorem tailTrace_1021850 : CollatzResearch.WordTrace tailWord_1021850 prefixEnd_1021850 349800137864621493917069 := by
  unfold tailWord_1021850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317482837004860732753751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24846620898679628620676669 9317482837004860732753751)
  ·
    refine ⟨13976224255507291099130627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9317482837004860732753751 13976224255507291099130627)
    ·
      refine ⟨20964336383260936648695941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13976224255507291099130627 20964336383260936648695941)
      ·
        refine ⟨3930813071861425621630489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20964336383260936648695941 3930813071861425621630489)
        ·
          refine ⟨2948109803896069216222867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930813071861425621630489 2948109803896069216222867)
          ·
            refine ⟨4422164705844103824334301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948109803896069216222867 4422164705844103824334301)
            ·
              refine ⟨1658311764691538934125363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4422164705844103824334301 1658311764691538934125363)
              ·
                refine ⟨2487467647037308401188045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658311764691538934125363 2487467647037308401188045)
                ·
                  refine ⟨932800367638990650445517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2487467647037308401188045 932800367638990650445517)
                  ·
                    refine ⟨349800137864621493917069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932800367638990650445517 349800137864621493917069)
                    ·
                      rfl

theorem cell22_1021850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_1021850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021850 prefixEnd_1021850 := by exact prefixLift 1021850
  have htrace : WordTrace (prefixWord ++ tailWord_1021850) baseStart_1021850 baseEnd_1021850 := by
    simpa [prefixWord, tailWord_1021850, baseEnd_1021850] using wordTrace_append hprefix tailTrace_1021850
  have hstable : (prefixWord ++ tailWord_1021850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021850).length < 2 ^ (prefixWord ++ tailWord_1021850).sum := by decide
  have hdescent : baseEnd_1021850 < baseStart_1021850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021861 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1021861 : Nat := 118140960795 + 1021861 * 2 ^ 59
def prefixEnd_1021861 : Nat := 4983230072969 + 3 ^ 40 * 1021861 * 2
def baseEnd_1021861 : Nat := 349803903389421131892035

theorem tailTrace_1021861 : CollatzResearch.WordTrace tailWord_1021861 prefixEnd_1021861 349803903389421131892035 := by
  unfold tailWord_1021861
  simp only [CollatzResearch.WordTrace]
  refine ⟨37270332550979591809665437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24846888367319727873110291 37270332550979591809665437)
  ·
    refine ⟨13976374706617346928624539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37270332550979591809665437 13976374706617346928624539)
    ·
      refine ⟨20964562059926020392936809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13976374706617346928624539 20964562059926020392936809)
      ·
        refine ⟨15723421544944515294702607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20964562059926020392936809 15723421544944515294702607)
        ·
          refine ⟨23585132317416772942053911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15723421544944515294702607 23585132317416772942053911)
          ·
            refine ⟨35377698476125159413080867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23585132317416772942053911 35377698476125159413080867)
            ·
              refine ⟨53066547714187739119621301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35377698476125159413080867 53066547714187739119621301)
              ·
                refine ⟨4974988848205100542464497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53066547714187739119621301 4974988848205100542464497)
                ·
                  refine ⟨3731241636153825406848373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4974988848205100542464497 3731241636153825406848373)
                  ·
                    refine ⟨349803903389421131892035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3731241636153825406848373 349803903389421131892035)
                    ·
                      rfl

theorem cell22_1021861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1021861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021861 prefixEnd_1021861 := by exact prefixLift 1021861
  have htrace : WordTrace (prefixWord ++ tailWord_1021861) baseStart_1021861 baseEnd_1021861 := by
    simpa [prefixWord, tailWord_1021861, baseEnd_1021861] using wordTrace_append hprefix tailTrace_1021861
  have hstable : (prefixWord ++ tailWord_1021861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021861).length < 2 ^ (prefixWord ++ tailWord_1021861).sum := by decide
  have hdescent : baseEnd_1021861 < baseStart_1021861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021908 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1021908 : Nat := 118140960795 + 1021908 * 2 ^ 59
def prefixEnd_1021908 : Nat := 4983230072969 + 3 ^ 40 * 1021908 * 2
def baseEnd_1021908 : Nat := 116606664149976225322297

theorem tailTrace_1021908 : CollatzResearch.WordTrace tailWord_1021908 prefixEnd_1021908 116606664149976225322297 := by
  unfold tailWord_1021908
  simp only [CollatzResearch.WordTrace]
  refine ⟨18636023390904659418313189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24848031187872879224417585 18636023390904659418313189)
  ·
    refine ⟨3494254385794623640933723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18636023390904659418313189 3494254385794623640933723)
    ·
      refine ⟨5241381578691935461400585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494254385794623640933723 5241381578691935461400585)
      ·
        refine ⟨3931036184018951596050439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241381578691935461400585 3931036184018951596050439)
        ·
          refine ⟨5896554276028427394075659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931036184018951596050439 5896554276028427394075659)
          ·
            refine ⟨8844831414042641091113489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896554276028427394075659 8844831414042641091113489)
            ·
              refine ⟨6633623560531980818335117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8844831414042641091113489 6633623560531980818335117)
              ·
                refine ⟨2487608835199492806875669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6633623560531980818335117 2487608835199492806875669)
                ·
                  refine ⟨116606664149976225322297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2487608835199492806875669 116606664149976225322297)
                  ·
                    rfl

theorem cell22_1021908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1021908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021908 prefixEnd_1021908 := by exact prefixLift 1021908
  have htrace : WordTrace (prefixWord ++ tailWord_1021908) baseStart_1021908 baseEnd_1021908 := by
    simpa [prefixWord, tailWord_1021908, baseEnd_1021908] using wordTrace_append hprefix tailTrace_1021908
  have hstable : (prefixWord ++ tailWord_1021908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021908).length < 2 ^ (prefixWord ++ tailWord_1021908).sum := by decide
  have hdescent : baseEnd_1021908 < baseStart_1021908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021923 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 1, 5]
def baseStart_1021923 : Nat := 118140960795 + 1021923 * 2 ^ 59
def prefixEnd_1021923 : Nat := 4983230072969 + 3 ^ 40 * 1021923 * 2
def baseEnd_1021923 : Nat := 349825127256473636841845

theorem tailTrace_1021923 : CollatzResearch.WordTrace tailWord_1021923 prefixEnd_1021923 349825127256473636841845 := by
  unfold tailWord_1021923
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272593876754976398422423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24848395917836650932281615 37272593876754976398422423)
  ·
    refine ⟨55908890815132464597633635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37272593876754976398422423 55908890815132464597633635)
    ·
      refine ⟨83863336222698696896450453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55908890815132464597633635 83863336222698696896450453)
      ·
        refine ⟨3931093885439001417021115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83863336222698696896450453 3931093885439001417021115)
        ·
          refine ⟨5896640828158502125531673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931093885439001417021115 5896640828158502125531673)
          ·
            refine ⟨4422480621118876594148755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896640828158502125531673 4422480621118876594148755)
            ·
              refine ⟨6633720931678314891223133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422480621118876594148755 6633720931678314891223133)
              ·
                refine ⟨2487645349379368084208675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6633720931678314891223133 2487645349379368084208675)
                ·
                  refine ⟨3731468024069052126313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487645349379368084208675 3731468024069052126313013)
                  ·
                    refine ⟨349825127256473636841845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3731468024069052126313013 349825127256473636841845)
                    ·
                      rfl

theorem cell22_1021923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_1021923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021923 prefixEnd_1021923 := by exact prefixLift 1021923
  have htrace : WordTrace (prefixWord ++ tailWord_1021923) baseStart_1021923 baseEnd_1021923 := by
    simpa [prefixWord, tailWord_1021923, baseEnd_1021923] using wordTrace_append hprefix tailTrace_1021923
  have hstable : (prefixWord ++ tailWord_1021923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021923).length < 2 ^ (prefixWord ++ tailWord_1021923).sum := by decide
  have hdescent : baseEnd_1021923 < baseStart_1021923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021936 : List Nat := [2, 1, 1, 1, 3, 2, 2, 10]
def baseStart_1021936 : Nat := 118140960795 + 1021936 * 2 ^ 59
def prefixEnd_1021936 : Nat := 4983230072969 + 3 ^ 40 * 1021936 * 2
def baseEnd_1021936 : Nat := 38869953046905104029645

theorem tailTrace_1021936 : CollatzResearch.WordTrace tailWord_1021936 prefixEnd_1021936 38869953046905104029645 := by
  unfold tailWord_1021936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18636534012853939809322831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24848712017138586412430441 18636534012853939809322831)
  ·
    refine ⟨27954801019280909713984247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18636534012853939809322831 27954801019280909713984247)
    ·
      refine ⟨41932201528921364570976371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27954801019280909713984247 41932201528921364570976371)
      ·
        refine ⟨62898302293382046856464557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41932201528921364570976371 62898302293382046856464557)
        ·
          refine ⟨23586863360018267571174209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62898302293382046856464557 23586863360018267571174209)
          ·
            refine ⟨17690147520013700678380657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23586863360018267571174209 17690147520013700678380657)
            ·
              refine ⟨13267610640010275508785493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17690147520013700678380657 13267610640010275508785493)
              ·
                refine ⟨38869953046905104029645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13267610640010275508785493 38869953046905104029645)
                ·
                  rfl

theorem cell22_1021936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 10].length) (baseStart_1021936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021936 prefixEnd_1021936 := by exact prefixLift 1021936
  have htrace : WordTrace (prefixWord ++ tailWord_1021936) baseStart_1021936 baseEnd_1021936 := by
    simpa [prefixWord, tailWord_1021936, baseEnd_1021936] using wordTrace_append hprefix tailTrace_1021936
  have hstable : (prefixWord ++ tailWord_1021936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021936).length < 2 ^ (prefixWord ++ tailWord_1021936).sum := by decide
  have hdescent : baseEnd_1021936 < baseStart_1021936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021951 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 9]
def baseStart_1021951 : Nat := 118140960795 + 1021951 * 2 ^ 59
def prefixEnd_1021951 : Nat := 4983230072969 + 3 ^ 40 * 1021951 * 2
def baseEnd_1021951 : Nat := 349834712228690897141759

theorem tailTrace_1021951 : CollatzResearch.WordTrace tailWord_1021951 prefixEnd_1021951 349834712228690897141759 := by
  unfold tailWord_1021951
  simp only [CollatzResearch.WordTrace]
  refine ⟨37273615120653537180441707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24849076747102358120294471 37273615120653537180441707)
  ·
    refine ⟨55910422680980305770662561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37273615120653537180441707 55910422680980305770662561)
    ·
      refine ⟨41932817010735229327996921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55910422680980305770662561 41932817010735229327996921)
      ·
        refine ⟨31449612758051421995997691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41932817010735229327996921 31449612758051421995997691)
        ·
          refine ⟨47174419137077132993996537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31449612758051421995997691 47174419137077132993996537)
          ·
            refine ⟨35380814352807849745497403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47174419137077132993996537 35380814352807849745497403)
            ·
              refine ⟨53071221529211774618246105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35380814352807849745497403 53071221529211774618246105)
              ·
                refine ⟨39803416146908830963684579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53071221529211774618246105 39803416146908830963684579)
                ·
                  refine ⟨59705124220363246445526869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39803416146908830963684579 59705124220363246445526869)
                  ·
                    refine ⟨349834712228690897141759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59705124220363246445526869 349834712228690897141759)
                    ·
                      rfl

theorem cell22_1021951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_1021951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021951 prefixEnd_1021951 := by exact prefixLift 1021951
  have htrace : WordTrace (prefixWord ++ tailWord_1021951) baseStart_1021951 baseEnd_1021951 := by
    simpa [prefixWord, tailWord_1021951, baseEnd_1021951] using wordTrace_append hprefix tailTrace_1021951
  have hstable : (prefixWord ++ tailWord_1021951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021951).length < 2 ^ (prefixWord ++ tailWord_1021951).sum := by decide
  have hdescent : baseEnd_1021951 < baseStart_1021951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021957 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_1021957 : Nat := 118140960795 + 1021957 * 2 ^ 59
def prefixEnd_1021957 : Nat := 4983230072969 + 3 ^ 40 * 1021957 * 2
def baseEnd_1021957 : Nat := 349836766151308881491741

theorem tailTrace_1021957 : CollatzResearch.WordTrace tailWord_1021957 prefixEnd_1021957 349836766151308881491741 := by
  unfold tailWord_1021957
  simp only [CollatzResearch.WordTrace]
  refine ⟨37273833958631800205160125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24849222639087866803440083 37273833958631800205160125)
  ·
    refine ⟨13977687734486925076935047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37273833958631800205160125 13977687734486925076935047)
    ·
      refine ⟨20966531601730387615402571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13977687734486925076935047 20966531601730387615402571)
      ·
        refine ⟨31449797402595581423103857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20966531601730387615402571 31449797402595581423103857)
        ·
          refine ⟨23587348051946686067327893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31449797402595581423103857 23587348051946686067327893)
          ·
            refine ⟨1105656939935000909405995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23587348051946686067327893 1105656939935000909405995)
            ·
              refine ⟨1658485409902501364108993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105656939935000909405995 1658485409902501364108993)
              ·
                refine ⟨1243864057426876023081745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658485409902501364108993 1243864057426876023081745)
                ·
                  refine ⟨932898043070157017311309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1243864057426876023081745 932898043070157017311309)
                  ·
                    refine ⟨349836766151308881491741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932898043070157017311309 349836766151308881491741)
                    ·
                      rfl

theorem cell22_1021957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_1021957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021957 prefixEnd_1021957 := by exact prefixLift 1021957
  have htrace : WordTrace (prefixWord ++ tailWord_1021957) baseStart_1021957 baseEnd_1021957 := by
    simpa [prefixWord, tailWord_1021957, baseEnd_1021957] using wordTrace_append hprefix tailTrace_1021957
  have hstable : (prefixWord ++ tailWord_1021957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021957).length < 2 ^ (prefixWord ++ tailWord_1021957).sum := by decide
  have hdescent : baseEnd_1021957 < baseStart_1021957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1021968 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_1021968 : Nat := 118140960795 + 1021968 * 2 ^ 59
def prefixEnd_1021968 : Nat := 4983230072969 + 3 ^ 40 * 1021968 * 2
def baseEnd_1021968 : Nat := 349840531676108519466707

theorem tailTrace_1021968 : CollatzResearch.WordTrace tailWord_1021968 prefixEnd_1021968 349840531676108519466707 := by
  unfold tailWord_1021968
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637117580795974541905279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24849490107727966055873705 18637117580795974541905279)
  ·
    refine ⟨27955676371193961812857919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18637117580795974541905279 27955676371193961812857919)
    ·
      refine ⟨41933514556790942719286879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27955676371193961812857919 41933514556790942719286879)
      ·
        refine ⟨62900271835186414078930319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41933514556790942719286879 62900271835186414078930319)
        ·
          refine ⟨94350407752779621118395479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62900271835186414078930319 94350407752779621118395479)
          ·
            refine ⟨141525611629169431677593219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94350407752779621118395479 141525611629169431677593219)
            ·
              refine ⟨212288417443754147516389829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141525611629169431677593219 212288417443754147516389829)
              ·
                refine ⟨39804078270703902659323093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212288417443754147516389829 39804078270703902659323093)
                ·
                  refine ⟨932908084469622718577885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 39804078270703902659323093 932908084469622718577885)
                  ·
                    refine ⟨349840531676108519466707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 932908084469622718577885 349840531676108519466707)
                    ·
                      rfl

theorem cell22_1021968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_1021968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1021968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1021968 prefixEnd_1021968 := by exact prefixLift 1021968
  have htrace : WordTrace (prefixWord ++ tailWord_1021968) baseStart_1021968 baseEnd_1021968 := by
    simpa [prefixWord, tailWord_1021968, baseEnd_1021968] using wordTrace_append hprefix tailTrace_1021968
  have hstable : (prefixWord ++ tailWord_1021968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1021968).length < 2 ^ (prefixWord ++ tailWord_1021968).sum := by decide
  have hdescent : baseEnd_1021968 < baseStart_1021968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1021968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022077 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1022077 : Nat := 118140960795 + 1022077 * 2 ^ 59
def prefixEnd_1022077 : Nat := 4983230072969 + 3 ^ 40 * 1022077 * 2
def baseEnd_1022077 : Nat := 116625948201222856163791

theorem tailTrace_1022077 : CollatzResearch.WordTrace tailWord_1022077 prefixEnd_1022077 116625948201222856163791 := by
  unfold tailWord_1022077
  simp only [CollatzResearch.WordTrace]
  refine ⟨37278210718197060699528485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24852140478798040466352323 37278210718197060699528485)
  ·
    refine ⟨6989664509661948881161591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37278210718197060699528485 6989664509661948881161591)
    ·
      refine ⟨10484496764492923321742387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6989664509661948881161591 10484496764492923321742387)
      ·
        refine ⟨15726745146739384982613581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10484496764492923321742387 15726745146739384982613581)
        ·
          refine ⟨5897529430027269368480093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15726745146739384982613581 5897529430027269368480093)
          ·
            refine ⟨2211573536260226013180035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5897529430027269368480093 2211573536260226013180035)
            ·
              refine ⟨3317360304390339019770053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211573536260226013180035 3317360304390339019770053)
              ·
                refine ⟨622005057073188566206885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3317360304390339019770053 622005057073188566206885)
                ·
                  refine ⟨116625948201222856163791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 622005057073188566206885 116625948201222856163791)
                  ·
                    rfl

theorem cell22_1022077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1022077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022077 prefixEnd_1022077 := by exact prefixLift 1022077
  have htrace : WordTrace (prefixWord ++ tailWord_1022077) baseStart_1022077 baseEnd_1022077 := by
    simpa [prefixWord, tailWord_1022077, baseEnd_1022077] using wordTrace_append hprefix tailTrace_1022077
  have hstable : (prefixWord ++ tailWord_1022077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022077).length < 2 ^ (prefixWord ++ tailWord_1022077).sum := by decide
  have hdescent : baseEnd_1022077 < baseStart_1022077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1022122 : List Nat := [3, 1, 5, 1, 2, 1, 9]
def baseStart_1022122 : Nat := 118140960795 + 1022122 * 2 ^ 59
def prefixEnd_1022122 : Nat := 4983230072969 + 3 ^ 40 * 1022122 * 2
def baseEnd_1022122 : Nat := 12959009223085313004305

theorem tailTrace_1022122 : CollatzResearch.WordTrace tailWord_1022122 prefixEnd_1022122 12959009223085313004305 := by
  unfold tailWord_1022122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9319963000758508346229155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24853234668689355589944413 9319963000758508346229155)
  ·
    refine ⟨13979944501137762519343733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9319963000758508346229155 13979944501137762519343733)
    ·
      refine ⟨1310619796981665236188475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13979944501137762519343733 1310619796981665236188475)
      ·
        refine ⟨1965929695472497854282713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310619796981665236188475 1965929695472497854282713)
        ·
          refine ⟨1474447271604373390712035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965929695472497854282713 1474447271604373390712035)
          ·
            refine ⟨2211670907406560086068053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474447271604373390712035 2211670907406560086068053)
            ·
              refine ⟨12959009223085313004305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2211670907406560086068053 12959009223085313004305)
              ·
                rfl

theorem cell22_1022122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 9].length) (baseStart_1022122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1022122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1022122 prefixEnd_1022122 := by exact prefixLift 1022122
  have htrace : WordTrace (prefixWord ++ tailWord_1022122) baseStart_1022122 baseEnd_1022122 := by
    simpa [prefixWord, tailWord_1022122, baseEnd_1022122] using wordTrace_append hprefix tailTrace_1022122
  have hstable : (prefixWord ++ tailWord_1022122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1022122).length < 2 ^ (prefixWord ++ tailWord_1022122).sum := by decide
  have hdescent : baseEnd_1022122 < baseStart_1022122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1022122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
