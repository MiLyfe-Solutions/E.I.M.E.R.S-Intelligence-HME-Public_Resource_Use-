import V185TrunkScan21Chunk028

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_351715 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 3]
def baseStart_351715 : Nat := 118140960795 + 351715 * 2 ^ 59
def prefixEnd_351715 : Nat := 4983230072969 + 3 ^ 40 * 351715 * 2
def baseEnd_351715 : Nat := 80266154842754065397777

theorem tailTrace_351715 : CollatzResearch.WordTrace tailWord_351715 prefixEnd_351715 80266154842754065397777 := by
  unfold tailWord_351715
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828099920804097984840599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8552066613869398656560399 12828099920804097984840599)
  ·
    refine ⟨19242149881206146977260899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12828099920804097984840599 19242149881206146977260899)
    ·
      refine ⟨28863224821809220465891349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19242149881206146977260899 28863224821809220465891349)
      ·
        refine ⟨1352963663522307209338657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28863224821809220465891349 1352963663522307209338657)
        ·
          refine ⟨1014722747641730407003993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352963663522307209338657 1014722747641730407003993)
          ·
            refine ⟨761042060731297805252995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1014722747641730407003993 761042060731297805252995)
            ·
              refine ⟨1141563091096946707879493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761042060731297805252995 1141563091096946707879493)
              ·
                refine ⟨214043079580677507727405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1141563091096946707879493 214043079580677507727405)
                ·
                  refine ⟨80266154842754065397777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214043079580677507727405 80266154842754065397777)
                  ·
                    rfl

theorem cell21_351715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 3].length) (baseStart_351715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351715 prefixEnd_351715 := by exact prefixLift 351715
  have htrace : WordTrace (prefixWord ++ tailWord_351715) baseStart_351715 baseEnd_351715 := by
    simpa [prefixWord, tailWord_351715, baseEnd_351715] using wordTrace_append hprefix tailTrace_351715
  have hstable : (prefixWord ++ tailWord_351715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351715).length < 2 ^ (prefixWord ++ tailWord_351715).sum := by decide
  have hdescent : baseEnd_351715 < baseStart_351715 := by decide
  rcases family_descends (prefixWord ++ tailWord_351715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351802 : List Nat := [3, 1, 1, 1, 3, 2, 3, 7]
def baseStart_351802 : Nat := 118140960795 + 351802 * 2 ^ 59
def prefixEnd_351802 : Nat := 4983230072969 + 3 ^ 40 * 351802 * 2
def baseEnd_351802 : Nat := 26762003142687082482533

theorem tailTrace_351802 : CollatzResearch.WordTrace tailWord_351802 prefixEnd_351802 26762003142687082482533 := by
  unfold tailWord_351802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207818267872227960814415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8554182047659274562171773 3207818267872227960814415)
  ·
    refine ⟨4811727401808341941221623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3207818267872227960814415 4811727401808341941221623)
    ·
      refine ⟨7217591102712512911832435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4811727401808341941221623 7217591102712512911832435)
      ·
        refine ⟨10826386654068769367748653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7217591102712512911832435 10826386654068769367748653)
        ·
          refine ⟨4059894995275788512905745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10826386654068769367748653 4059894995275788512905745)
          ·
            refine ⟨3044921246456841384679309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4059894995275788512905745 3044921246456841384679309)
            ·
              refine ⟨1141845467421315519254741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3044921246456841384679309 1141845467421315519254741)
              ·
                refine ⟨26762003142687082482533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1141845467421315519254741 26762003142687082482533)
                ·
                  rfl

theorem cell21_351802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_351802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351802 prefixEnd_351802 := by exact prefixLift 351802
  have htrace : WordTrace (prefixWord ++ tailWord_351802) baseStart_351802 baseEnd_351802 := by
    simpa [prefixWord, tailWord_351802, baseEnd_351802] using wordTrace_append hprefix tailTrace_351802
  have hstable : (prefixWord ++ tailWord_351802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351802).length < 2 ^ (prefixWord ++ tailWord_351802).sum := by decide
  have hdescent : baseEnd_351802 < baseStart_351802 := by decide
  rcases family_descends (prefixWord ++ tailWord_351802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351878 : List Nat := [6, 15]
def baseStart_351878 : Nat := 118140960795 + 351878 * 2 ^ 59
def prefixEnd_351878 : Nat := 4983230072969 + 3 ^ 40 * 351878 * 2
def baseEnd_351878 : Nat := 36718497331276636571

theorem tailTrace_351878 : CollatzResearch.WordTrace tailWord_351878 prefixEnd_351878 36718497331276636571 := by
  unfold tailWord_351878
  simp only [CollatzResearch.WordTrace]
  refine ⟨401063906850424275719509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8556030012809051215349525 401063906850424275719509)
  ·
    refine ⟨36718497331276636571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 15 401063906850424275719509 36718497331276636571)
    ·
      rfl

theorem cell21_351878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 15].length) (baseStart_351878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351878 prefixEnd_351878 := by exact prefixLift 351878
  have htrace : WordTrace (prefixWord ++ tailWord_351878) baseStart_351878 baseEnd_351878 := by
    simpa [prefixWord, tailWord_351878, baseEnd_351878] using wordTrace_append hprefix tailTrace_351878
  have hstable : (prefixWord ++ tailWord_351878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351878).length < 2 ^ (prefixWord ++ tailWord_351878).sum := by decide
  have hdescent : baseEnd_351878 < baseStart_351878 := by decide
  rcases family_descends (prefixWord ++ tailWord_351878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351895 : List Nat := [1, 1, 3, 3, 2, 4, 1, 6]
def baseStart_351895 : Nat := 118140960795 + 351895 * 2 ^ 59
def prefixEnd_351895 : Nat := 4983230072969 + 3 ^ 40 * 351895 * 2
def baseEnd_351895 : Nat := 26769077765037917465803

theorem tailTrace_351895 : CollatzResearch.WordTrace tailWord_351895 prefixEnd_351895 26769077765037917465803 := by
  unfold tailWord_351895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834665060151988726393139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8556443373434659150928759 12834665060151988726393139)
  ·
    refine ⟨19251997590227983089589709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12834665060151988726393139 19251997590227983089589709)
    ·
      refine ⟨7219499096335493658596141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19251997590227983089589709 7219499096335493658596141)
      ·
        refine ⟨2707312161125810121973553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7219499096335493658596141 2707312161125810121973553)
        ·
          refine ⟨2030484120844357591480165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2707312161125810121973553 2030484120844357591480165)
          ·
            refine ⟨380715772658317048402531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2030484120844357591480165 380715772658317048402531)
            ·
              refine ⟨571073658987475572603797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380715772658317048402531 571073658987475572603797)
              ·
                refine ⟨26769077765037917465803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 571073658987475572603797 26769077765037917465803)
                ·
                  rfl

theorem cell21_351895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 6].length) (baseStart_351895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351895 prefixEnd_351895 := by exact prefixLift 351895
  have htrace : WordTrace (prefixWord ++ tailWord_351895) baseStart_351895 baseEnd_351895 := by
    simpa [prefixWord, tailWord_351895, baseEnd_351895] using wordTrace_append hprefix tailTrace_351895
  have hstable : (prefixWord ++ tailWord_351895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351895).length < 2 ^ (prefixWord ++ tailWord_351895).sum := by decide
  have hdescent : baseEnd_351895 < baseStart_351895 := by decide
  rcases family_descends (prefixWord ++ tailWord_351895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351923 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_351923 : Nat := 118140960795 + 351923 * 2 ^ 59
def prefixEnd_351923 : Nat := 4983230072969 + 3 ^ 40 * 351923 * 2
def baseEnd_351923 : Nat := 80313623276591925930685

theorem tailTrace_351923 : CollatzResearch.WordTrace tailWord_351923 prefixEnd_351923 80313623276591925930685 := by
  unfold tailWord_351923
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835686304050549508412423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8557124202700366338941615 12835686304050549508412423)
  ·
    refine ⟨19253529456075824262618635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12835686304050549508412423 19253529456075824262618635)
    ·
      refine ⟨28880294184113736393927953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19253529456075824262618635 28880294184113736393927953)
      ·
        refine ⟨21660220638085302295445965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28880294184113736393927953 21660220638085302295445965)
        ·
          refine ⟨8122582739281988360792237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21660220638085302295445965 8122582739281988360792237)
          ·
            refine ⟨3045968527230745635297089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8122582739281988360792237 3045968527230745635297089)
            ·
              refine ⟨2284476395423059226472817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3045968527230745635297089 2284476395423059226472817)
              ·
                refine ⟨1713357296567294419854613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284476395423059226472817 1713357296567294419854613)
                ·
                  refine ⟨80313623276591925930685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1713357296567294419854613 80313623276591925930685)
                  ·
                    rfl

theorem cell21_351923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_351923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351923 prefixEnd_351923 := by exact prefixLift 351923
  have htrace : WordTrace (prefixWord ++ tailWord_351923) baseStart_351923 baseEnd_351923 := by
    simpa [prefixWord, tailWord_351923, baseEnd_351923] using wordTrace_append hprefix tailTrace_351923
  have hstable : (prefixWord ++ tailWord_351923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351923).length < 2 ^ (prefixWord ++ tailWord_351923).sum := by decide
  have hdescent : baseEnd_351923 < baseStart_351923 := by decide
  rcases family_descends (prefixWord ++ tailWord_351923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351940 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_351940 : Nat := 118140960795 + 351940 * 2 ^ 59
def prefixEnd_351940 : Nat := 4983230072969 + 3 ^ 40 * 351940 * 2
def baseEnd_351940 : Nat := 80317502908203674147317

theorem tailTrace_351940 : CollatzResearch.WordTrace tailWord_351940 prefixEnd_351940 80317502908203674147317 := by
  unfold tailWord_351940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418153172494480705890637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8557537563325974274520849 6418153172494480705890637)
  ·
    refine ⟨2406807439685430264708989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6418153172494480705890637 2406807439685430264708989)
    ·
      refine ⟨902552789882036349265871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2406807439685430264708989 902552789882036349265871)
      ·
        refine ⟨1353829184823054523898807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902552789882036349265871 1353829184823054523898807)
        ·
          refine ⟨2030743777234581785848211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353829184823054523898807 2030743777234581785848211)
          ·
            refine ⟨3046115665851872678772317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030743777234581785848211 3046115665851872678772317)
            ·
              refine ⟨1142293374694452254539619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3046115665851872678772317 1142293374694452254539619)
              ·
                refine ⟨1713440062041678381809429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142293374694452254539619 1713440062041678381809429)
                ·
                  refine ⟨80317502908203674147317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1713440062041678381809429 80317502908203674147317)
                  ·
                    rfl

theorem cell21_351940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_351940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351940 prefixEnd_351940 := by exact prefixLift 351940
  have htrace : WordTrace (prefixWord ++ tailWord_351940) baseStart_351940 baseEnd_351940 := by
    simpa [prefixWord, tailWord_351940, baseEnd_351940] using wordTrace_append hprefix tailTrace_351940
  have hstable : (prefixWord ++ tailWord_351940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351940).length < 2 ^ (prefixWord ++ tailWord_351940).sum := by decide
  have hdescent : baseEnd_351940 < baseStart_351940 := by decide
  rcases family_descends (prefixWord ++ tailWord_351940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351971 : List Nat := [1, 1, 1, 7, 2, 1, 1, 7]
def baseStart_351971 : Nat := 118140960795 + 351971 * 2 ^ 59
def prefixEnd_351971 : Nat := 4983230072969 + 3 ^ 40 * 351971 * 2
def baseEnd_351971 : Nat := 26774859176851503043529

theorem tailTrace_351971 : CollatzResearch.WordTrace tailWord_351971 prefixEnd_351971 26774859176851503043529 := by
  unfold tailWord_351971
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837437007876653706159767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558291338584435804106511 12837437007876653706159767)
  ·
    refine ⟨19256155511814980559239651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12837437007876653706159767 19256155511814980559239651)
    ·
      refine ⟨28884233267722470838859477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19256155511814980559239651 28884233267722470838859477)
      ·
        refine ⟨676974217212245410285769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28884233267722470838859477 676974217212245410285769)
        ·
          refine ⟨507730662909184057714327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676974217212245410285769 507730662909184057714327)
          ·
            refine ⟨761595994363776086571491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507730662909184057714327 761595994363776086571491)
            ·
              refine ⟨1142393991545664129857237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761595994363776086571491 1142393991545664129857237)
              ·
                refine ⟨26774859176851503043529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1142393991545664129857237 26774859176851503043529)
                ·
                  rfl

theorem cell21_351971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 7].length) (baseStart_351971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351971 prefixEnd_351971 := by exact prefixLift 351971
  have htrace : WordTrace (prefixWord ++ tailWord_351971) baseStart_351971 baseEnd_351971 := by
    simpa [prefixWord, tailWord_351971, baseEnd_351971] using wordTrace_append hprefix tailTrace_351971
  have hstable : (prefixWord ++ tailWord_351971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351971).length < 2 ^ (prefixWord ++ tailWord_351971).sum := by decide
  have hdescent : baseEnd_351971 < baseStart_351971 := by decide
  rcases family_descends (prefixWord ++ tailWord_351971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351988 : List Nat := [2, 6, 1, 1, 1, 1, 9]
def baseStart_351988 : Nat := 118140960795 + 351988 * 2 ^ 59
def prefixEnd_351988 : Nat := 4983230072969 + 3 ^ 40 * 351988 * 2
def baseEnd_351988 : Nat := 8925384129129584149691

theorem tailTrace_351988 : CollatzResearch.WordTrace tailWord_351988 prefixEnd_351988 8925384129129584149691 := by
  unfold tailWord_351988
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419028524407532804764309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8558704699210043739685745 6419028524407532804764309)
  ·
    refine ⟨300891962081603100223327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6419028524407532804764309 300891962081603100223327)
    ·
      refine ⟨451337943122404650334991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300891962081603100223327 451337943122404650334991)
      ·
        refine ⟨677006914683606975502487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451337943122404650334991 677006914683606975502487)
        ·
          refine ⟨1015510372025410463253731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677006914683606975502487 1015510372025410463253731)
          ·
            refine ⟨1523265558038115694880597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015510372025410463253731 1523265558038115694880597)
            ·
              refine ⟨8925384129129584149691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1523265558038115694880597 8925384129129584149691)
              ·
                rfl

theorem cell21_351988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 9].length) (baseStart_351988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351988 prefixEnd_351988 := by exact prefixLift 351988
  have htrace : WordTrace (prefixWord ++ tailWord_351988) baseStart_351988 baseEnd_351988 := by
    simpa [prefixWord, tailWord_351988, baseEnd_351988] using wordTrace_append hprefix tailTrace_351988
  have hstable : (prefixWord ++ tailWord_351988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351988).length < 2 ^ (prefixWord ++ tailWord_351988).sum := by decide
  have hdescent : baseEnd_351988 < baseStart_351988 := by decide
  rcases family_descends (prefixWord ++ tailWord_351988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351999 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_351999 : Nat := 118140960795 + 351999 * 2 ^ 59
def prefixEnd_351999 : Nat := 4983230072969 + 3 ^ 40 * 351999 * 2
def baseEnd_351999 : Nat := 80330967512032682663863

theorem tailTrace_351999 : CollatzResearch.WordTrace tailWord_351999 prefixEnd_351999 80330967512032682663863 := by
  unfold tailWord_351999
  simp only [CollatzResearch.WordTrace]
  refine ⟨12838458251775214488179051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558972167850142992119367 12838458251775214488179051)
  ·
    refine ⟨19257687377662821732268577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12838458251775214488179051 19257687377662821732268577)
    ·
      refine ⟨14443265533247116299201433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19257687377662821732268577 14443265533247116299201433)
      ·
        refine ⟨10832449149935337224401075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14443265533247116299201433 10832449149935337224401075)
        ·
          refine ⟨16248673724903005836601613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10832449149935337224401075 16248673724903005836601613)
          ·
            refine ⟨6093252646838627188725605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16248673724903005836601613 6093252646838627188725605)
            ·
              refine ⟨1142484871282242597886051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6093252646838627188725605 1142484871282242597886051)
              ·
                refine ⟨1713727306923363896829077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142484871282242597886051 1713727306923363896829077)
                ·
                  refine ⟨80330967512032682663863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1713727306923363896829077 80330967512032682663863)
                  ·
                    rfl

theorem cell21_351999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_351999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351999 prefixEnd_351999 := by exact prefixLift 351999
  have htrace : WordTrace (prefixWord ++ tailWord_351999) baseStart_351999 baseEnd_351999 := by
    simpa [prefixWord, tailWord_351999, baseEnd_351999] using wordTrace_append hprefix tailTrace_351999
  have hstable : (prefixWord ++ tailWord_351999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351999).length < 2 ^ (prefixWord ++ tailWord_351999).sum := by decide
  have hdescent : baseEnd_351999 < baseStart_351999 := by decide
  rcases family_descends (prefixWord ++ tailWord_351999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352053 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 3]
def baseStart_352053 : Nat := 118140960795 + 352053 * 2 ^ 59
def prefixEnd_352053 : Nat := 4983230072969 + 3 ^ 40 * 352053 * 2
def baseEnd_352053 : Nat := 80343291047740588763753

theorem tailTrace_352053 : CollatzResearch.WordTrace tailWord_352053 prefixEnd_352053 80343291047740588763753 := by
  unfold tailWord_352053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840427793579581710644813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8560285195719721140429875 12840427793579581710644813)
  ·
    refine ⟨4815160422592343141491805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12840427793579581710644813 4815160422592343141491805)
    ·
      refine ⟨1805685158472128678059427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4815160422592343141491805 1805685158472128678059427)
      ·
        refine ⟨2708527737708193017089141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805685158472128678059427 2708527737708193017089141)
        ·
          refine ⟨253924475410143095352107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2708527737708193017089141 253924475410143095352107)
          ·
            refine ⟨380886713115214643028161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253924475410143095352107 380886713115214643028161)
            ·
              refine ⟨285665034836410982271121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380886713115214643028161 285665034836410982271121)
              ·
                refine ⟨214248776127308236703341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285665034836410982271121 214248776127308236703341)
                ·
                  refine ⟨80343291047740588763753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214248776127308236703341 80343291047740588763753)
                  ·
                    rfl

theorem cell21_352053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_352053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352053 prefixEnd_352053 := by exact prefixLift 352053
  have htrace : WordTrace (prefixWord ++ tailWord_352053) baseStart_352053 baseEnd_352053 := by
    simpa [prefixWord, tailWord_352053, baseEnd_352053] using wordTrace_append hprefix tailTrace_352053
  have hstable : (prefixWord ++ tailWord_352053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352053).length < 2 ^ (prefixWord ++ tailWord_352053).sum := by decide
  have hdescent : baseEnd_352053 < baseStart_352053 := by decide
  rcases family_descends (prefixWord ++ tailWord_352053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352151 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 6]
def baseStart_352151 : Nat := 118140960795 + 352151 * 2 ^ 59
def prefixEnd_352151 : Nat := 4983230072969 + 3 ^ 40 * 352151 * 2
def baseEnd_352151 : Nat := 80365655982914196130219

theorem tailTrace_352151 : CollatzResearch.WordTrace tailWord_352151 prefixEnd_352151 80365655982914196130219 := by
  unfold tailWord_352151
  simp only [CollatzResearch.WordTrace]
  refine ⟨12844002147224544447712307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8562668098149696298474871 12844002147224544447712307)
  ·
    refine ⟨19266003220836816671568461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12844002147224544447712307 19266003220836816671568461)
    ·
      refine ⟨7224751207813806251838173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19266003220836816671568461 7224751207813806251838173)
      ·
        refine ⟨2709281702930177344439315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7224751207813806251838173 2709281702930177344439315)
        ·
          refine ⟨4063922554395266016658973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709281702930177344439315 4063922554395266016658973)
          ·
            refine ⟨1523970957898224756247115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4063922554395266016658973 1523970957898224756247115)
            ·
              refine ⟨2285956436847337134370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523970957898224756247115 2285956436847337134370673)
              ·
                refine ⟨1714467327635502850778005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285956436847337134370673 1714467327635502850778005)
                ·
                  refine ⟨80365655982914196130219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1714467327635502850778005 80365655982914196130219)
                  ·
                    rfl

theorem cell21_352151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_352151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352151 prefixEnd_352151 := by exact prefixLift 352151
  have htrace : WordTrace (prefixWord ++ tailWord_352151) baseStart_352151 baseEnd_352151 := by
    simpa [prefixWord, tailWord_352151, baseEnd_352151] using wordTrace_append hprefix tailTrace_352151
  have hstable : (prefixWord ++ tailWord_352151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352151).length < 2 ^ (prefixWord ++ tailWord_352151).sum := by decide
  have hdescent : baseEnd_352151 < baseStart_352151 := by decide
  rcases family_descends (prefixWord ++ tailWord_352151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352334 : List Nat := [4, 1, 1, 1, 1, 6, 7]
def baseStart_352334 : Nat := 118140960795 + 352334 * 2 ^ 59
def prefixEnd_352334 : Nat := 4983230072969 + 3 ^ 40 * 352334 * 2
def baseEnd_352334 : Nat := 8934157675127393842205

theorem tailTrace_352334 : CollatzResearch.WordTrace tailWord_352334 prefixEnd_352334 8934157675127393842205 := by
  unfold tailWord_352334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606334588195195837703007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8567117803707711134416037 1606334588195195837703007)
  ·
    refine ⟨2409501882292793756554511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1606334588195195837703007 2409501882292793756554511)
    ·
      refine ⟨3614252823439190634831767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2409501882292793756554511 3614252823439190634831767)
      ·
        refine ⟨5421379235158785952247651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614252823439190634831767 5421379235158785952247651)
        ·
          refine ⟨8132068852738178928371477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5421379235158785952247651 8132068852738178928371477)
          ·
            refine ⟨381190727472102137267413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8132068852738178928371477 381190727472102137267413)
            ·
              refine ⟨8934157675127393842205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 381190727472102137267413 8934157675127393842205)
              ·
                rfl

theorem cell21_352334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 7].length) (baseStart_352334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352334 prefixEnd_352334 := by exact prefixLift 352334
  have htrace : WordTrace (prefixWord ++ tailWord_352334) baseStart_352334 baseEnd_352334 := by
    simpa [prefixWord, tailWord_352334, baseEnd_352334] using wordTrace_append hprefix tailTrace_352334
  have hstable : (prefixWord ++ tailWord_352334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352334).length < 2 ^ (prefixWord ++ tailWord_352334).sum := by decide
  have hdescent : baseEnd_352334 < baseStart_352334 := by decide
  rcases family_descends (prefixWord ++ tailWord_352334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352545 : List Nat := [1, 2, 3, 2, 1, 1, 4, 7]
def baseStart_352545 : Nat := 118140960795 + 352545 * 2 ^ 59
def prefixEnd_352545 : Nat := 4983230072969 + 3 ^ 40 * 352545 * 2
def baseEnd_352545 : Nat := 26818524050285688854249

theorem tailTrace_352545 : CollatzResearch.WordTrace tailWord_352545 prefixEnd_352545 26818524050285688854249 := by
  unfold tailWord_352545
  simp only [CollatzResearch.WordTrace]
  refine ⟨12858372507797149737555089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8572248338531433158370059 12858372507797149737555089)
  ·
    refine ⟨9643779380847862303166317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12858372507797149737555089 9643779380847862303166317)
    ·
      refine ⟨3616417267817948363687369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9643779380847862303166317 3616417267817948363687369)
      ·
        refine ⟨2712312950863461272765527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3616417267817948363687369 2712312950863461272765527)
        ·
          refine ⟨4068469426295191909148291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712312950863461272765527 4068469426295191909148291)
          ·
            refine ⟨6102704139442787863722437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4068469426295191909148291 6102704139442787863722437)
            ·
              refine ⟨1144257026145522724447957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6102704139442787863722437 1144257026145522724447957)
              ·
                refine ⟨26818524050285688854249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1144257026145522724447957 26818524050285688854249)
                ·
                  rfl

theorem cell21_352545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_352545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352545 prefixEnd_352545 := by exact prefixLift 352545
  have htrace : WordTrace (prefixWord ++ tailWord_352545) baseStart_352545 baseEnd_352545 := by
    simpa [prefixWord, tailWord_352545, baseEnd_352545] using wordTrace_append hprefix tailTrace_352545
  have hstable : (prefixWord ++ tailWord_352545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352545).length < 2 ^ (prefixWord ++ tailWord_352545).sum := by decide
  have hdescent : baseEnd_352545 < baseStart_352545 := by decide
  rcases family_descends (prefixWord ++ tailWord_352545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352562 : List Nat := [3, 2, 1, 1, 6, 8]
def baseStart_352562 : Nat := 118140960795 + 352562 * 2 ^ 59
def prefixEnd_352562 : Nat := 4983230072969 + 3 ^ 40 * 352562 * 2
def baseEnd_352562 : Nat := 2979979695646993139977

theorem tailTrace_352562 : CollatzResearch.WordTrace tailWord_352562 prefixEnd_352562 2979979695646993139977 := by
  unfold tailWord_352562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214748137183890410230985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8572661699157041093949293 3214748137183890410230985)
  ·
    refine ⟨2411061102887917807673239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3214748137183890410230985 2411061102887917807673239)
    ·
      refine ⟨3616591654331876711509859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411061102887917807673239 3616591654331876711509859)
      ·
        refine ⟨5424887481497815067264789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3616591654331876711509859 5424887481497815067264789)
        ·
          refine ⟨254291600695210081278037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5424887481497815067264789 254291600695210081278037)
          ·
            refine ⟨2979979695646993139977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 254291600695210081278037 2979979695646993139977)
            ·
              rfl

theorem cell21_352562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 8].length) (baseStart_352562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352562 prefixEnd_352562 := by exact prefixLift 352562
  have htrace : WordTrace (prefixWord ++ tailWord_352562) baseStart_352562 baseEnd_352562 := by
    simpa [prefixWord, tailWord_352562, baseEnd_352562] using wordTrace_append hprefix tailTrace_352562
  have hstable : (prefixWord ++ tailWord_352562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352562).length < 2 ^ (prefixWord ++ tailWord_352562).sum := by decide
  have hdescent : baseEnd_352562 < baseStart_352562 := by decide
  rcases family_descends (prefixWord ++ tailWord_352562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352610 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_352610 : Nat := 118140960795 + 352610 * 2 ^ 59
def prefixEnd_352610 : Nat := 4983230072969 + 3 ^ 40 * 352610 * 2
def baseEnd_352610 : Nat := 80470406036431397979281

theorem tailTrace_352610 : CollatzResearch.WordTrace tailWord_352610 prefixEnd_352610 80470406036431397979281 := by
  unfold tailWord_352610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215185813140416459667821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8573828835041110559114189 3215185813140416459667821)
  ·
    refine ⟨1205694679927656172375433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3215185813140416459667821 1205694679927656172375433)
    ·
      refine ⟨904271009945742129281575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1205694679927656172375433 904271009945742129281575)
      ·
        refine ⟨1356406514918613193922363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904271009945742129281575 1356406514918613193922363)
        ·
          refine ⟨2034609772377919790883545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1356406514918613193922363 2034609772377919790883545)
          ·
            refine ⟨1525957329283439843162659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2034609772377919790883545 1525957329283439843162659)
            ·
              refine ⟨2288935993925159764743989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1525957329283439843162659 2288935993925159764743989)
              ·
                refine ⟨214587749430483727944749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2288935993925159764743989 214587749430483727944749)
                ·
                  refine ⟨80470406036431397979281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214587749430483727944749 80470406036431397979281)
                  ·
                    rfl

theorem cell21_352610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_352610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352610 prefixEnd_352610 := by exact prefixLift 352610
  have htrace : WordTrace (prefixWord ++ tailWord_352610) baseStart_352610 baseEnd_352610 := by
    simpa [prefixWord, tailWord_352610, baseEnd_352610] using wordTrace_append hprefix tailTrace_352610
  have hstable : (prefixWord ++ tailWord_352610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352610).length < 2 ^ (prefixWord ++ tailWord_352610).sum := by decide
  have hdescent : baseEnd_352610 < baseStart_352610 := by decide
  rcases family_descends (prefixWord ++ tailWord_352610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352621 : List Nat := [1, 5, 1, 1, 1, 2, 10]
def baseStart_352621 : Nat := 118140960795 + 352621 * 2 ^ 59
def prefixEnd_352621 : Nat := 4983230072969 + 3 ^ 40 * 352621 * 2
def baseEnd_352621 : Nat := 8941435154033091477325

theorem tailTrace_352621 : CollatzResearch.WordTrace tailWord_352621 prefixEnd_352621 8941435154033091477325 := by
  unfold tailWord_352621
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861144455521814717321717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8574096303681209811547811 12861144455521814717321717)
  ·
    refine ⟨1205732292705170129748911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12861144455521814717321717 1205732292705170129748911)
    ·
      refine ⟨1808598439057755194623367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205732292705170129748911 1808598439057755194623367)
      ·
        refine ⟨2712897658586632791935051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808598439057755194623367 2712897658586632791935051)
        ·
          refine ⟨4069346487879949187902577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2712897658586632791935051 4069346487879949187902577)
          ·
            refine ⟨3052009865909961890926933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4069346487879949187902577 3052009865909961890926933)
            ·
              refine ⟨8941435154033091477325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3052009865909961890926933 8941435154033091477325)
              ·
                rfl

theorem cell21_352621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 10].length) (baseStart_352621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352621 prefixEnd_352621 := by exact prefixLift 352621
  have htrace : WordTrace (prefixWord ++ tailWord_352621) baseStart_352621 baseEnd_352621 := by
    simpa [prefixWord, tailWord_352621, baseEnd_352621] using wordTrace_append hprefix tailTrace_352621
  have hstable : (prefixWord ++ tailWord_352621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352621).length < 2 ^ (prefixWord ++ tailWord_352621).sum := by decide
  have hdescent : baseEnd_352621 < baseStart_352621 := by decide
  rcases family_descends (prefixWord ++ tailWord_352621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352624 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_352624 : Nat := 118140960795 + 352624 * 2 ^ 59
def prefixEnd_352624 : Nat := 4983230072969 + 3 ^ 40 * 352624 * 2
def baseEnd_352624 : Nat := 80473601027170484745919

theorem tailTrace_352624 : CollatzResearch.WordTrace tailWord_352624 prefixEnd_352624 80473601027170484745919 := by
  unfold tailWord_352624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430626937255473114840463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8574169249673964153120617 6430626937255473114840463)
  ·
    refine ⟨9645940405883209672260695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6430626937255473114840463 9645940405883209672260695)
    ·
      refine ⟨14468910608824814508391043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9645940405883209672260695 14468910608824814508391043)
      ·
        refine ⟨21703365913237221762586565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14468910608824814508391043 21703365913237221762586565)
        ·
          refine ⟨4069381108731979080484981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21703365913237221762586565 4069381108731979080484981)
          ·
            refine ⟨381504478943623038795467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4069381108731979080484981 381504478943623038795467)
            ·
              refine ⟨572256718415434558193201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381504478943623038795467 572256718415434558193201)
              ·
                refine ⟨429192538811575918644901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572256718415434558193201 429192538811575918644901)
                ·
                  refine ⟨80473601027170484745919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429192538811575918644901 80473601027170484745919)
                  ·
                    rfl

theorem cell21_352624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_352624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352624 prefixEnd_352624 := by exact prefixLift 352624
  have htrace : WordTrace (prefixWord ++ tailWord_352624) baseStart_352624 baseEnd_352624 := by
    simpa [prefixWord, tailWord_352624, baseEnd_352624] using wordTrace_append hprefix tailTrace_352624
  have hstable : (prefixWord ++ tailWord_352624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352624).length < 2 ^ (prefixWord ++ tailWord_352624).sum := by decide
  have hdescent : baseEnd_352624 < baseStart_352624 := by decide
  rcases family_descends (prefixWord ++ tailWord_352624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352641 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 4]
def baseStart_352641 : Nat := 118140960795 + 352641 * 2 ^ 59
def prefixEnd_352641 : Nat := 4983230072969 + 3 ^ 40 * 352641 * 2
def baseEnd_352641 : Nat := 80477480658782232962551

theorem tailTrace_352641 : CollatzResearch.WordTrace tailWord_352641 prefixEnd_352641 80477480658782232962551 := by
  unfold tailWord_352641
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861873915449358133049777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8574582610299572088699851 12861873915449358133049777)
  ·
    refine ⟨9646405436587018599787333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12861873915449358133049777 9646405436587018599787333)
    ·
      refine ⟨1808701019360065987460125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9646405436587018599787333 1808701019360065987460125)
      ·
        refine ⟨678262882260024745297547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1808701019360065987460125 678262882260024745297547)
        ·
          refine ⟨1017394323390037117946321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678262882260024745297547 1017394323390037117946321)
          ·
            refine ⟨763045742542527838459741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017394323390037117946321 763045742542527838459741)
            ·
              refine ⟨286142153453447939422403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763045742542527838459741 286142153453447939422403)
              ·
                refine ⟨429213230180171909133605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286142153453447939422403 429213230180171909133605)
                ·
                  refine ⟨80477480658782232962551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429213230180171909133605 80477480658782232962551)
                  ·
                    rfl

theorem cell21_352641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_352641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352641 prefixEnd_352641 := by exact prefixLift 352641
  have htrace : WordTrace (prefixWord ++ tailWord_352641) baseStart_352641 baseEnd_352641 := by
    simpa [prefixWord, tailWord_352641, baseEnd_352641] using wordTrace_append hprefix tailTrace_352641
  have hstable : (prefixWord ++ tailWord_352641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352641).length < 2 ^ (prefixWord ++ tailWord_352641).sum := by decide
  have hdescent : baseEnd_352641 < baseStart_352641 := by decide
  rcases family_descends (prefixWord ++ tailWord_352641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352652 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_352652 : Nat := 118140960795 + 352652 * 2 ^ 59
def prefixEnd_352652 : Nat := 4983230072969 + 3 ^ 40 * 352652 * 2
def baseEnd_352652 : Nat := 80479991008648658279195

theorem tailTrace_352652 : CollatzResearch.WordTrace tailWord_352652 prefixEnd_352652 80479991008648658279195 := by
  unfold tailWord_352652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431137559204753505850105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8574850078939671341133473 6431137559204753505850105)
  ·
    refine ⟨4823353169403565129387579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6431137559204753505850105 4823353169403565129387579)
    ·
      refine ⟨7235029754105347694081369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823353169403565129387579 7235029754105347694081369)
      ·
        refine ⟨5426272315579010770561027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7235029754105347694081369 5426272315579010770561027)
        ·
          refine ⟨8139408473368516155841541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426272315579010770561027 8139408473368516155841541)
          ·
            refine ⟨1526139088756596779220289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8139408473368516155841541 1526139088756596779220289)
            ·
              refine ⟨1144604316567447584415217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1526139088756596779220289 1144604316567447584415217)
              ·
                refine ⟨858453237425585688311413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1144604316567447584415217 858453237425585688311413)
                ·
                  refine ⟨80479991008648658279195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 858453237425585688311413 80479991008648658279195)
                  ·
                    rfl

theorem cell21_352652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_352652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352652 prefixEnd_352652 := by exact prefixLift 352652
  have htrace : WordTrace (prefixWord ++ tailWord_352652) baseStart_352652 baseEnd_352652 := by
    simpa [prefixWord, tailWord_352652, baseEnd_352652] using wordTrace_append hprefix tailTrace_352652
  have hstable : (prefixWord ++ tailWord_352652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352652).length < 2 ^ (prefixWord ++ tailWord_352652).sum := by decide
  have hdescent : baseEnd_352652 < baseStart_352652 := by decide
  rcases family_descends (prefixWord ++ tailWord_352652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352692 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_352692 : Nat := 118140960795 + 352692 * 2 ^ 59
def prefixEnd_352692 : Nat := 4983230072969 + 3 ^ 40 * 352692 * 2
def baseEnd_352692 : Nat := 80489119553617477612447

theorem tailTrace_352692 : CollatzResearch.WordTrace tailWord_352692 prefixEnd_352692 80489119553617477612447 := by
  unfold tailWord_352692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6431867019132296921578165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8575822692176395895437553 6431867019132296921578165)
  ·
    refine ⟨602987533043652836397953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6431867019132296921578165 602987533043652836397953)
    ·
      refine ⟨452240649782739627298465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 602987533043652836397953 452240649782739627298465)
      ·
        refine ⟨339180487337054720473849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 452240649782739627298465 339180487337054720473849)
        ·
          refine ⟨254385365502791040355387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339180487337054720473849 254385365502791040355387)
          ·
            refine ⟨381578048254186560533081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254385365502791040355387 381578048254186560533081)
            ·
              refine ⟨286183536190639920399811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381578048254186560533081 286183536190639920399811)
              ·
                refine ⟨429275304285959880599717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286183536190639920399811 429275304285959880599717)
                ·
                  refine ⟨80489119553617477612447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429275304285959880599717 80489119553617477612447)
                  ·
                    rfl

theorem cell21_352692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_352692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352692 prefixEnd_352692 := by exact prefixLift 352692
  have htrace : WordTrace (prefixWord ++ tailWord_352692) baseStart_352692 baseEnd_352692 := by
    simpa [prefixWord, tailWord_352692, baseEnd_352692] using wordTrace_append hprefix tailTrace_352692
  have hstable : (prefixWord ++ tailWord_352692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352692).length < 2 ^ (prefixWord ++ tailWord_352692).sum := by decide
  have hdescent : baseEnd_352692 < baseStart_352692 := by decide
  rcases family_descends (prefixWord ++ tailWord_352692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352697 : List Nat := [1, 2, 1, 4, 3, 1, 1, 8]
def baseStart_352697 : Nat := 118140960795 + 352697 * 2 ^ 59
def prefixEnd_352697 : Nat := 4983230072969 + 3 ^ 40 * 352697 * 2
def baseEnd_352697 : Nat := 26830086873912860009701

theorem tailTrace_352697 : CollatzResearch.WordTrace tailWord_352697 prefixEnd_352697 26830086873912860009701 := by
  unfold tailWord_352697
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863916403246479697088345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8575944268830986464725563 12863916403246479697088345)
  ·
    refine ⟨9647937302434859772816259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12863916403246479697088345 9647937302434859772816259)
    ·
      refine ⟨14471905953652289659224389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647937302434859772816259 14471905953652289659224389)
      ·
        refine ⟨2713482366309804311104573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14471905953652289659224389 2713482366309804311104573)
        ·
          refine ⟨1017555887366176616664215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2713482366309804311104573 1017555887366176616664215)
          ·
            refine ⟨1526333831049264924996323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017555887366176616664215 1526333831049264924996323)
            ·
              refine ⟨2289500746573897387494485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1526333831049264924996323 2289500746573897387494485)
              ·
                refine ⟨26830086873912860009701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2289500746573897387494485 26830086873912860009701)
                ·
                  rfl

theorem cell21_352697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_352697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352697 prefixEnd_352697 := by exact prefixLift 352697
  have htrace : WordTrace (prefixWord ++ tailWord_352697) baseStart_352697 baseEnd_352697 := by
    simpa [prefixWord, tailWord_352697, baseEnd_352697] using wordTrace_append hprefix tailTrace_352697
  have hstable : (prefixWord ++ tailWord_352697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352697).length < 2 ^ (prefixWord ++ tailWord_352697).sum := by decide
  have hdescent : baseEnd_352697 < baseStart_352697 := by decide
  rcases family_descends (prefixWord ++ tailWord_352697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352700 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_352700 : Nat := 118140960795 + 352700 * 2 ^ 59
def prefixEnd_352700 : Nat := 4983230072969 + 3 ^ 40 * 352700 * 2
def baseEnd_352700 : Nat := 80490945262611241479097

theorem tailTrace_352700 : CollatzResearch.WordTrace tailWord_352700 prefixEnd_352700 80490945262611241479097 := by
  unfold tailWord_352700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6432012911117805604723777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8576017214823740806298369 6432012911117805604723777)
  ·
    refine ⟨4824009683338354203542833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6432012911117805604723777 4824009683338354203542833)
    ·
      refine ⟨3618007262503765652657125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4824009683338354203542833 3618007262503765652657125)
      ·
        refine ⟨678376361719456059873211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3618007262503765652657125 678376361719456059873211)
        ·
          refine ⟨1017564542579184089809817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678376361719456059873211 1017564542579184089809817)
          ·
            refine ⟨763173406934388067357363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017564542579184089809817 763173406934388067357363)
            ·
              refine ⟨1144760110401582101036045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763173406934388067357363 1144760110401582101036045)
              ·
                refine ⟨429285041400593287888517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1144760110401582101036045 429285041400593287888517)
                ·
                  refine ⟨80490945262611241479097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429285041400593287888517 80490945262611241479097)
                  ·
                    rfl

theorem cell21_352700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_352700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352700 prefixEnd_352700 := by exact prefixLift 352700
  have htrace : WordTrace (prefixWord ++ tailWord_352700) baseStart_352700 baseEnd_352700 := by
    simpa [prefixWord, tailWord_352700, baseEnd_352700] using wordTrace_append hprefix tailTrace_352700
  have hstable : (prefixWord ++ tailWord_352700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352700).length < 2 ^ (prefixWord ++ tailWord_352700).sum := by decide
  have hdescent : baseEnd_352700 < baseStart_352700 := by decide
  rcases family_descends (prefixWord ++ tailWord_352700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352787 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_352787 : Nat := 118140960795 + 352787 * 2 ^ 59
def prefixEnd_352787 : Nat := 4983230072969 + 3 ^ 40 * 352787 * 2
def baseEnd_352787 : Nat := 80510799847918423528919

theorem tailTrace_352787 : CollatzResearch.WordTrace tailWord_352787 prefixEnd_352787 80510799847918423528919 := by
  unfold tailWord_352787
  simp only [CollatzResearch.WordTrace]
  refine ⟨12867198972920425067864615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8578132648613616711909743 12867198972920425067864615)
  ·
    refine ⟨19300798459380637601796923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12867198972920425067864615 19300798459380637601796923)
    ·
      refine ⟨28951197689070956402695385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19300798459380637601796923 28951197689070956402695385)
      ·
        refine ⟨21713398266803217302021539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28951197689070956402695385 21713398266803217302021539)
        ·
          refine ⟨32570097400204825953032309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21713398266803217302021539 32570097400204825953032309)
          ·
            refine ⟨3053446631269202433096779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32570097400204825953032309 3053446631269202433096779)
            ·
              refine ⟨4580169946903803649645169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053446631269202433096779 4580169946903803649645169)
              ·
                refine ⟨3435127460177852737233877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4580169946903803649645169 3435127460177852737233877)
                ·
                  refine ⟨80510799847918423528919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3435127460177852737233877 80510799847918423528919)
                  ·
                    rfl

theorem cell21_352787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_352787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352787 prefixEnd_352787 := by exact prefixLift 352787
  have htrace : WordTrace (prefixWord ++ tailWord_352787) baseStart_352787 baseEnd_352787 := by
    simpa [prefixWord, tailWord_352787, baseEnd_352787] using wordTrace_append hprefix tailTrace_352787
  have hstable : (prefixWord ++ tailWord_352787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352787).length < 2 ^ (prefixWord ++ tailWord_352787).sum := by decide
  have hdescent : baseEnd_352787 < baseStart_352787 := by decide
  rcases family_descends (prefixWord ++ tailWord_352787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352849 : List Nat := [1, 2, 2, 1, 3, 5, 7]
def baseStart_352849 : Nat := 118140960795 + 352849 * 2 ^ 59
def prefixEnd_352849 : Nat := 4983230072969 + 3 ^ 40 * 352849 * 2
def baseEnd_352849 : Nat := 8947216565846677055051

theorem tailTrace_352849 : CollatzResearch.WordTrace tailWord_352849 prefixEnd_352849 8947216565846677055051 := by
  unfold tailWord_352849
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869460298695809656621601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8579640199130539771081067 12869460298695809656621601)
  ·
    refine ⟨9652095224021857242466201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12869460298695809656621601 9652095224021857242466201)
    ·
      refine ⟨7239071418016392931849651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9652095224021857242466201 7239071418016392931849651)
      ·
        refine ⟨10858607127024589397774477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7239071418016392931849651 10858607127024589397774477)
        ·
          refine ⟨4071977672634221024165429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10858607127024589397774477 4071977672634221024165429)
          ·
            refine ⟨381747906809458221015509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4071977672634221024165429 381747906809458221015509)
            ·
              refine ⟨8947216565846677055051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 381747906809458221015509 8947216565846677055051)
              ·
                rfl

theorem cell21_352849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 7].length) (baseStart_352849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352849 prefixEnd_352849 := by exact prefixLift 352849
  have htrace : WordTrace (prefixWord ++ tailWord_352849) baseStart_352849 baseEnd_352849 := by
    simpa [prefixWord, tailWord_352849, baseEnd_352849] using wordTrace_append hprefix tailTrace_352849
  have hstable : (prefixWord ++ tailWord_352849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352849).length < 2 ^ (prefixWord ++ tailWord_352849).sum := by decide
  have hdescent : baseEnd_352849 < baseStart_352849 := by decide
  rcases family_descends (prefixWord ++ tailWord_352849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352869 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 4]
def baseStart_352869 : Nat := 118140960795 + 352869 * 2 ^ 59
def prefixEnd_352869 : Nat := 4983230072969 + 3 ^ 40 * 352869 * 2
def baseEnd_352869 : Nat := 80529513365104503162085

theorem tailTrace_352869 : CollatzResearch.WordTrace tailWord_352869 prefixEnd_352869 80529513365104503162085 := by
  unfold tailWord_352869
  simp only [CollatzResearch.WordTrace]
  refine ⟨12870189758623353072349661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8580126505748902048233107 12870189758623353072349661)
  ·
    refine ⟨4826321159483757402131123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12870189758623353072349661 4826321159483757402131123)
    ·
      refine ⟨7239481739225636103196685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826321159483757402131123 7239481739225636103196685)
      ·
        refine ⟨2714805652209613538698757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7239481739225636103196685 2714805652209613538698757)
        ·
          refine ⟨509026059789302538506017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2714805652209613538698757 509026059789302538506017)
          ·
            refine ⟨381769544841976903879513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509026059789302538506017 381769544841976903879513)
            ·
              refine ⟨286327158631482677909635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381769544841976903879513 286327158631482677909635)
              ·
                refine ⟨429490737947224016864453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286327158631482677909635 429490737947224016864453)
                ·
                  refine ⟨80529513365104503162085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 429490737947224016864453 80529513365104503162085)
                  ·
                    rfl

theorem cell21_352869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_352869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352869 prefixEnd_352869 := by exact prefixLift 352869
  have htrace : WordTrace (prefixWord ++ tailWord_352869) baseStart_352869 baseEnd_352869 := by
    simpa [prefixWord, tailWord_352869, baseEnd_352869] using wordTrace_append hprefix tailTrace_352869
  have hstable : (prefixWord ++ tailWord_352869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352869).length < 2 ^ (prefixWord ++ tailWord_352869).sum := by decide
  have hdescent : baseEnd_352869 < baseStart_352869 := by decide
  rcases family_descends (prefixWord ++ tailWord_352869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352897 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 3]
def baseStart_352897 : Nat := 118140960795 + 352897 * 2 ^ 59
def prefixEnd_352897 : Nat := 4983230072969 + 3 ^ 40 * 352897 * 2
def baseEnd_352897 : Nat := 80535903346582676695361

theorem tailTrace_352897 : CollatzResearch.WordTrace tailWord_352897 prefixEnd_352897 80535903346582676695361 := by
  unfold tailWord_352897
  simp only [CollatzResearch.WordTrace]
  refine ⟨12871211002521913854368945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8580807335014609236245963 12871211002521913854368945)
  ·
    refine ⟨9653408251891435390776709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12871211002521913854368945 9653408251891435390776709)
    ·
      refine ⟨1810014047229644135770633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9653408251891435390776709 1810014047229644135770633)
      ·
        refine ⟨1357510535422233101827975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1810014047229644135770633 1357510535422233101827975)
        ·
          refine ⟨2036265803133349652741963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357510535422233101827975 2036265803133349652741963)
          ·
            refine ⟨3054398704700024479112945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036265803133349652741963 3054398704700024479112945)
            ·
              refine ⟨2290799028525018359334709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054398704700024479112945 2290799028525018359334709)
              ·
                refine ⟨214762408924220471187629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2290799028525018359334709 214762408924220471187629)
                ·
                  refine ⟨80535903346582676695361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214762408924220471187629 80535903346582676695361)
                  ·
                    rfl

theorem cell21_352897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_352897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352897 prefixEnd_352897 := by exact prefixLift 352897
  have htrace : WordTrace (prefixWord ++ tailWord_352897) baseStart_352897 baseEnd_352897 := by
    simpa [prefixWord, tailWord_352897, baseEnd_352897] using wordTrace_append hprefix tailTrace_352897
  have hstable : (prefixWord ++ tailWord_352897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352897).length < 2 ^ (prefixWord ++ tailWord_352897).sum := by decide
  have hdescent : baseEnd_352897 < baseStart_352897 := by decide
  rcases family_descends (prefixWord ++ tailWord_352897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352914 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 3]
def baseStart_352914 : Nat := 118140960795 + 352914 * 2 ^ 59
def prefixEnd_352914 : Nat := 4983230072969 + 3 ^ 40 * 352914 * 2
def baseEnd_352914 : Nat := 80539782978194424911993

theorem tailTrace_352914 : CollatzResearch.WordTrace tailWord_352914 prefixEnd_352914 80539782978194424911993 := by
  unfold tailWord_352914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217957760865081439434449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8581220695640217171825197 3217957760865081439434449)
  ·
    refine ⟨2413468320648811079575837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3217957760865081439434449 2413468320648811079575837)
    ·
      refine ⟨905050620243304154840939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2413468320648811079575837 905050620243304154840939)
      ·
        refine ⟨1357575930364956232261409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905050620243304154840939 1357575930364956232261409)
        ·
          refine ⟨1018181947773717174196057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357575930364956232261409 1018181947773717174196057)
          ·
            refine ⟨763636460830287880647043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018181947773717174196057 763636460830287880647043)
            ·
              refine ⟨1145454691245431820970565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763636460830287880647043 1145454691245431820970565)
              ·
                refine ⟨214772754608518466431981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1145454691245431820970565 214772754608518466431981)
                ·
                  refine ⟨80539782978194424911993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214772754608518466431981 80539782978194424911993)
                  ·
                    rfl

theorem cell21_352914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_352914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352914 prefixEnd_352914 := by exact prefixLift 352914
  have htrace : WordTrace (prefixWord ++ tailWord_352914) baseStart_352914 baseEnd_352914 := by
    simpa [prefixWord, tailWord_352914, baseEnd_352914] using wordTrace_append hprefix tailTrace_352914
  have hstable : (prefixWord ++ tailWord_352914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352914).length < 2 ^ (prefixWord ++ tailWord_352914).sum := by decide
  have hdescent : baseEnd_352914 < baseStart_352914 := by decide
  rcases family_descends (prefixWord ++ tailWord_352914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352925 : List Nat := [1, 4, 2, 1, 1, 1, 5, 6]
def baseStart_352925 : Nat := 118140960795 + 352925 * 2 ^ 59
def prefixEnd_352925 : Nat := 4983230072969 + 3 ^ 40 * 352925 * 2
def baseEnd_352925 : Nat := 26847431109353616742879

theorem tailTrace_352925 : CollatzResearch.WordTrace tailWord_352925 prefixEnd_352925 26847431109353616742879 := by
  unfold tailWord_352925
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872232246420474636388229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8581488164280316424258819 12872232246420474636388229)
  ·
    refine ⟨2413543546203838994322793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12872232246420474636388229 2413543546203838994322793)
    ·
      refine ⟨1810157659652879245742095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2413543546203838994322793 1810157659652879245742095)
      ·
        refine ⟨2715236489479318868613143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810157659652879245742095 2715236489479318868613143)
        ·
          refine ⟨4072854734218978302919715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715236489479318868613143 4072854734218978302919715)
          ·
            refine ⟨6109282101328467454379573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072854734218978302919715 6109282101328467454379573)
            ·
              refine ⟨572745196999543823848085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6109282101328467454379573 572745196999543823848085)
              ·
                refine ⟨26847431109353616742879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 572745196999543823848085 26847431109353616742879)
                ·
                  rfl

theorem cell21_352925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 6].length) (baseStart_352925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_352925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_352925 prefixEnd_352925 := by exact prefixLift 352925
  have htrace : WordTrace (prefixWord ++ tailWord_352925) baseStart_352925 baseEnd_352925 := by
    simpa [prefixWord, tailWord_352925, baseEnd_352925] using wordTrace_append hprefix tailTrace_352925
  have hstable : (prefixWord ++ tailWord_352925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352925).length < 2 ^ (prefixWord ++ tailWord_352925).sum := by decide
  have hdescent : baseEnd_352925 < baseStart_352925 := by decide
  rcases family_descends (prefixWord ++ tailWord_352925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353001 : List Nat := [1, 2, 1, 1, 1, 2, 8, 5]
def baseStart_353001 : Nat := 118140960795 + 353001 * 2 ^ 59
def prefixEnd_353001 : Nat := 4983230072969 + 3 ^ 40 * 353001 * 2
def baseEnd_353001 : Nat := 26853212521167202320605

theorem tailTrace_353001 : CollatzResearch.WordTrace tailWord_353001 prefixEnd_353001 26853212521167202320605 := by
  unfold tailWord_353001
  simp only [CollatzResearch.WordTrace]
  refine ⟨12875004194145139616154857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8583336129430093077436571 12875004194145139616154857)
  ·
    refine ⟨9656253145608854712116143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12875004194145139616154857 9656253145608854712116143)
    ·
      refine ⟨14484379718413282068174215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656253145608854712116143 14484379718413282068174215)
      ·
        refine ⟨21726569577619923102261323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14484379718413282068174215 21726569577619923102261323)
        ·
          refine ⟨32589854366429884653391985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21726569577619923102261323 32589854366429884653391985)
          ·
            refine ⟨24442390774822413490043989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32589854366429884653391985 24442390774822413490043989)
            ·
              refine ⟨286434266892450158086453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 24442390774822413490043989 286434266892450158086453)
              ·
                refine ⟨26853212521167202320605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286434266892450158086453 26853212521167202320605)
                ·
                  rfl

theorem cell21_353001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 5].length) (baseStart_353001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353001 prefixEnd_353001 := by exact prefixLift 353001
  have htrace : WordTrace (prefixWord ++ tailWord_353001) baseStart_353001 baseEnd_353001 := by
    simpa [prefixWord, tailWord_353001, baseEnd_353001] using wordTrace_append hprefix tailTrace_353001
  have hstable : (prefixWord ++ tailWord_353001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353001).length < 2 ^ (prefixWord ++ tailWord_353001).sum := by decide
  have hdescent : baseEnd_353001 < baseStart_353001 := by decide
  rcases family_descends (prefixWord ++ tailWord_353001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353032 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_353032 : Nat := 118140960795 + 353032 * 2 ^ 59
def prefixEnd_353032 : Nat := 4983230072969 + 3 ^ 40 * 353032 * 2
def baseEnd_353032 : Nat := 80566712185852441945085

theorem tailTrace_353032 : CollatzResearch.WordTrace tailWord_353032 prefixEnd_353032 80566712185852441945085 := by
  unfold tailWord_353032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438067428516415955266675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8584089904688554607022233 6438067428516415955266675)
  ·
    refine ⟨9657101142774623932900013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6438067428516415955266675 9657101142774623932900013)
    ·
      refine ⟨3621412928540483974837505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9657101142774623932900013 3621412928540483974837505)
      ·
        refine ⟨2716059696405362981128129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3621412928540483974837505 2716059696405362981128129)
        ·
          refine ⟨2037044772304022235846097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716059696405362981128129 2037044772304022235846097)
          ·
            refine ⟨1527783579228016676884573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2037044772304022235846097 1527783579228016676884573)
            ·
              refine ⟨572918842210506253831715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527783579228016676884573 572918842210506253831715)
              ·
                refine ⟨859378263315759380747573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572918842210506253831715 859378263315759380747573)
                ·
                  refine ⟨80566712185852441945085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 859378263315759380747573 80566712185852441945085)
                  ·
                    rfl

theorem cell21_353032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_353032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353032 prefixEnd_353032 := by exact prefixLift 353032
  have htrace : WordTrace (prefixWord ++ tailWord_353032) baseStart_353032 baseEnd_353032 := by
    simpa [prefixWord, tailWord_353032, baseEnd_353032] using wordTrace_append hprefix tailTrace_353032
  have hstable : (prefixWord ++ tailWord_353032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353032).length < 2 ^ (prefixWord ++ tailWord_353032).sum := by decide
  have hdescent : baseEnd_353032 < baseStart_353032 := by decide
  rcases family_descends (prefixWord ++ tailWord_353032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353091 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_353091 : Nat := 118140960795 + 353091 * 2 ^ 59
def prefixEnd_353091 : Nat := 4983230072969 + 3 ^ 40 * 353091 * 2
def baseEnd_353091 : Nat := 80580176789681450461631

theorem tailTrace_353091 : CollatzResearch.WordTrace tailWord_353091 prefixEnd_353091 80580176789681450461631 := by
  unfold tailWord_353091
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878286763819084986931127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8585524509212723324620751 12878286763819084986931127)
  ·
    refine ⟨19317430145728627480396691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12878286763819084986931127 19317430145728627480396691)
    ·
      refine ⟨28976145218592941220595037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19317430145728627480396691 28976145218592941220595037)
      ·
        refine ⟨10866054456972352957723139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28976145218592941220595037 10866054456972352957723139)
        ·
          refine ⟨16299081685458529436584709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866054456972352957723139 16299081685458529436584709)
          ·
            refine ⟨3056077816023474269359633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16299081685458529436584709 3056077816023474269359633)
            ·
              refine ⟨2292058362017605702019725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056077816023474269359633 2292058362017605702019725)
              ·
                refine ⟨859521885756602138257397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2292058362017605702019725 859521885756602138257397)
                ·
                  refine ⟨80580176789681450461631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 859521885756602138257397 80580176789681450461631)
                  ·
                    rfl

theorem cell21_353091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_353091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353091 prefixEnd_353091 := by exact prefixLift 353091
  have htrace : WordTrace (prefixWord ++ tailWord_353091) baseStart_353091 baseEnd_353091 := by
    simpa [prefixWord, tailWord_353091, baseEnd_353091] using wordTrace_append hprefix tailTrace_353091
  have hstable : (prefixWord ++ tailWord_353091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353091).length < 2 ^ (prefixWord ++ tailWord_353091).sum := by decide
  have hdescent : baseEnd_353091 < baseStart_353091 := by decide
  rcases family_descends (prefixWord ++ tailWord_353091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353142 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_353142 : Nat := 118140960795 + 353142 * 2 ^ 59
def prefixEnd_353142 : Nat := 4983230072969 + 3 ^ 40 * 353142 * 2
def baseEnd_353142 : Nat := 80591815684516695111527

theorem tailTrace_353142 : CollatzResearch.WordTrace tailWord_353142 prefixEnd_353142 80591815684516695111527 := by
  unfold tailWord_353142
  simp only [CollatzResearch.WordTrace]
  refine ⟨805009180414645043564855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8586764591089547131358453 805009180414645043564855)
  ·
    refine ⟨1207513770621967565347283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 805009180414645043564855 1207513770621967565347283)
    ·
      refine ⟨1811270655932951348020925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1207513770621967565347283 1811270655932951348020925)
      ·
        refine ⟨679226495974856755507847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1811270655932951348020925 679226495974856755507847)
        ·
          refine ⟨1018839743962285133261771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679226495974856755507847 1018839743962285133261771)
          ·
            refine ⟨1528259615943427699892657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018839743962285133261771 1528259615943427699892657)
            ·
              refine ⟨1146194711957570774919493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528259615943427699892657 1146194711957570774919493)
              ·
                refine ⟨214911508492044520297405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1146194711957570774919493 214911508492044520297405)
                ·
                  refine ⟨80591815684516695111527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 214911508492044520297405 80591815684516695111527)
                  ·
                    rfl

theorem cell21_353142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_353142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353142 prefixEnd_353142 := by exact prefixLift 353142
  have htrace : WordTrace (prefixWord ++ tailWord_353142) baseStart_353142 baseEnd_353142 := by
    simpa [prefixWord, tailWord_353142, baseEnd_353142] using wordTrace_append hprefix tailTrace_353142
  have hstable : (prefixWord ++ tailWord_353142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353142).length < 2 ^ (prefixWord ++ tailWord_353142).sum := by decide
  have hdescent : baseEnd_353142 < baseStart_353142 := by decide
  rcases family_descends (prefixWord ++ tailWord_353142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353170 : List Nat := [3, 2, 3, 2, 2, 1, 1, 7]
def baseStart_353170 : Nat := 118140960795 + 353170 * 2 ^ 59
def prefixEnd_353170 : Nat := 4983230072969 + 3 ^ 40 * 353170 * 2
def baseEnd_353170 : Nat := 26866068555331622881601

theorem tailTrace_353170 : CollatzResearch.WordTrace tailWord_353170 prefixEnd_353170 26866068555331622881601 := by
  unfold tailWord_353170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220292032633220369764241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8587445420355254319371309 3220292032633220369764241)
  ·
    refine ⟨2415219024474915277323181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3220292032633220369764241 2415219024474915277323181)
    ·
      refine ⟨905707134178093228996193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2415219024474915277323181 905707134178093228996193)
      ·
        refine ⟨679280350633569921747145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 905707134178093228996193 679280350633569921747145)
        ·
          refine ⟨509460262975177441310359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 679280350633569921747145 509460262975177441310359)
          ·
            refine ⟨764190394462766161965539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509460262975177441310359 764190394462766161965539)
            ·
              refine ⟨1146285591694149242948309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764190394462766161965539 1146285591694149242948309)
              ·
                refine ⟨26866068555331622881601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1146285591694149242948309 26866068555331622881601)
                ·
                  rfl

theorem cell21_353170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_353170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353170 prefixEnd_353170 := by exact prefixLift 353170
  have htrace : WordTrace (prefixWord ++ tailWord_353170) baseStart_353170 baseEnd_353170 := by
    simpa [prefixWord, tailWord_353170, baseEnd_353170] using wordTrace_append hprefix tailTrace_353170
  have hstable : (prefixWord ++ tailWord_353170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353170).length < 2 ^ (prefixWord ++ tailWord_353170).sum := by decide
  have hdescent : baseEnd_353170 < baseStart_353170 := by decide
  rcases family_descends (prefixWord ++ tailWord_353170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353201 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 5]
def baseStart_353201 : Nat := 118140960795 + 353201 * 2 ^ 59
def prefixEnd_353201 : Nat := 4983230072969 + 3 ^ 40 * 353201 * 2
def baseEnd_353201 : Nat := 80605280288345703628073

theorem tailTrace_353201 : CollatzResearch.WordTrace tailWord_353201 prefixEnd_353201 80605280288345703628073 := by
  unfold tailWord_353201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12882298793420573773435457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8588199195613715848956971 12882298793420573773435457)
  ·
    refine ⟨9661724095065430330076593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12882298793420573773435457 9661724095065430330076593)
    ·
      refine ⟨7246293071299072747557445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9661724095065430330076593 7246293071299072747557445)
      ·
        refine ⟨1358679950868576140167021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7246293071299072747557445 1358679950868576140167021)
        ·
          refine ⟨509504981575716052562633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1358679950868576140167021 509504981575716052562633)
          ·
            refine ⟨382128736181787039421975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509504981575716052562633 382128736181787039421975)
            ·
              refine ⟨573193104272680559132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382128736181787039421975 573193104272680559132963)
              ·
                refine ⟨859789656409020838699445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573193104272680559132963 859789656409020838699445)
                ·
                  refine ⟨80605280288345703628073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 859789656409020838699445 80605280288345703628073)
                  ·
                    rfl

theorem cell21_353201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_353201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353201 prefixEnd_353201 := by exact prefixLift 353201
  have htrace : WordTrace (prefixWord ++ tailWord_353201) baseStart_353201 baseEnd_353201 := by
    simpa [prefixWord, tailWord_353201, baseEnd_353201] using wordTrace_append hprefix tailTrace_353201
  have hstable : (prefixWord ++ tailWord_353201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353201).length < 2 ^ (prefixWord ++ tailWord_353201).sum := by decide
  have hdescent : baseEnd_353201 < baseStart_353201 := by decide
  rcases family_descends (prefixWord ++ tailWord_353201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353308 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_353308 : Nat := 118140960795 + 353308 * 2 ^ 59
def prefixEnd_353308 : Nat := 4983230072969 + 3 ^ 40 * 353308 * 2
def baseEnd_353308 : Nat := 80629699146137295344521

theorem tailTrace_353308 : CollatzResearch.WordTrace tailWord_353308 prefixEnd_353308 80629699146137295344521 := by
  unfold tailWord_353308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443100702016465523790289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8590800936021954031720385 6443100702016465523790289)
  ·
    refine ⟨4832325526512349142842717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6443100702016465523790289 4832325526512349142842717)
    ·
      refine ⟨1812122072442130928566019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4832325526512349142842717 1812122072442130928566019)
      ·
        refine ⟨2718183108663196392849029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812122072442130928566019 2718183108663196392849029)
        ·
          refine ⟨509659332874349323659193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2718183108663196392849029 509659332874349323659193)
          ·
            refine ⟨382244499655761992744395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509659332874349323659193 382244499655761992744395)
            ·
              refine ⟨573366749483642989116593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382244499655761992744395 573366749483642989116593)
              ·
                refine ⟨430025062112732241837445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573366749483642989116593 430025062112732241837445)
                ·
                  refine ⟨80629699146137295344521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430025062112732241837445 80629699146137295344521)
                  ·
                    rfl

theorem cell21_353308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_353308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353308 prefixEnd_353308 := by exact prefixLift 353308
  have htrace : WordTrace (prefixWord ++ tailWord_353308) baseStart_353308 baseEnd_353308 := by
    simpa [prefixWord, tailWord_353308, baseEnd_353308] using wordTrace_append hprefix tailTrace_353308
  have hstable : (prefixWord ++ tailWord_353308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353308).length < 2 ^ (prefixWord ++ tailWord_353308).sum := by decide
  have hdescent : baseEnd_353308 < baseStart_353308 := by decide
  rcases family_descends (prefixWord ++ tailWord_353308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353364 : List Nat := [2, 4, 1, 1, 1, 1, 11]
def baseStart_353364 : Nat := 118140960795 + 353364 * 2 ^ 59
def prefixEnd_353364 : Nat := 4983230072969 + 3 ^ 40 * 353364 * 2
def baseEnd_353364 : Nat := 8960275456565960267897

theorem tailTrace_353364 : CollatzResearch.WordTrace tailWord_353364 prefixEnd_353364 8960275456565960267897 := by
  unfold tailWord_353364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444121945915026305809573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8592162594553368407746097 6444121945915026305809573)
  ·
    refine ⟨1208272864859067432339295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6444121945915026305809573 1208272864859067432339295)
    ·
      refine ⟨1812409297288601148508943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1208272864859067432339295 1812409297288601148508943)
      ·
        refine ⟨2718613945932901722763415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1812409297288601148508943 2718613945932901722763415)
        ·
          refine ⟨4077920918899352584145123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718613945932901722763415 4077920918899352584145123)
          ·
            refine ⟨6116881378349028876217685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077920918899352584145123 6116881378349028876217685)
            ·
              refine ⟨8960275456565960267897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6116881378349028876217685 8960275456565960267897)
              ·
                rfl

theorem cell21_353364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 11].length) (baseStart_353364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353364 prefixEnd_353364 := by exact prefixLift 353364
  have htrace : WordTrace (prefixWord ++ tailWord_353364) baseStart_353364 baseEnd_353364 := by
    simpa [prefixWord, tailWord_353364, baseEnd_353364] using wordTrace_append hprefix tailTrace_353364
  have hstable : (prefixWord ++ tailWord_353364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353364).length < 2 ^ (prefixWord ++ tailWord_353364).sum := by decide
  have hdescent : baseEnd_353364 < baseStart_353364 := by decide
  rcases family_descends (prefixWord ++ tailWord_353364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353384 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_353384 : Nat := 118140960795 + 353384 * 2 ^ 59
def prefixEnd_353384 : Nat := 4983230072969 + 3 ^ 40 * 353384 * 2
def baseEnd_353384 : Nat := 80647043381578052077699

theorem tailTrace_353384 : CollatzResearch.WordTrace tailWord_353384 prefixEnd_353384 80647043381578052077699 := by
  unfold tailWord_353384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444486675878798013673603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8592648901171730684898137 6444486675878798013673603)
  ·
    refine ⟨9666730013818197020510405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6444486675878798013673603 9666730013818197020510405)
    ·
      refine ⟨1812511877590911941345701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9666730013818197020510405 1812511877590911941345701)
      ·
        refine ⟨339845977048295989002319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1812511877590911941345701 339845977048295989002319)
        ·
          refine ⟨509768965572443983503479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339845977048295989002319 509768965572443983503479)
          ·
            refine ⟨764653448358665975255219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509768965572443983503479 764653448358665975255219)
            ·
              refine ⟨1146980172537998962882829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764653448358665975255219 1146980172537998962882829)
              ·
                refine ⟨430117564701749611081061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1146980172537998962882829 430117564701749611081061)
                ·
                  refine ⟨80647043381578052077699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430117564701749611081061 80647043381578052077699)
                  ·
                    rfl

theorem cell21_353384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_353384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353384 prefixEnd_353384 := by exact prefixLift 353384
  have htrace : WordTrace (prefixWord ++ tailWord_353384) baseStart_353384 baseEnd_353384 := by
    simpa [prefixWord, tailWord_353384, baseEnd_353384] using wordTrace_append hprefix tailTrace_353384
  have hstable : (prefixWord ++ tailWord_353384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353384).length < 2 ^ (prefixWord ++ tailWord_353384).sum := by decide
  have hdescent : baseEnd_353384 < baseStart_353384 := by decide
  rcases family_descends (prefixWord ++ tailWord_353384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353516 : List Nat := [2, 2, 1, 1, 2, 5, 1, 7]
def baseStart_353516 : Nat := 118140960795 + 353516 * 2 ^ 59
def prefixEnd_353516 : Nat := 4983230072969 + 3 ^ 40 * 353516 * 2
def baseEnd_353516 : Nat := 26892389193325051959143

theorem tailTrace_353516 : CollatzResearch.WordTrace tailWord_353516 prefixEnd_353516 26892389193325051959143 := by
  unfold tailWord_353516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446893893639691285576201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8595858524852921714101601 6446893893639691285576201)
  ·
    refine ⟨4835170420229768464182151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6446893893639691285576201 4835170420229768464182151)
    ·
      refine ⟨7252755630344652696273227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835170420229768464182151 7252755630344652696273227)
      ·
        refine ⟨10879133445516979044409841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7252755630344652696273227 10879133445516979044409841)
        ·
          refine ⟨8159350084137734283307381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10879133445516979044409841 8159350084137734283307381)
          ·
            refine ⟨764939070387912589060067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8159350084137734283307381 764939070387912589060067)
            ·
              refine ⟨1147408605581868883590101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764939070387912589060067 1147408605581868883590101)
              ·
                refine ⟨26892389193325051959143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1147408605581868883590101 26892389193325051959143)
                ·
                  rfl

theorem cell21_353516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_353516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353516 prefixEnd_353516 := by exact prefixLift 353516
  have htrace : WordTrace (prefixWord ++ tailWord_353516) baseStart_353516 baseEnd_353516 := by
    simpa [prefixWord, tailWord_353516, baseEnd_353516] using wordTrace_append hprefix tailTrace_353516
  have hstable : (prefixWord ++ tailWord_353516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353516).length < 2 ^ (prefixWord ++ tailWord_353516).sum := by decide
  have hdescent : baseEnd_353516 < baseStart_353516 := by decide
  rcases family_descends (prefixWord ++ tailWord_353516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353522 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_353522 : Nat := 118140960795 + 353522 * 2 ^ 59
def prefixEnd_353522 : Nat := 4983230072969 + 3 ^ 40 * 353522 * 2
def baseEnd_353522 : Nat := 80678536861720478777417

theorem tailTrace_353522 : CollatzResearch.WordTrace tailWord_353522 prefixEnd_353522 80678536861720478777417 := by
  unfold tailWord_353522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223501656314411398967705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8596004416838430397247213 3223501656314411398967705)
  ·
    refine ⟨2417626242235808549225779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3223501656314411398967705 2417626242235808549225779)
    ·
      refine ⟨3626439363353712823838669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417626242235808549225779 3626439363353712823838669)
      ·
        refine ⟨1359914761257642308939501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3626439363353712823838669 1359914761257642308939501)
        ·
          refine ⟨509968035471615865852313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1359914761257642308939501 509968035471615865852313)
          ·
            refine ⟨382476026603711899389235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509968035471615865852313 382476026603711899389235)
            ·
              refine ⟨573714039905567849083853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382476026603711899389235 573714039905567849083853)
              ·
                refine ⟨215142764964587943406445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 573714039905567849083853 215142764964587943406445)
                ·
                  refine ⟨80678536861720478777417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215142764964587943406445 80678536861720478777417)
                  ·
                    rfl

theorem cell21_353522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_353522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353522 prefixEnd_353522 := by exact prefixLift 353522
  have htrace : WordTrace (prefixWord ++ tailWord_353522) baseStart_353522 baseEnd_353522 := by
    simpa [prefixWord, tailWord_353522, baseEnd_353522] using wordTrace_append hprefix tailTrace_353522
  have hstable : (prefixWord ++ tailWord_353522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353522).length < 2 ^ (prefixWord ++ tailWord_353522).sum := by decide
  have hdescent : baseEnd_353522 < baseStart_353522 := by decide
  rcases family_descends (prefixWord ++ tailWord_353522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353547 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 5]
def baseStart_353547 : Nat := 118140960795 + 353547 * 2 ^ 59
def prefixEnd_353547 : Nat := 4983230072969 + 3 ^ 40 * 353547 * 2
def baseEnd_353547 : Nat := 80684242202325990860699

theorem tailTrace_353547 : CollatzResearch.WordTrace tailWord_353547 prefixEnd_353547 80684242202325990860699 := by
  unfold tailWord_353547
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894918450167074865530895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8596612300111383243687263 12894918450167074865530895)
  ·
    refine ⟨19342377675250612298296343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12894918450167074865530895 19342377675250612298296343)
    ·
      refine ⟨29013566512875918447444515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19342377675250612298296343 29013566512875918447444515)
      ·
        refine ⟨43520349769313877671166773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29013566512875918447444515 43520349769313877671166773)
        ·
          refine ⟨4080032790873176031671885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43520349769313877671166773 4080032790873176031671885)
          ·
            refine ⟨1530012296577441011876957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4080032790873176031671885 1530012296577441011876957)
            ·
              refine ⟨573754611216540379453859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1530012296577441011876957 573754611216540379453859)
              ·
                refine ⟨860631916824810569180789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573754611216540379453859 860631916824810569180789)
                ·
                  refine ⟨80684242202325990860699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860631916824810569180789 80684242202325990860699)
                  ·
                    rfl

theorem cell21_353547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_353547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353547 prefixEnd_353547 := by exact prefixLift 353547
  have htrace : WordTrace (prefixWord ++ tailWord_353547) baseStart_353547 baseEnd_353547 := by
    simpa [prefixWord, tailWord_353547, baseEnd_353547] using wordTrace_append hprefix tailTrace_353547
  have hstable : (prefixWord ++ tailWord_353547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353547).length < 2 ^ (prefixWord ++ tailWord_353547).sum := by decide
  have hdescent : baseEnd_353547 < baseStart_353547 := by decide
  rcases family_descends (prefixWord ++ tailWord_353547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353623 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 5]
def baseStart_353623 : Nat := 118140960795 + 353623 * 2 ^ 59
def prefixEnd_353623 : Nat := 4983230072969 + 3 ^ 40 * 353623 * 2
def baseEnd_353623 : Nat := 80701586437766747593877

theorem tailTrace_353623 : CollatzResearch.WordTrace tailWord_353623 prefixEnd_353623 80701586437766747593877 := by
  unfold tailWord_353623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897690397891739845297523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8598460265261159896865015 12897690397891739845297523)
  ·
    refine ⟨19346535596837609767946285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12897690397891739845297523 19346535596837609767946285)
    ·
      refine ⟨7254950848814103662979857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19346535596837609767946285 7254950848814103662979857)
      ·
        refine ⟨5441213136610577747234893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7254950848814103662979857 5441213136610577747234893)
        ·
          refine ⟨2040454926228966655213085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5441213136610577747234893 2040454926228966655213085)
          ·
            refine ⟨765170597335862495704907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2040454926228966655213085 765170597335862495704907)
            ·
              refine ⟨1147755896003793743557361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765170597335862495704907 1147755896003793743557361)
              ·
                refine ⟨860816922002845307668021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147755896003793743557361 860816922002845307668021)
                ·
                  refine ⟨80701586437766747593877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860816922002845307668021 80701586437766747593877)
                  ·
                    rfl

theorem cell21_353623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_353623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353623 prefixEnd_353623 := by exact prefixLift 353623
  have htrace : WordTrace (prefixWord ++ tailWord_353623) baseStart_353623 baseEnd_353623 := by
    simpa [prefixWord, tailWord_353623, baseEnd_353623] using wordTrace_append hprefix tailTrace_353623
  have hstable : (prefixWord ++ tailWord_353623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353623).length < 2 ^ (prefixWord ++ tailWord_353623).sum := by decide
  have hdescent : baseEnd_353623 < baseStart_353623 := by decide
  rcases family_descends (prefixWord ++ tailWord_353623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353637 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_353637 : Nat := 118140960795 + 353637 * 2 ^ 59
def prefixEnd_353637 : Nat := 4983230072969 + 3 ^ 40 * 353637 * 2
def baseEnd_353637 : Nat := 80704781428505834360515

theorem tailTrace_353637 : CollatzResearch.WordTrace tailWord_353637 prefixEnd_353637 80704781428505834360515 := by
  unfold tailWord_353637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12898201019841020236307165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8598800679894013490871443 12898201019841020236307165)
  ·
    refine ⟨4836825382440382588615187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12898201019841020236307165 4836825382440382588615187)
    ·
      refine ⟨7255238073660573882922781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4836825382440382588615187 7255238073660573882922781)
      ·
        refine ⟨2720714277622715206096043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7255238073660573882922781 2720714277622715206096043)
        ·
          refine ⟨4081071416434072809144065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720714277622715206096043 4081071416434072809144065)
          ·
            refine ⟨3060803562325554606858049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081071416434072809144065 3060803562325554606858049)
            ·
              refine ⟨2295602671744165955143537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3060803562325554606858049 2295602671744165955143537)
              ·
                refine ⟨1721702003808124466357653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2295602671744165955143537 1721702003808124466357653)
                ·
                  refine ⟨80704781428505834360515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1721702003808124466357653 80704781428505834360515)
                  ·
                    rfl

theorem cell21_353637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_353637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353637 prefixEnd_353637 := by exact prefixLift 353637
  have htrace : WordTrace (prefixWord ++ tailWord_353637) baseStart_353637 baseEnd_353637 := by
    simpa [prefixWord, tailWord_353637, baseEnd_353637] using wordTrace_append hprefix tailTrace_353637
  have hstable : (prefixWord ++ tailWord_353637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353637).length < 2 ^ (prefixWord ++ tailWord_353637).sum := by decide
  have hdescent : baseEnd_353637 < baseStart_353637 := by decide
  rcases family_descends (prefixWord ++ tailWord_353637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353671 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 4]
def baseStart_353671 : Nat := 118140960795 + 353671 * 2 ^ 59
def prefixEnd_353671 : Nat := 4983230072969 + 3 ^ 40 * 353671 * 2
def baseEnd_353671 : Nat := 80712540691729330793779

theorem tailTrace_353671 : CollatzResearch.WordTrace tailWord_353671 prefixEnd_353671 80712540691729330793779 := by
  unfold tailWord_353671
  simp only [CollatzResearch.WordTrace]
  refine ⟨12899441101717844043044867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8599627401145229362029911 12899441101717844043044867)
  ·
    refine ⟨19349161652576766064567301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12899441101717844043044867 19349161652576766064567301)
    ·
      refine ⟨3627967809858143637106369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19349161652576766064567301 3627967809858143637106369)
      ·
        refine ⟨2720975857393607727829777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3627967809858143637106369 2720975857393607727829777)
        ·
          refine ⟨2040731893045205795872333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2720975857393607727829777 2040731893045205795872333)
          ·
            refine ⟨765274459891952173452125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2040731893045205795872333 765274459891952173452125)
            ·
              refine ⟨286977922459482065044547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 765274459891952173452125 286977922459482065044547)
              ·
                refine ⟨430466883689223097566821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286977922459482065044547 430466883689223097566821)
                ·
                  refine ⟨80712540691729330793779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430466883689223097566821 80712540691729330793779)
                  ·
                    rfl

theorem cell21_353671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 4].length) (baseStart_353671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353671 prefixEnd_353671 := by exact prefixLift 353671
  have htrace : WordTrace (prefixWord ++ tailWord_353671) baseStart_353671 baseEnd_353671 := by
    simpa [prefixWord, tailWord_353671, baseEnd_353671] using wordTrace_append hprefix tailTrace_353671
  have hstable : (prefixWord ++ tailWord_353671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353671).length < 2 ^ (prefixWord ++ tailWord_353671).sum := by decide
  have hdescent : baseEnd_353671 < baseStart_353671 := by decide
  rcases family_descends (prefixWord ++ tailWord_353671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353713 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_353713 : Nat := 118140960795 + 353713 * 2 ^ 59
def prefixEnd_353713 : Nat := 4983230072969 + 3 ^ 40 * 353713 * 2
def baseEnd_353713 : Nat := 80722125663946591093693

theorem tailTrace_353713 : CollatzResearch.WordTrace tailWord_353713 prefixEnd_353713 80722125663946591093693 := by
  unfold tailWord_353713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12900972967565685216073793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8600648645043790144049195 12900972967565685216073793)
  ·
    refine ⟨9675729725674263912055345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12900972967565685216073793 9675729725674263912055345)
    ·
      refine ⟨7256797294255697934041509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9675729725674263912055345 7256797294255697934041509)
      ·
        refine ⟨1360649492672943362632783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7256797294255697934041509 1360649492672943362632783)
        ·
          refine ⟨2040974239009415043949175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360649492672943362632783 2040974239009415043949175)
          ·
            refine ⟨3061461358514122565923763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040974239009415043949175 3061461358514122565923763)
            ·
              refine ⟨4592192037771183848885645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061461358514122565923763 4592192037771183848885645)
              ·
                refine ⟨1722072014164193943332117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4592192037771183848885645 1722072014164193943332117)
                ·
                  refine ⟨80722125663946591093693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1722072014164193943332117 80722125663946591093693)
                  ·
                    rfl

theorem cell21_353713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_353713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353713 prefixEnd_353713 := by exact prefixLift 353713
  have htrace : WordTrace (prefixWord ++ tailWord_353713) baseStart_353713 baseEnd_353713 := by
    simpa [prefixWord, tailWord_353713, baseEnd_353713] using wordTrace_append hprefix tailTrace_353713
  have hstable : (prefixWord ++ tailWord_353713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353713).length < 2 ^ (prefixWord ++ tailWord_353713).sum := by decide
  have hdescent : baseEnd_353713 < baseStart_353713 := by decide
  rcases family_descends (prefixWord ++ tailWord_353713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353868 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_353868 : Nat := 118140960795 + 353868 * 2 ^ 59
def prefixEnd_353868 : Nat := 4983230072969 + 3 ^ 40 * 353868 * 2
def baseEnd_353868 : Nat := 80757498775700766010043

theorem tailTrace_353868 : CollatzResearch.WordTrace tailWord_353868 prefixEnd_353868 80757498775700766010043 := by
  unfold tailWord_353868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453313141002073343983129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8604417521336097791977505 6453313141002073343983129)
  ·
    refine ⟨4839984855751555007987347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6453313141002073343983129 4839984855751555007987347)
    ·
      refine ⟨7259977283627332511981021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839984855751555007987347 7259977283627332511981021)
      ·
        refine ⟨2722491481360249691992883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7259977283627332511981021 2722491481360249691992883)
        ·
          refine ⟨4083737222040374537989325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722491481360249691992883 4083737222040374537989325)
          ·
            refine ⟨1531401458265140451745997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4083737222040374537989325 1531401458265140451745997)
            ·
              refine ⟨574275546849427669404749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1531401458265140451745997 574275546849427669404749)
              ·
                refine ⟨215353330068535376026781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574275546849427669404749 215353330068535376026781)
                ·
                  refine ⟨80757498775700766010043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215353330068535376026781 80757498775700766010043)
                  ·
                    rfl

theorem cell21_353868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_353868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353868 prefixEnd_353868 := by exact prefixLift 353868
  have htrace : WordTrace (prefixWord ++ tailWord_353868) baseStart_353868 baseEnd_353868 := by
    simpa [prefixWord, tailWord_353868, baseEnd_353868] using wordTrace_append hprefix tailTrace_353868
  have hstable : (prefixWord ++ tailWord_353868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353868).length < 2 ^ (prefixWord ++ tailWord_353868).sum := by decide
  have hdescent : baseEnd_353868 < baseStart_353868 := by decide
  rcases family_descends (prefixWord ++ tailWord_353868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353879 : List Nat := [1, 1, 3, 2, 2, 3, 9]
def baseStart_353879 : Nat := 118140960795 + 353879 * 2 ^ 59
def prefixEnd_353879 : Nat := 4983230072969 + 3 ^ 40 * 353879 * 2
def baseEnd_353879 : Nat := 8973334347285243480743

theorem tailTrace_353879 : CollatzResearch.WordTrace tailWord_353879 prefixEnd_353879 8973334347285243480743 := by
  unfold tailWord_353879
  simp only [CollatzResearch.WordTrace]
  refine ⟨12907027484964295566616691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8604684989976197044411127 12907027484964295566616691)
  ·
    refine ⟨19360541227446443349925037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12907027484964295566616691 19360541227446443349925037)
    ·
      refine ⟨7260202960292416256221889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19360541227446443349925037 7260202960292416256221889)
      ·
        refine ⟨5445152220219312192166417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7260202960292416256221889 5445152220219312192166417)
        ·
          refine ⟨4083864165164484144124813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5445152220219312192166417 4083864165164484144124813)
          ·
            refine ⟨1531449061936681554046805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4083864165164484144124813 1531449061936681554046805)
            ·
              refine ⟨8973334347285243480743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1531449061936681554046805 8973334347285243480743)
              ·
                rfl

theorem cell21_353879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 9].length) (baseStart_353879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353879 prefixEnd_353879 := by exact prefixLift 353879
  have htrace : WordTrace (prefixWord ++ tailWord_353879) baseStart_353879 baseEnd_353879 := by
    simpa [prefixWord, tailWord_353879, baseEnd_353879] using wordTrace_append hprefix tailTrace_353879
  have hstable : (prefixWord ++ tailWord_353879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353879).length < 2 ^ (prefixWord ++ tailWord_353879).sum := by decide
  have hdescent : baseEnd_353879 < baseStart_353879 := by decide
  rcases family_descends (prefixWord ++ tailWord_353879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353896 : List Nat := [2, 1, 4, 3, 1, 1, 1, 8]
def baseStart_353896 : Nat := 118140960795 + 353896 * 2 ^ 59
def prefixEnd_353896 : Nat := 4983230072969 + 3 ^ 40 * 353896 * 2
def baseEnd_353896 : Nat := 26921296252392979847773

theorem tailTrace_353896 : CollatzResearch.WordTrace tailWord_353896 prefixEnd_353896 26921296252392979847773 := by
  unfold tailWord_353896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453823762951353734992771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8605098350601804979990361 6453823762951353734992771)
  ·
    refine ⟨9680735644427030602489157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6453823762951353734992771 9680735644427030602489157)
    ·
      refine ⟨1815137933330068237966717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9680735644427030602489157 1815137933330068237966717)
      ·
        refine ⟨680676724998775589237519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1815137933330068237966717 680676724998775589237519)
        ·
          refine ⟨1021015087498163383856279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680676724998775589237519 1021015087498163383856279)
          ·
            refine ⟨1531522631247245075784419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021015087498163383856279 1531522631247245075784419)
            ·
              refine ⟨2297283946870867613676629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531522631247245075784419 2297283946870867613676629)
              ·
                refine ⟨26921296252392979847773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2297283946870867613676629 26921296252392979847773)
                ·
                  rfl

theorem cell21_353896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_353896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353896 prefixEnd_353896 := by exact prefixLift 353896
  have htrace : WordTrace (prefixWord ++ tailWord_353896) baseStart_353896 baseEnd_353896 := by
    simpa [prefixWord, tailWord_353896, baseEnd_353896] using wordTrace_append hprefix tailTrace_353896
  have hstable : (prefixWord ++ tailWord_353896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353896).length < 2 ^ (prefixWord ++ tailWord_353896).sum := by decide
  have hdescent : baseEnd_353896 < baseStart_353896 := by decide
  rcases family_descends (prefixWord ++ tailWord_353896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353944 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_353944 : Nat := 118140960795 + 353944 * 2 ^ 59
def prefixEnd_353944 : Nat := 4983230072969 + 3 ^ 40 * 353944 * 2
def baseEnd_353944 : Nat := 80774843011141522743221

theorem tailTrace_353944 : CollatzResearch.WordTrace tailWord_353944 prefixEnd_353944 80774843011141522743221 := by
  unfold tailWord_353944
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454699114864405833866443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8606265486485874445155257 6454699114864405833866443)
  ·
    refine ⟨9682048672296608750799665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6454699114864405833866443 9682048672296608750799665)
    ·
      refine ⟨7261536504222456563099749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9682048672296608750799665 7261536504222456563099749)
      ·
        refine ⟨1361538094541710605581203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7261536504222456563099749 1361538094541710605581203)
        ·
          refine ⟨2042307141812565908371805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361538094541710605581203 2042307141812565908371805)
          ·
            refine ⟨765865178179712215639427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2042307141812565908371805 765865178179712215639427)
            ·
              refine ⟨1148797767269568323459141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765865178179712215639427 1148797767269568323459141)
              ·
                refine ⟨215399581363044060648589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1148797767269568323459141 215399581363044060648589)
                ·
                  refine ⟨80774843011141522743221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215399581363044060648589 80774843011141522743221)
                  ·
                    rfl

theorem cell21_353944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_353944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_353944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_353944 prefixEnd_353944 := by exact prefixLift 353944
  have htrace : WordTrace (prefixWord ++ tailWord_353944) baseStart_353944 baseEnd_353944 := by
    simpa [prefixWord, tailWord_353944, baseEnd_353944] using wordTrace_append hprefix tailTrace_353944
  have hstable : (prefixWord ++ tailWord_353944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353944).length < 2 ^ (prefixWord ++ tailWord_353944).sum := by decide
  have hdescent : baseEnd_353944 < baseStart_353944 := by decide
  rcases family_descends (prefixWord ++ tailWord_353944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354023 : List Nat := [1, 1, 5, 4, 2, 1, 2, 5]
def baseStart_354023 : Nat := 118140960795 + 354023 * 2 ^ 59
def prefixEnd_354023 : Nat := 4983230072969 + 3 ^ 40 * 354023 * 2
def baseEnd_354023 : Nat := 26930957295818313642131

theorem tailTrace_354023 : CollatzResearch.WordTrace tailWord_354023 prefixEnd_354023 26930957295818313642131 := by
  unfold tailWord_354023
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912279596442608159858723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8608186397628405439905815 12912279596442608159858723)
  ·
    refine ⟨19368419394663912239788085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12912279596442608159858723 19368419394663912239788085)
    ·
      refine ⟨1815789318249741772480133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19368419394663912239788085 1815789318249741772480133)
      ·
        refine ⟨340460497171826582340025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1815789318249741772480133 340460497171826582340025)
        ·
          refine ⟨255345372878869936755019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340460497171826582340025 255345372878869936755019)
          ·
            refine ⟨383018059318304905132529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255345372878869936755019 383018059318304905132529)
            ·
              refine ⟨287263544488728678849397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383018059318304905132529 287263544488728678849397)
              ·
                refine ⟨26930957295818313642131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287263544488728678849397 26930957295818313642131)
                ·
                  rfl

theorem cell21_354023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 5].length) (baseStart_354023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354023 prefixEnd_354023 := by exact prefixLift 354023
  have htrace : WordTrace (prefixWord ++ tailWord_354023) baseStart_354023 baseEnd_354023 := by
    simpa [prefixWord, tailWord_354023, baseEnd_354023] using wordTrace_append hprefix tailTrace_354023
  have hstable : (prefixWord ++ tailWord_354023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354023).length < 2 ^ (prefixWord ++ tailWord_354023).sum := by decide
  have hdescent : baseEnd_354023 < baseStart_354023 := by decide
  rcases family_descends (prefixWord ++ tailWord_354023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354031 : List Nat := [1, 1, 2, 1, 5, 1, 3, 7]
def baseStart_354031 : Nat := 118140960795 + 354031 * 2 ^ 59
def prefixEnd_354031 : Nat := 4983230072969 + 3 ^ 40 * 354031 * 2
def baseEnd_354031 : Nat := 26931565865482901597681

theorem tailTrace_354031 : CollatzResearch.WordTrace tailWord_354031 prefixEnd_354031 26931565865482901597681 := by
  unfold tailWord_354031
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912571380413625526149947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8608380920275750350766631 12912571380413625526149947)
  ·
    refine ⟨19368857070620438289224921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12912571380413625526149947 19368857070620438289224921)
    ·
      refine ⟨14526642802965328716918691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19368857070620438289224921 14526642802965328716918691)
      ·
        refine ⟨21789964204447993075378037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14526642802965328716918691 21789964204447993075378037)
        ·
          refine ⟨2042809144166999350816691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21789964204447993075378037 2042809144166999350816691)
          ·
            refine ⟨3064213716250499026225037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042809144166999350816691 3064213716250499026225037)
            ·
              refine ⟨1149080143593937134834389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3064213716250499026225037 1149080143593937134834389)
              ·
                refine ⟨26931565865482901597681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1149080143593937134834389 26931565865482901597681)
                ·
                  rfl

theorem cell21_354031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_354031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354031 prefixEnd_354031 := by exact prefixLift 354031
  have htrace : WordTrace (prefixWord ++ tailWord_354031) baseStart_354031 baseEnd_354031 := by
    simpa [prefixWord, tailWord_354031, baseEnd_354031] using wordTrace_append hprefix tailTrace_354031
  have hstable : (prefixWord ++ tailWord_354031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354031).length < 2 ^ (prefixWord ++ tailWord_354031).sum := by decide
  have hdescent : baseEnd_354031 < baseStart_354031 := by decide
  rcases family_descends (prefixWord ++ tailWord_354031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354110 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_354110 : Nat := 118140960795 + 354110 * 2 ^ 59
def prefixEnd_354110 : Nat := 4983230072969 + 3 ^ 40 * 354110 * 2
def baseEnd_354110 : Nat := 80812726472762122976215

theorem tailTrace_354110 : CollatzResearch.WordTrace tailWord_354110 prefixEnd_354110 80812726472762122976215 := by
  unfold tailWord_354110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614431593390927752284473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8610301831418281345517189 1614431593390927752284473)
  ·
    refine ⟨1210823695043195814213355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1614431593390927752284473 1210823695043195814213355)
    ·
      refine ⟨1816235542564793721320033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210823695043195814213355 1816235542564793721320033)
      ·
        refine ⟨1362176656923595290990025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1816235542564793721320033 1362176656923595290990025)
        ·
          refine ⟨1021632492692696468242519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1362176656923595290990025 1021632492692696468242519)
          ·
            refine ⟨1532448739039044702363779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021632492692696468242519 1532448739039044702363779)
            ·
              refine ⟨2298673108558567053545669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532448739039044702363779 2298673108558567053545669)
              ·
                refine ⟨431001207854731322539813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2298673108558567053545669 431001207854731322539813)
                ·
                  refine ⟨80812726472762122976215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 431001207854731322539813 80812726472762122976215)
                  ·
                    rfl

theorem cell21_354110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_354110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354110 prefixEnd_354110 := by exact prefixLift 354110
  have htrace : WordTrace (prefixWord ++ tailWord_354110) baseStart_354110 baseEnd_354110 := by
    simpa [prefixWord, tailWord_354110, baseEnd_354110] using wordTrace_append hprefix tailTrace_354110
  have hstable : (prefixWord ++ tailWord_354110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354110).length < 2 ^ (prefixWord ++ tailWord_354110).sum := by decide
  have hdescent : baseEnd_354110 < baseStart_354110 := by decide
  rcases family_descends (prefixWord ++ tailWord_354110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354138 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_354138 : Nat := 118140960795 + 354138 * 2 ^ 59
def prefixEnd_354138 : Nat := 4983230072969 + 3 ^ 40 * 354138 * 2
def baseEnd_354138 : Nat := 80819116454240296509491

theorem tailTrace_354138 : CollatzResearch.WordTrace tailWord_354138 prefixEnd_354138 80819116454240296509491 := by
  unfold tailWord_354138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3229118497756495700073767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8610982660683988533530045 3229118497756495700073767)
  ·
    refine ⟨4843677746634743550110651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3229118497756495700073767 4843677746634743550110651)
    ·
      refine ⟨7265516619952115325165977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843677746634743550110651 7265516619952115325165977)
      ·
        refine ⟨5449137464964086493874483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7265516619952115325165977 5449137464964086493874483)
        ·
          refine ⟨8173706197446129740811725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449137464964086493874483 8173706197446129740811725)
          ·
            refine ⟨3065139824042298652804397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8173706197446129740811725 3065139824042298652804397)
            ·
              refine ⟨1149427434015861994801649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3065139824042298652804397 1149427434015861994801649)
              ·
                refine ⟨862070575511896496101237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149427434015861994801649 862070575511896496101237)
                ·
                  refine ⟨80819116454240296509491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 862070575511896496101237 80819116454240296509491)
                  ·
                    rfl

theorem cell21_354138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_354138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354138 prefixEnd_354138 := by exact prefixLift 354138
  have htrace : WordTrace (prefixWord ++ tailWord_354138) baseStart_354138 baseEnd_354138 := by
    simpa [prefixWord, tailWord_354138, baseEnd_354138] using wordTrace_append hprefix tailTrace_354138
  have hstable : (prefixWord ++ tailWord_354138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354138).length < 2 ^ (prefixWord ++ tailWord_354138).sum := by decide
  have hdescent : baseEnd_354138 < baseStart_354138 := by decide
  rcases family_descends (prefixWord ++ tailWord_354138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354369 : List Nat := [1, 2, 5, 1, 2, 3, 2, 5]
def baseStart_354369 : Nat := 118140960795 + 354369 * 2 ^ 59
def prefixEnd_354369 : Nat := 4983230072969 + 3 ^ 40 * 354369 * 2
def baseEnd_354369 : Nat := 26957277933811742719673

theorem tailTrace_354369 : CollatzResearch.WordTrace tailWord_354369 prefixEnd_354369 26957277933811742719673 := by
  unfold tailWord_354369
  simp only [CollatzResearch.WordTrace]
  refine ⟨12924899253189109251954161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8616599502126072834636107 12924899253189109251954161)
  ·
    refine ⟨9693674439891831938965621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12924899253189109251954161 9693674439891831938965621)
    ·
      refine ⟨908781978739859244278027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9693674439891831938965621 908781978739859244278027)
      ·
        refine ⟨1363172968109788866417041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908781978739859244278027 1363172968109788866417041)
        ·
          refine ⟨1022379726082341649812781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363172968109788866417041 1022379726082341649812781)
          ·
            refine ⟨383392397280878118679793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1022379726082341649812781 383392397280878118679793)
            ·
              refine ⟨287544297960658589009845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383392397280878118679793 287544297960658589009845)
              ·
                refine ⟨26957277933811742719673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287544297960658589009845 26957277933811742719673)
                ·
                  rfl

theorem cell21_354369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 5].length) (baseStart_354369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354369 prefixEnd_354369 := by exact prefixLift 354369
  have htrace : WordTrace (prefixWord ++ tailWord_354369) baseStart_354369 baseEnd_354369 := by
    simpa [prefixWord, tailWord_354369, baseEnd_354369] using wordTrace_append hprefix tailTrace_354369
  have hstable : (prefixWord ++ tailWord_354369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354369).length < 2 ^ (prefixWord ++ tailWord_354369).sum := by decide
  have hdescent : baseEnd_354369 < baseStart_354369 := by decide
  rcases family_descends (prefixWord ++ tailWord_354369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354380 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_354380 : Nat := 118140960795 + 354380 * 2 ^ 59
def prefixEnd_354380 : Nat := 4983230072969 + 3 ^ 40 * 354380 * 2
def baseEnd_354380 : Nat := 80874344151301653475663

theorem tailTrace_354380 : CollatzResearch.WordTrace tailWord_354380 prefixEnd_354380 80874344151301653475663 := by
  unfold tailWord_354380
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462650228074629065302297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8616866970766172087069729 6462650228074629065302297)
  ·
    refine ⟨4846987671055971798976723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6462650228074629065302297 4846987671055971798976723)
    ·
      refine ⟨7270481506583957698465085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846987671055971798976723 7270481506583957698465085)
      ·
        refine ⟨2726430564968984136924407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7270481506583957698465085 2726430564968984136924407)
        ·
          refine ⟨4089645847453476205386611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726430564968984136924407 4089645847453476205386611)
          ·
            refine ⟨6134468771180214308079917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089645847453476205386611 6134468771180214308079917)
            ·
              refine ⟨2300425789192580365529969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6134468771180214308079917 2300425789192580365529969)
              ·
                refine ⟨1725319341894435274147477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300425789192580365529969 1725319341894435274147477)
                ·
                  refine ⟨80874344151301653475663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1725319341894435274147477 80874344151301653475663)
                  ·
                    rfl

theorem cell21_354380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_354380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354380 prefixEnd_354380 := by exact prefixLift 354380
  have htrace : WordTrace (prefixWord ++ tailWord_354380) baseStart_354380 baseEnd_354380 := by
    simpa [prefixWord, tailWord_354380, baseEnd_354380] using wordTrace_append hprefix tailTrace_354380
  have hstable : (prefixWord ++ tailWord_354380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354380).length < 2 ^ (prefixWord ++ tailWord_354380).sum := by decide
  have hdescent : baseEnd_354380 < baseStart_354380 := by decide
  rcases family_descends (prefixWord ++ tailWord_354380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354400 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_354400 : Nat := 118140960795 + 354400 * 2 ^ 59
def prefixEnd_354400 : Nat := 4983230072969 + 3 ^ 40 * 354400 * 2
def baseEnd_354400 : Nat := 80878908423786063142289

theorem tailTrace_354400 : CollatzResearch.WordTrace tailWord_354400 prefixEnd_354400 80878908423786063142289 := by
  unfold tailWord_354400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463014958038400773166327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8617353277384534364221769 6463014958038400773166327)
  ·
    refine ⟨9694522437057601159749491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6463014958038400773166327 9694522437057601159749491)
    ·
      refine ⟨14541783655586401739624237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9694522437057601159749491 14541783655586401739624237)
      ·
        refine ⟨5453168870844900652359089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14541783655586401739624237 5453168870844900652359089)
        ·
          refine ⟨4089876653133675489269317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5453168870844900652359089 4089876653133675489269317)
          ·
            refine ⟨766851872462564154237997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4089876653133675489269317 766851872462564154237997)
            ·
              refine ⟨287569452173461557839249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 766851872462564154237997 287569452173461557839249)
              ·
                refine ⟨215677089130096168379437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287569452173461557839249 215677089130096168379437)
                ·
                  refine ⟨80878908423786063142289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215677089130096168379437 80878908423786063142289)
                  ·
                    rfl

theorem cell21_354400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_354400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354400 prefixEnd_354400 := by exact prefixLift 354400
  have htrace : WordTrace (prefixWord ++ tailWord_354400) baseStart_354400 baseEnd_354400 := by
    simpa [prefixWord, tailWord_354400, baseEnd_354400] using wordTrace_append hprefix tailTrace_354400
  have hstable : (prefixWord ++ tailWord_354400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354400).length < 2 ^ (prefixWord ++ tailWord_354400).sum := by decide
  have hdescent : baseEnd_354400 < baseStart_354400 := by decide
  rcases family_descends (prefixWord ++ tailWord_354400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354462 : List Nat := [4, 3, 1, 1, 4, 1, 1, 6]
def baseStart_354462 : Nat := 118140960795 + 354462 * 2 ^ 59
def prefixEnd_354462 : Nat := 4983230072969 + 3 ^ 40 * 354462 * 2
def baseEnd_354462 : Nat := 26964352556162577702943

theorem tailTrace_354462 : CollatzResearch.WordTrace tailWord_354462 prefixEnd_354462 26964352556162577702943 := by
  unfold tailWord_354462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616036405231523266886205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8618860827901457423393093 1616036405231523266886205)
  ·
    refine ⟨606013651961821225082327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1616036405231523266886205 606013651961821225082327)
    ·
      refine ⟨909020477942731837623491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 606013651961821225082327 909020477942731837623491)
      ·
        refine ⟨1363530716914097756435237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909020477942731837623491 1363530716914097756435237)
        ·
          refine ⟨255662009421393329331607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1363530716914097756435237 255662009421393329331607)
          ·
            refine ⟨383493014132089993997411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255662009421393329331607 383493014132089993997411)
            ·
              refine ⟨575239521198134990996117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383493014132089993997411 575239521198134990996117)
              ·
                refine ⟨26964352556162577702943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 575239521198134990996117 26964352556162577702943)
                ·
                  rfl

theorem cell21_354462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_354462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354462 prefixEnd_354462 := by exact prefixLift 354462
  have htrace : WordTrace (prefixWord ++ tailWord_354462) baseStart_354462 baseEnd_354462 := by
    simpa [prefixWord, tailWord_354462, baseEnd_354462] using wordTrace_append hprefix tailTrace_354462
  have hstable : (prefixWord ++ tailWord_354462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354462).length < 2 ^ (prefixWord ++ tailWord_354462).sum := by decide
  have hdescent : baseEnd_354462 < baseStart_354462 := by decide
  rcases family_descends (prefixWord ++ tailWord_354462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354524 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_354524 : Nat := 118140960795 + 354524 * 2 ^ 59
def prefixEnd_354524 : Nat := 4983230072969 + 3 ^ 40 * 354524 * 2
def baseEnd_354524 : Nat := 80907206913189403075369

theorem tailTrace_354524 : CollatzResearch.WordTrace tailWord_354524 prefixEnd_354524 80907206913189403075369 := by
  unfold tailWord_354524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465276283813785361923313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8620368378418380482564417 6465276283813785361923313)
  ·
    refine ⟨4848957212860339021442485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6465276283813785361923313 4848957212860339021442485)
    ·
      refine ⟨454589738705656783260233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4848957212860339021442485 454589738705656783260233)
      ·
        refine ⟨340942304029242587445175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454589738705656783260233 340942304029242587445175)
        ·
          refine ⟨511413456043863881167763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340942304029242587445175 511413456043863881167763)
          ·
            refine ⟨767120184065795821751645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511413456043863881167763 767120184065795821751645)
            ·
              refine ⟨287670069024673433156867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 767120184065795821751645 287670069024673433156867)
              ·
                refine ⟨431505103537010149735301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287670069024673433156867 431505103537010149735301)
                ·
                  refine ⟨80907206913189403075369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 431505103537010149735301 80907206913189403075369)
                  ·
                    rfl

theorem cell21_354524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_354524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354524 prefixEnd_354524 := by exact prefixLift 354524
  have htrace : WordTrace (prefixWord ++ tailWord_354524) baseStart_354524 baseEnd_354524 := by
    simpa [prefixWord, tailWord_354524, baseEnd_354524] using wordTrace_append hprefix tailTrace_354524
  have hstable : (prefixWord ++ tailWord_354524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354524).length < 2 ^ (prefixWord ++ tailWord_354524).sum := by decide
  have hdescent : baseEnd_354524 < baseStart_354524 := by decide
  rcases family_descends (prefixWord ++ tailWord_354524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354656 : List Nat := [2, 1, 1, 3, 5, 1, 3, 5]
def baseStart_354656 : Nat := 118140960795 + 354656 * 2 ^ 59
def prefixEnd_354656 : Nat := 4983230072969 + 3 ^ 40 * 354656 * 2
def baseEnd_354656 : Nat := 26979110370528835625033

theorem tailTrace_354656 : CollatzResearch.WordTrace tailWord_354656 prefixEnd_354656 26979110370528835625033 := by
  unfold tailWord_354656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467683501574678633825911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8623578002099571511767881 6467683501574678633825911)
  ·
    refine ⟨9701525252362017950738867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6467683501574678633825911 9701525252362017950738867)
    ·
      refine ⟨14552287878543026926108301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701525252362017950738867 14552287878543026926108301)
      ·
        refine ⟨5457107954453635097290613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14552287878543026926108301 5457107954453635097290613)
        ·
          refine ⟨511603870730028290370995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5457107954453635097290613 511603870730028290370995)
          ·
            refine ⟨767405806095042435556493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511603870730028290370995 767405806095042435556493)
            ·
              refine ⟨287777177285640913333685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 767405806095042435556493 287777177285640913333685)
              ·
                refine ⟨26979110370528835625033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287777177285640913333685 26979110370528835625033)
                ·
                  rfl

theorem cell21_354656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_354656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354656 prefixEnd_354656 := by exact prefixLift 354656
  have htrace : WordTrace (prefixWord ++ tailWord_354656) baseStart_354656 baseEnd_354656 := by
    simpa [prefixWord, tailWord_354656, baseEnd_354656] using wordTrace_append hprefix tailTrace_354656
  have hstable : (prefixWord ++ tailWord_354656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354656).length < 2 ^ (prefixWord ++ tailWord_354656).sum := by decide
  have hdescent : baseEnd_354656 < baseStart_354656 := by decide
  rcases family_descends (prefixWord ++ tailWord_354656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354667 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_354667 : Nat := 118140960795 + 354667 * 2 ^ 59
def prefixEnd_354667 : Nat := 4983230072969 + 3 ^ 40 * 354667 * 2
def baseEnd_354667 : Nat := 80939841461452932191743

theorem tailTrace_354667 : CollatzResearch.WordTrace tailWord_354667 prefixEnd_354667 80939841461452932191743 := by
  unfold tailWord_354667
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935768206109506146302255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8623845470739670764201503 12935768206109506146302255)
  ·
    refine ⟨19403652309164259219453383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12935768206109506146302255 19403652309164259219453383)
    ·
      refine ⟨29105478463746388829180075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19403652309164259219453383 29105478463746388829180075)
      ·
        refine ⟨43658217695619583243770113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29105478463746388829180075 43658217695619583243770113)
        ·
          refine ⟨32743663271714687432827585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43658217695619583243770113 32743663271714687432827585)
          ·
            refine ⟨24557747453786015574620689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32743663271714687432827585 24557747453786015574620689)
            ·
              refine ⟨18418310590339511680965517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24557747453786015574620689 18418310590339511680965517)
              ·
                refine ⟨6906866471377316880362069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18418310590339511680965517 6906866471377316880362069)
                ·
                  refine ⟨80939841461452932191743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6906866471377316880362069 80939841461452932191743)
                  ·
                    rfl

theorem cell21_354667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_354667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354667 prefixEnd_354667 := by exact prefixLift 354667
  have htrace : WordTrace (prefixWord ++ tailWord_354667) baseStart_354667 baseEnd_354667 := by
    simpa [prefixWord, tailWord_354667, baseEnd_354667] using wordTrace_append hprefix tailTrace_354667
  have hstable : (prefixWord ++ tailWord_354667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354667).length < 2 ^ (prefixWord ++ tailWord_354667).sum := by decide
  have hdescent : baseEnd_354667 < baseStart_354667 := by decide
  rcases family_descends (prefixWord ++ tailWord_354667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354684 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_354684 : Nat := 118140960795 + 354684 * 2 ^ 59
def prefixEnd_354684 : Nat := 4983230072969 + 3 ^ 40 * 354684 * 2
def baseEnd_354684 : Nat := 80943721093064680408375

theorem tailTrace_354684 : CollatzResearch.WordTrace tailWord_354684 prefixEnd_354684 80943721093064680408375 := by
  unfold tailWord_354684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468194123523959024835553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8624258831365278699780737 6468194123523959024835553)
  ·
    refine ⟨4851145592642969268626665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6468194123523959024835553 4851145592642969268626665)
    ·
      refine ⟨3638359194482226951469999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4851145592642969268626665 3638359194482226951469999)
      ·
        refine ⟨5457538791723340427204999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638359194482226951469999 5457538791723340427204999)
        ·
          refine ⟨8186308187585010640807499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457538791723340427204999 8186308187585010640807499)
          ·
            refine ⟨12279462281377515961211249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186308187585010640807499 12279462281377515961211249)
            ·
              refine ⟨9209596711033136970908437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12279462281377515961211249 9209596711033136970908437)
              ·
                refine ⟨431699845829678295511333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9209596711033136970908437 431699845829678295511333)
                ·
                  refine ⟨80943721093064680408375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 431699845829678295511333 80943721093064680408375)
                  ·
                    rfl

theorem cell21_354684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_354684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354684 prefixEnd_354684 := by exact prefixLift 354684
  have htrace : WordTrace (prefixWord ++ tailWord_354684) baseStart_354684 baseEnd_354684 := by
    simpa [prefixWord, tailWord_354684, baseEnd_354684] using wordTrace_append hprefix tailTrace_354684
  have hstable : (prefixWord ++ tailWord_354684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354684).length < 2 ^ (prefixWord ++ tailWord_354684).sum := by decide
  have hdescent : baseEnd_354684 < baseStart_354684 := by decide
  rcases family_descends (prefixWord ++ tailWord_354684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354721 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 3]
def baseStart_354721 : Nat := 118140960795 + 354721 * 2 ^ 59
def prefixEnd_354721 : Nat := 4983230072969 + 3 ^ 40 * 354721 * 2
def baseEnd_354721 : Nat := 80952164997160838291633

theorem tailTrace_354721 : CollatzResearch.WordTrace tailWord_354721 prefixEnd_354721 80952164997160838291633 := by
  unfold tailWord_354721
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937737747913873368768017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8625158498609248912512011 12937737747913873368768017)
  ·
    refine ⟨9703303310935405026576013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12937737747913873368768017 9703303310935405026576013)
    ·
      refine ⟨3638738741600776884966005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9703303310935405026576013 3638738741600776884966005)
      ·
        refine ⟨341131757025072832965563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3638738741600776884966005 341131757025072832965563)
        ·
          refine ⟨511697635537609249448345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341131757025072832965563 511697635537609249448345)
          ·
            refine ⟨383773226653206937086259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511697635537609249448345 383773226653206937086259)
            ·
              refine ⟨575659839979810405629389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383773226653206937086259 575659839979810405629389)
              ·
                refine ⟨215872439992428902111021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 575659839979810405629389 215872439992428902111021)
                ·
                  refine ⟨80952164997160838291633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215872439992428902111021 80952164997160838291633)
                  ·
                    rfl

theorem cell21_354721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_354721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354721 prefixEnd_354721 := by exact prefixLift 354721
  have htrace : WordTrace (prefixWord ++ tailWord_354721) baseStart_354721 baseEnd_354721 := by
    simpa [prefixWord, tailWord_354721, baseEnd_354721] using wordTrace_append hprefix tailTrace_354721
  have hstable : (prefixWord ++ tailWord_354721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354721).length < 2 ^ (prefixWord ++ tailWord_354721).sum := by decide
  have hdescent : baseEnd_354721 < baseStart_354721 := by decide
  rcases family_descends (prefixWord ++ tailWord_354721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354746 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_354746 : Nat := 118140960795 + 354746 * 2 ^ 59
def prefixEnd_354746 : Nat := 4983230072969 + 3 ^ 40 * 354746 * 2
def baseEnd_354746 : Nat := 80957870337766350374915

theorem tailTrace_354746 : CollatzResearch.WordTrace tailWord_354746 prefixEnd_354746 80957870337766350374915 := by
  unfold tailWord_354746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234662393205825659607023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8625766381882201758952061 3234662393205825659607023)
  ·
    refine ⟨4851993589808738489410535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234662393205825659607023 4851993589808738489410535)
    ·
      refine ⟨7277990384713107734115803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4851993589808738489410535 7277990384713107734115803)
      ·
        refine ⟨10916985577069661601173705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7277990384713107734115803 10916985577069661601173705)
        ·
          refine ⟨8187739182802246200880279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10916985577069661601173705 8187739182802246200880279)
          ·
            refine ⟨12281608774203369301320419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187739182802246200880279 12281608774203369301320419)
            ·
              refine ⟨18422413161305053951980629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281608774203369301320419 18422413161305053951980629)
              ·
                refine ⟨215887654234043600999773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 18422413161305053951980629 215887654234043600999773)
                ·
                  refine ⟨80957870337766350374915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215887654234043600999773 80957870337766350374915)
                  ·
                    rfl

theorem cell21_354746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_354746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354746 prefixEnd_354746 := by exact prefixLift 354746
  have htrace : WordTrace (prefixWord ++ tailWord_354746) baseStart_354746 baseEnd_354746 := by
    simpa [prefixWord, tailWord_354746, baseEnd_354746] using wordTrace_append hprefix tailTrace_354746
  have hstable : (prefixWord ++ tailWord_354746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354746).length < 2 ^ (prefixWord ++ tailWord_354746).sum := by decide
  have hdescent : baseEnd_354746 < baseStart_354746 := by decide
  rcases family_descends (prefixWord ++ tailWord_354746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354797 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 3]
def baseStart_354797 : Nat := 118140960795 + 354797 * 2 ^ 59
def prefixEnd_354797 : Nat := 4983230072969 + 3 ^ 40 * 354797 * 2
def baseEnd_354797 : Nat := 80969509232601595024811

theorem tailTrace_354797 : CollatzResearch.WordTrace tailWord_354797 prefixEnd_354797 80969509232601595024811 := by
  unfold tailWord_354797
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940509695638538348534645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8627006463759025565689763 12940509695638538348534645)
  ·
    refine ⟨1213172783966112970175123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12940509695638538348534645 1213172783966112970175123)
    ·
      refine ⟨1819759175949169455262685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213172783966112970175123 1819759175949169455262685)
      ·
        refine ⟨682409690980938545723507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1819759175949169455262685 682409690980938545723507)
        ·
          refine ⟨1023614536471407818585261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682409690980938545723507 1023614536471407818585261)
          ·
            refine ⟨383855451176777931969473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1023614536471407818585261 383855451176777931969473)
            ·
              refine ⟨287891588382583448977105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383855451176777931969473 287891588382583448977105)
              ·
                refine ⟨215918691286937586732829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287891588382583448977105 215918691286937586732829)
                ·
                  refine ⟨80969509232601595024811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215918691286937586732829 80969509232601595024811)
                  ·
                    rfl

theorem cell21_354797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_354797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354797 prefixEnd_354797 := by exact prefixLift 354797
  have htrace : WordTrace (prefixWord ++ tailWord_354797) baseStart_354797 baseEnd_354797 := by
    simpa [prefixWord, tailWord_354797, baseEnd_354797] using wordTrace_append hprefix tailTrace_354797
  have hstable : (prefixWord ++ tailWord_354797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354797).length < 2 ^ (prefixWord ++ tailWord_354797).sum := by decide
  have hdescent : baseEnd_354797 < baseStart_354797 := by decide
  rcases family_descends (prefixWord ++ tailWord_354797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354895 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_354895 : Nat := 118140960795 + 354895 * 2 ^ 59
def prefixEnd_354895 : Nat := 4983230072969 + 3 ^ 40 * 354895 * 2
def baseEnd_354895 : Nat := 80991874167775202391277

theorem tailTrace_354895 : CollatzResearch.WordTrace tailWord_354895 prefixEnd_354895 80991874167775202391277 := by
  unfold tailWord_354895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944084049283501085602139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8629389366189000723734759 12944084049283501085602139)
  ·
    refine ⟨19416126073925251628403209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12944084049283501085602139 19416126073925251628403209)
    ·
      refine ⟨14562094555443938721302407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19416126073925251628403209 14562094555443938721302407)
      ·
        refine ⟨21843141833165908081953611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14562094555443938721302407 21843141833165908081953611)
        ·
          refine ⟨32764712749748862122930417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21843141833165908081953611 32764712749748862122930417)
          ·
            refine ⟨24573534562311646592197813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32764712749748862122930417 24573534562311646592197813)
            ·
              refine ⟨2303768865216716868018545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24573534562311646592197813 2303768865216716868018545)
              ·
                refine ⟨1727826648912537651013909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303768865216716868018545 1727826648912537651013909)
                ·
                  refine ⟨80991874167775202391277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1727826648912537651013909 80991874167775202391277)
                  ·
                    rfl

theorem cell21_354895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_354895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354895 prefixEnd_354895 := by exact prefixLift 354895
  have htrace : WordTrace (prefixWord ++ tailWord_354895) baseStart_354895 baseEnd_354895 := by
    simpa [prefixWord, tailWord_354895, baseEnd_354895] using wordTrace_append hprefix tailTrace_354895
  have hstable : (prefixWord ++ tailWord_354895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354895).length < 2 ^ (prefixWord ++ tailWord_354895).sum := by decide
  have hdescent : baseEnd_354895 < baseStart_354895 := by decide
  rcases family_descends (prefixWord ++ tailWord_354895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354915 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 3]
def baseStart_354915 : Nat := 118140960795 + 354915 * 2 ^ 59
def prefixEnd_354915 : Nat := 4983230072969 + 3 ^ 40 * 354915 * 2
def baseEnd_354915 : Nat := 80996438440259612057903

theorem tailTrace_354915 : CollatzResearch.WordTrace tailWord_354915 prefixEnd_354915 80996438440259612057903 := by
  unfold tailWord_354915
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944813509211044501330199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8629875672807363000886799 12944813509211044501330199)
  ·
    refine ⟨19417220263816566751995299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12944813509211044501330199 19417220263816566751995299)
    ·
      refine ⟨29125830395724850127992949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19417220263816566751995299 29125830395724850127992949)
      ·
        refine ⟨2730546599599204699499339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29125830395724850127992949 2730546599599204699499339)
        ·
          refine ⟨4095819899398807049249009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730546599599204699499339 4095819899398807049249009)
          ·
            refine ⟨3071864924549105286936757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4095819899398807049249009 3071864924549105286936757)
            ·
              refine ⟨287987336676478620650321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3071864924549105286936757 287987336676478620650321)
              ·
                refine ⟨215990502507358965487741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 287987336676478620650321 215990502507358965487741)
                ·
                  refine ⟨80996438440259612057903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215990502507358965487741 80996438440259612057903)
                  ·
                    rfl

theorem cell21_354915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 3].length) (baseStart_354915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354915 prefixEnd_354915 := by exact prefixLift 354915
  have htrace : WordTrace (prefixWord ++ tailWord_354915) baseStart_354915 baseEnd_354915 := by
    simpa [prefixWord, tailWord_354915, baseEnd_354915] using wordTrace_append hprefix tailTrace_354915
  have hstable : (prefixWord ++ tailWord_354915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354915).length < 2 ^ (prefixWord ++ tailWord_354915).sum := by decide
  have hdescent : baseEnd_354915 < baseStart_354915 := by decide
  rcases family_descends (prefixWord ++ tailWord_354915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354974 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_354974 : Nat := 118140960795 + 354974 * 2 ^ 59
def prefixEnd_354974 : Nat := 4983230072969 + 3 ^ 40 * 354974 * 2
def baseEnd_354974 : Nat := 81009903044088620574449

theorem tailTrace_354974 : CollatzResearch.WordTrace tailWord_354974 prefixEnd_354974 81009903044088620574449 := by
  unfold tailWord_354974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1618370676999662197215997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8631310277331531718485317 1618370676999662197215997)
  ·
    refine ⟨606889003874873323955999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1618370676999662197215997 606889003874873323955999)
    ·
      refine ⟨910333505812309985933999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 606889003874873323955999 910333505812309985933999)
      ·
        refine ⟨1365500258718464978900999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910333505812309985933999 1365500258718464978900999)
        ·
          refine ⟨2048250388077697468351499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365500258718464978900999 2048250388077697468351499)
          ·
            refine ⟨3072375582116546202527249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048250388077697468351499 3072375582116546202527249)
            ·
              refine ⟨2304281686587409651895437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3072375582116546202527249 2304281686587409651895437)
              ·
                refine ⟨864105632470278619460789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2304281686587409651895437 864105632470278619460789)
                ·
                  refine ⟨81009903044088620574449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 864105632470278619460789 81009903044088620574449)
                  ·
                    rfl

theorem cell21_354974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_354974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_354974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_354974 prefixEnd_354974 := by exact prefixLift 354974
  have htrace : WordTrace (prefixWord ++ tailWord_354974) baseStart_354974 baseEnd_354974 := by
    simpa [prefixWord, tailWord_354974, baseEnd_354974] using wordTrace_append hprefix tailTrace_354974
  have hstable : (prefixWord ++ tailWord_354974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354974).length < 2 ^ (prefixWord ++ tailWord_354974).sum := by decide
  have hdescent : baseEnd_354974 < baseStart_354974 := by decide
  rcases family_descends (prefixWord ++ tailWord_354974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355033 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 5]
def baseStart_355033 : Nat := 118140960795 + 355033 * 2 ^ 59
def prefixEnd_355033 : Nat := 4983230072969 + 3 ^ 40 * 355033 * 2
def baseEnd_355033 : Nat := 81023367647917629090995

theorem tailTrace_355033 : CollatzResearch.WordTrace tailWord_355033 prefixEnd_355033 81023367647917629090995 := by
  unfold tailWord_355033
  simp only [CollatzResearch.WordTrace]
  refine ⟨12949117322783550654125753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8632744881855700436083835 12949117322783550654125753)
  ·
    refine ⟨9711837992087662990594315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12949117322783550654125753 9711837992087662990594315)
    ·
      refine ⟨14567756988131494485891473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711837992087662990594315 14567756988131494485891473)
      ·
        refine ⟨10925817741098620864418605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14567756988131494485891473 10925817741098620864418605)
        ·
          refine ⟨4097181652911982824156977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10925817741098620864418605 4097181652911982824156977)
          ·
            refine ⟨3072886239683987118117733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097181652911982824156977 3072886239683987118117733)
            ·
              refine ⟨576166169940747584647075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3072886239683987118117733 576166169940747584647075)
              ·
                refine ⟨864249254911121376970613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576166169940747584647075 864249254911121376970613)
                ·
                  refine ⟨81023367647917629090995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 864249254911121376970613 81023367647917629090995)
                  ·
                    rfl

theorem cell21_355033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_355033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355033 prefixEnd_355033 := by exact prefixLift 355033
  have htrace : WordTrace (prefixWord ++ tailWord_355033) baseStart_355033 baseEnd_355033 := by
    simpa [prefixWord, tailWord_355033, baseEnd_355033] using wordTrace_append hprefix tailTrace_355033
  have hstable : (prefixWord ++ tailWord_355033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355033).length < 2 ^ (prefixWord ++ tailWord_355033).sum := by decide
  have hdescent : baseEnd_355033 < baseStart_355033 := by decide
  rcases family_descends (prefixWord ++ tailWord_355033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355095 : List Nat := [1, 1, 3, 4, 3, 1, 2, 6]
def baseStart_355095 : Nat := 118140960795 + 355095 * 2 ^ 59
def prefixEnd_355095 : Nat := 4983230072969 + 3 ^ 40 * 355095 * 2
def baseEnd_355095 : Nat := 27012505630873099685845

theorem tailTrace_355095 : CollatzResearch.WordTrace tailWord_355095 prefixEnd_355095 27012505630873099685845 := by
  unfold tailWord_355095
  simp only [CollatzResearch.WordTrace]
  refine ⟨12951378648558935242882739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8634252432372623495255159 12951378648558935242882739)
  ·
    refine ⟨19427067972838402864324109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12951378648558935242882739 19427067972838402864324109)
    ·
      refine ⟨7285150489814401074121541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19427067972838402864324109 7285150489814401074121541)
      ·
        refine ⟨1365965716840200201397789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7285150489814401074121541 1365965716840200201397789)
        ·
          refine ⟨512237143815075075524171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1365965716840200201397789 512237143815075075524171)
          ·
            refine ⟨768355715722612613286257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512237143815075075524171 768355715722612613286257)
            ·
              refine ⟨576266786791959459964693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768355715722612613286257 576266786791959459964693)
              ·
                refine ⟨27012505630873099685845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 576266786791959459964693 27012505630873099685845)
                ·
                  rfl

theorem cell21_355095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_355095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355095 prefixEnd_355095 := by exact prefixLift 355095
  have htrace : WordTrace (prefixWord ++ tailWord_355095) baseStart_355095 baseEnd_355095 := by
    simpa [prefixWord, tailWord_355095, baseEnd_355095] using wordTrace_append hprefix tailTrace_355095
  have hstable : (prefixWord ++ tailWord_355095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355095).length < 2 ^ (prefixWord ++ tailWord_355095).sum := by decide
  have hdescent : baseEnd_355095 < baseStart_355095 := by decide
  rcases family_descends (prefixWord ++ tailWord_355095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355171 : List Nat := [1, 1, 1, 5, 3, 2, 3, 5]
def baseStart_355171 : Nat := 118140960795 + 355171 * 2 ^ 59
def prefixEnd_355171 : Nat := 4983230072969 + 3 ^ 40 * 355171 * 2
def baseEnd_355171 : Nat := 27018287042686685263571

theorem tailTrace_355171 : CollatzResearch.WordTrace tailWord_355171 prefixEnd_355171 27018287042686685263571 := by
  unfold tailWord_355171
  simp only [CollatzResearch.WordTrace]
  refine ⟨12954150596283600222649367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8636100397522400148432911 12954150596283600222649367)
  ·
    refine ⟨19431225894425400333974051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12954150596283600222649367 19431225894425400333974051)
    ·
      refine ⟨29146838841638100500961077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19431225894425400333974051 29146838841638100500961077)
      ·
        refine ⟨2732516141403571921965101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29146838841638100500961077 2732516141403571921965101)
        ·
          refine ⟨1024693553026339470736913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2732516141403571921965101 1024693553026339470736913)
          ·
            refine ⟨768520164769754603052685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024693553026339470736913 768520164769754603052685)
            ·
              refine ⟨288195061788657976144757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768520164769754603052685 288195061788657976144757)
              ·
                refine ⟨27018287042686685263571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288195061788657976144757 27018287042686685263571)
                ·
                  rfl

theorem cell21_355171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 5].length) (baseStart_355171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355171 prefixEnd_355171 := by exact prefixLift 355171
  have htrace : WordTrace (prefixWord ++ tailWord_355171) baseStart_355171 baseEnd_355171 := by
    simpa [prefixWord, tailWord_355171, baseEnd_355171] using wordTrace_append hprefix tailTrace_355171
  have hstable : (prefixWord ++ tailWord_355171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355171).length < 2 ^ (prefixWord ++ tailWord_355171).sum := by decide
  have hdescent : baseEnd_355171 < baseStart_355171 := by decide
  rcases family_descends (prefixWord ++ tailWord_355171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355222 : List Nat := [5, 3, 1, 1, 1, 3, 2, 5]
def baseStart_355222 : Nat := 118140960795 + 355222 * 2 ^ 59
def prefixEnd_355222 : Nat := 4983230072969 + 3 ^ 40 * 355222 * 2
def baseEnd_355222 : Nat := 27022166674298433480203

theorem tailTrace_355222 : CollatzResearch.WordTrace tailWord_355222 prefixEnd_355222 27022166674298433480203 := by
  unfold tailWord_355222
  simp only [CollatzResearch.WordTrace]
  refine ⟨809750669943677245797245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8637340479399223955170613 809750669943677245797245)
  ·
    refine ⟨303656501228878967173967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 809750669943677245797245 303656501228878967173967)
    ·
      refine ⟨455484751843318450760951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303656501228878967173967 455484751843318450760951)
      ·
        refine ⟨683227127764977676141427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455484751843318450760951 683227127764977676141427)
        ·
          refine ⟨1024840691647466514212141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683227127764977676141427 1024840691647466514212141)
          ·
            refine ⟨384315259367799942829553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1024840691647466514212141 384315259367799942829553)
            ·
              refine ⟨288236444525849957122165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384315259367799942829553 288236444525849957122165)
              ·
                refine ⟨27022166674298433480203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288236444525849957122165 27022166674298433480203)
                ·
                  rfl

theorem cell21_355222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_355222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355222 prefixEnd_355222 := by exact prefixLift 355222
  have htrace : WordTrace (prefixWord ++ tailWord_355222) baseStart_355222 baseEnd_355222 := by
    simpa [prefixWord, tailWord_355222, baseEnd_355222] using wordTrace_append hprefix tailTrace_355222
  have hstable : (prefixWord ++ tailWord_355222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355222).length < 2 ^ (prefixWord ++ tailWord_355222).sum := by decide
  have hdescent : baseEnd_355222 < baseStart_355222 := by decide
  rcases family_descends (prefixWord ++ tailWord_355222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355320 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_355320 : Nat := 118140960795 + 355320 * 2 ^ 59
def prefixEnd_355320 : Nat := 4983230072969 + 3 ^ 40 * 355320 * 2
def baseEnd_355320 : Nat := 81088864958068907807075

theorem tailTrace_355320 : CollatzResearch.WordTrace tailWord_355320 prefixEnd_355320 81088864958068907807075 := by
  unfold tailWord_355320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479792536371899334911707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8639723381829199113215609 6479792536371899334911707)
  ·
    refine ⟨9719688804557849002367561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479792536371899334911707 9719688804557849002367561)
    ·
      refine ⟨7289766603418386751775671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9719688804557849002367561 7289766603418386751775671)
      ·
        refine ⟨10934649905127580127663507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7289766603418386751775671 10934649905127580127663507)
        ·
          refine ⟨16401974857691370191495261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10934649905127580127663507 16401974857691370191495261)
          ·
            refine ⟨6150740571634263821810723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16401974857691370191495261 6150740571634263821810723)
            ·
              refine ⟨9226110857451395732716085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150740571634263821810723 9226110857451395732716085)
              ·
                refine ⟨864947892886068349942133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9226110857451395732716085 864947892886068349942133)
                ·
                  refine ⟨81088864958068907807075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 864947892886068349942133 81088864958068907807075)
                  ·
                    rfl

theorem cell21_355320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_355320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355320 prefixEnd_355320 := by exact prefixLift 355320
  have htrace : WordTrace (prefixWord ++ tailWord_355320) baseStart_355320 baseEnd_355320 := by
    simpa [prefixWord, tailWord_355320, baseEnd_355320] using wordTrace_append hprefix tailTrace_355320
  have hstable : (prefixWord ++ tailWord_355320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355320).length < 2 ^ (prefixWord ++ tailWord_355320).sum := by decide
  have hdescent : baseEnd_355320 < baseStart_355320 := by decide
  rcases family_descends (prefixWord ++ tailWord_355320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355354 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 3]
def baseStart_355354 : Nat := 118140960795 + 355354 * 2 ^ 59
def prefixEnd_355354 : Nat := 4983230072969 + 3 ^ 40 * 355354 * 2
def baseEnd_355354 : Nat := 81096624221292404240339

theorem tailTrace_355354 : CollatzResearch.WordTrace tailWord_355354 prefixEnd_355354 81096624221292404240339 := by
  unfold tailWord_355354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3240206288655155619140279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8640550103080414984374077 3240206288655155619140279)
  ·
    refine ⟨4860309432982733428710419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3240206288655155619140279 4860309432982733428710419)
    ·
      refine ⟨7290464149474100143065629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860309432982733428710419 7290464149474100143065629)
      ·
        refine ⟨2733924056052787553649611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7290464149474100143065629 2733924056052787553649611)
        ·
          refine ⟨4100886084079181330474417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733924056052787553649611 4100886084079181330474417)
          ·
            refine ⟨3075664563059385997855813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4100886084079181330474417 3075664563059385997855813)
            ·
              refine ⟨576687105573634874597965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3075664563059385997855813 576687105573634874597965)
              ·
                refine ⟨216257664590113077974237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 576687105573634874597965 216257664590113077974237)
                ·
                  refine ⟨81096624221292404240339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216257664590113077974237 81096624221292404240339)
                  ·
                    rfl

theorem cell21_355354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_355354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355354 prefixEnd_355354 := by exact prefixLift 355354
  have htrace : WordTrace (prefixWord ++ tailWord_355354) baseStart_355354 baseEnd_355354 := by
    simpa [prefixWord, tailWord_355354, baseEnd_355354] using wordTrace_append hprefix tailTrace_355354
  have hstable : (prefixWord ++ tailWord_355354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355354).length < 2 ^ (prefixWord ++ tailWord_355354).sum := by decide
  have hdescent : baseEnd_355354 < baseStart_355354 := by decide
  rcases family_descends (prefixWord ++ tailWord_355354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355365 : List Nat := [1, 3, 1, 2, 2, 2, 10]
def baseStart_355365 : Nat := 118140960795 + 355365 * 2 ^ 59
def prefixEnd_355365 : Nat := 4983230072969 + 3 ^ 40 * 355365 * 2
def baseEnd_355365 : Nat := 9011014952350981061887

theorem tailTrace_355365 : CollatzResearch.WordTrace tailWord_355365 prefixEnd_355365 9011014952350981061887 := by
  unfold tailWord_355365
  simp only [CollatzResearch.WordTrace]
  refine ⟨12961226357580771355211549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8640817571720514236807699 12961226357580771355211549)
  ·
    refine ⟨4860459884092789258204331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12961226357580771355211549 4860459884092789258204331)
    ·
      refine ⟨7290689826139183887306497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860459884092789258204331 7290689826139183887306497)
      ·
        refine ⟨5468017369604387915479873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7290689826139183887306497 5468017369604387915479873)
        ·
          refine ⟨4101013027203290936609905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5468017369604387915479873 4101013027203290936609905)
          ·
            refine ⟨3075759770402468202457429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4101013027203290936609905 3075759770402468202457429)
            ·
              refine ⟨9011014952350981061887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3075759770402468202457429 9011014952350981061887)
              ·
                rfl

theorem cell21_355365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 10].length) (baseStart_355365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355365 prefixEnd_355365 := by exact prefixLift 355365
  have htrace : WordTrace (prefixWord ++ tailWord_355365) baseStart_355365 baseEnd_355365 := by
    simpa [prefixWord, tailWord_355365, baseEnd_355365] using wordTrace_append hprefix tailTrace_355365
  have hstable : (prefixWord ++ tailWord_355365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355365).length < 2 ^ (prefixWord ++ tailWord_355365).sum := by decide
  have hdescent : baseEnd_355365 < baseStart_355365 := by decide
  rcases family_descends (prefixWord ++ tailWord_355365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355385 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 4]
def baseStart_355385 : Nat := 118140960795 + 355385 * 2 ^ 59
def prefixEnd_355385 : Nat := 4983230072969 + 3 ^ 40 * 355385 * 2
def baseEnd_355385 : Nat := 81103698843643239223609

theorem tailTrace_355385 : CollatzResearch.WordTrace tailWord_355385 prefixEnd_355385 81103698843643239223609 := by
  unfold tailWord_355385
  simp only [CollatzResearch.WordTrace]
  refine ⟨12961955817508314770939609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8641303878338876513959739 12961955817508314770939609)
  ·
    refine ⟨9721466863131236078204707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12961955817508314770939609 9721466863131236078204707)
    ·
      refine ⟨14582200294696854117307061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9721466863131236078204707 14582200294696854117307061)
      ·
        refine ⟨1367081277627830073497537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14582200294696854117307061 1367081277627830073497537)
        ·
          refine ⟨1025310958220872555123153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1367081277627830073497537 1025310958220872555123153)
          ·
            refine ⟨768983218665654416342365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025310958220872555123153 768983218665654416342365)
            ·
              refine ⟨288368706999620406128387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768983218665654416342365 288368706999620406128387)
              ·
                refine ⟨432553060499430609192581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288368706999620406128387 432553060499430609192581)
                ·
                  refine ⟨81103698843643239223609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432553060499430609192581 81103698843643239223609)
                  ·
                    rfl

theorem cell21_355385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_355385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355385 prefixEnd_355385 := by exact prefixLift 355385
  have htrace : WordTrace (prefixWord ++ tailWord_355385) baseStart_355385 baseEnd_355385 := by
    simpa [prefixWord, tailWord_355385, baseEnd_355385] using wordTrace_append hprefix tailTrace_355385
  have hstable : (prefixWord ++ tailWord_355385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355385).length < 2 ^ (prefixWord ++ tailWord_355385).sum := by decide
  have hdescent : baseEnd_355385 < baseStart_355385 := by decide
  rcases family_descends (prefixWord ++ tailWord_355385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355399 : List Nat := [1, 1, 4, 1, 3, 4, 2, 5]
def baseStart_355399 : Nat := 118140960795 + 355399 * 2 ^ 59
def prefixEnd_355399 : Nat := 4983230072969 + 3 ^ 40 * 355399 * 2
def baseEnd_355399 : Nat := 27035631278127441996749

theorem tailTrace_355399 : CollatzResearch.WordTrace tailWord_355399 prefixEnd_355399 27035631278127441996749 := by
  unfold tailWord_355399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12962466439457595161949251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8641644292971730107966167 12962466439457595161949251)
  ·
    refine ⟨19443699659186392742923877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12962466439457595161949251 19443699659186392742923877)
    ·
      refine ⟨3645693686097448639298227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19443699659186392742923877 3645693686097448639298227)
      ·
        refine ⟨5468540529146172958947341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645693686097448639298227 5468540529146172958947341)
        ·
          refine ⟨2050702698429814859605253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5468540529146172958947341 2050702698429814859605253)
          ·
            refine ⟨384506755955590286175985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2050702698429814859605253 384506755955590286175985)
            ·
              refine ⟨288380066966692714631989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384506755955590286175985 288380066966692714631989)
              ·
                refine ⟨27035631278127441996749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288380066966692714631989 27035631278127441996749)
                ·
                  rfl

theorem cell21_355399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 5].length) (baseStart_355399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355399 prefixEnd_355399 := by exact prefixLift 355399
  have htrace : WordTrace (prefixWord ++ tailWord_355399) baseStart_355399 baseEnd_355399 := by
    simpa [prefixWord, tailWord_355399, baseEnd_355399] using wordTrace_append hprefix tailTrace_355399
  have hstable : (prefixWord ++ tailWord_355399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355399).length < 2 ^ (prefixWord ++ tailWord_355399).sum := by decide
  have hdescent : baseEnd_355399 < baseStart_355399 := by decide
  rcases family_descends (prefixWord ++ tailWord_355399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355427 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 4]
def baseStart_355427 : Nat := 118140960795 + 355427 * 2 ^ 59
def prefixEnd_355427 : Nat := 4983230072969 + 3 ^ 40 * 355427 * 2
def baseEnd_355427 : Nat := 81113283815860499523523

theorem tailTrace_355427 : CollatzResearch.WordTrace tailWord_355427 prefixEnd_355427 81113283815860499523523 := by
  unfold tailWord_355427
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963487683356155943968535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8642325122237437295979023 12963487683356155943968535)
  ·
    refine ⟨19445231525034233915952803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12963487683356155943968535 19445231525034233915952803)
    ·
      refine ⟨29167847287551350873929205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19445231525034233915952803 29167847287551350873929205)
      ·
        refine ⟨2734485683207939144430863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29167847287551350873929205 2734485683207939144430863)
        ·
          refine ⟨4101728524811908716646295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734485683207939144430863 4101728524811908716646295)
          ·
            refine ⟨6152592787217863074969443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101728524811908716646295 6152592787217863074969443)
            ·
              refine ⟨9228889180826794612454165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152592787217863074969443 9228889180826794612454165)
              ·
                refine ⟨432604180351255997458789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9228889180826794612454165 432604180351255997458789)
                ·
                  refine ⟨81113283815860499523523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432604180351255997458789 81113283815860499523523)
                  ·
                    rfl

theorem cell21_355427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_355427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355427 prefixEnd_355427 := by exact prefixLift 355427
  have htrace : WordTrace (prefixWord ++ tailWord_355427) baseStart_355427 baseEnd_355427 := by
    simpa [prefixWord, tailWord_355427, baseEnd_355427] using wordTrace_append hprefix tailTrace_355427
  have hstable : (prefixWord ++ tailWord_355427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355427).length < 2 ^ (prefixWord ++ tailWord_355427).sum := by decide
  have hdescent : baseEnd_355427 < baseStart_355427 := by decide
  rcases family_descends (prefixWord ++ tailWord_355427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355503 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 4]
def baseStart_355503 : Nat := 118140960795 + 355503 * 2 ^ 59
def prefixEnd_355503 : Nat := 4983230072969 + 3 ^ 40 * 355503 * 2
def baseEnd_355503 : Nat := 81130628051301256256701

theorem tailTrace_355503 : CollatzResearch.WordTrace tailWord_355503 prefixEnd_355503 81130628051301256256701 := by
  unfold tailWord_355503
  simp only [CollatzResearch.WordTrace]
  refine ⟨12966259631080820923735163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8644173087387213949156775 12966259631080820923735163)
  ·
    refine ⟨19449389446621231385602745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12966259631080820923735163 19449389446621231385602745)
    ·
      refine ⟨14587042084965923539202059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19449389446621231385602745 14587042084965923539202059)
      ·
        refine ⟨21880563127448885308803089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14587042084965923539202059 21880563127448885308803089)
        ·
          refine ⟨16410422345586663981602317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21880563127448885308803089 16410422345586663981602317)
          ·
            refine ⟨6153908379594998993100869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16410422345586663981602317 6153908379594998993100869)
            ·
              refine ⟨1153857821174062311206413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6153908379594998993100869 1153857821174062311206413)
              ·
                refine ⟨432696682940273366702405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1153857821174062311206413 432696682940273366702405)
                ·
                  refine ⟨81130628051301256256701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432696682940273366702405 81130628051301256256701)
                  ·
                    rfl

theorem cell21_355503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_355503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355503 prefixEnd_355503 := by exact prefixLift 355503
  have htrace : WordTrace (prefixWord ++ tailWord_355503) baseStart_355503 baseEnd_355503 := by
    simpa [prefixWord, tailWord_355503, baseEnd_355503] using wordTrace_append hprefix tailTrace_355503
  have hstable : (prefixWord ++ tailWord_355503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355503).length < 2 ^ (prefixWord ++ tailWord_355503).sum := by decide
  have hdescent : baseEnd_355503 < baseStart_355503 := by decide
  rcases family_descends (prefixWord ++ tailWord_355503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355517 : List Nat := [1, 4, 1, 2, 1, 1, 2, 9]
def baseStart_355517 : Nat := 118140960795 + 355517 * 2 ^ 59
def prefixEnd_355517 : Nat := 4983230072969 + 3 ^ 40 * 355517 * 2
def baseEnd_355517 : Nat := 27044607680680114341113

theorem tailTrace_355517 : CollatzResearch.WordTrace tailWord_355517 prefixEnd_355517 27044607680680114341113 := by
  unfold tailWord_355517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12966770253030101314744805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8644513502020067543163203 12966770253030101314744805)
  ·
    refine ⟨2431269422443143996514651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12966770253030101314744805 2431269422443143996514651)
    ·
      refine ⟨3646904133664715994771977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431269422443143996514651 3646904133664715994771977)
      ·
        refine ⟨2735178100248536996078983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3646904133664715994771977 2735178100248536996078983)
        ·
          refine ⟨4102767150372805494118475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735178100248536996078983 4102767150372805494118475)
          ·
            refine ⟨6154150725559208241177713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102767150372805494118475 6154150725559208241177713)
            ·
              refine ⟨4615613044169406180883285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6154150725559208241177713 4615613044169406180883285)
              ·
                refine ⟨27044607680680114341113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4615613044169406180883285 27044607680680114341113)
                ·
                  rfl

theorem cell21_355517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 9].length) (baseStart_355517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355517 prefixEnd_355517 := by exact prefixLift 355517
  have htrace : WordTrace (prefixWord ++ tailWord_355517) baseStart_355517 baseEnd_355517 := by
    simpa [prefixWord, tailWord_355517, baseEnd_355517] using wordTrace_append hprefix tailTrace_355517
  have hstable : (prefixWord ++ tailWord_355517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355517).length < 2 ^ (prefixWord ++ tailWord_355517).sum := by decide
  have hdescent : baseEnd_355517 < baseStart_355517 := by decide
  rcases family_descends (prefixWord ++ tailWord_355517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355534 : List Nat := [4, 1, 1, 1, 5, 1, 8]
def baseStart_355534 : Nat := 118140960795 + 355534 * 2 ^ 59
def prefixEnd_355534 : Nat := 4983230072969 + 3 ^ 40 * 355534 * 2
def baseEnd_355534 : Nat := 9015300297072454582219

theorem tailTrace_355534 : CollatzResearch.WordTrace tailWord_355534 prefixEnd_355534 9015300297072454582219 := by
  unfold tailWord_355534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620923786746064152264207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8644926862645675478742437 1620923786746064152264207)
  ·
    refine ⟨2431385680119096228396311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620923786746064152264207 2431385680119096228396311)
    ·
      refine ⟨3647078520178644342594467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431385680119096228396311 3647078520178644342594467)
      ·
        refine ⟨5470617780267966513891701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647078520178644342594467 5470617780267966513891701)
        ·
          refine ⟨512870416900121860677347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5470617780267966513891701 512870416900121860677347)
          ·
            refine ⟨769305625350182791016021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512870416900121860677347 769305625350182791016021)
            ·
              refine ⟨9015300297072454582219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 769305625350182791016021 9015300297072454582219)
              ·
                rfl

theorem cell21_355534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 8].length) (baseStart_355534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355534 prefixEnd_355534 := by exact prefixLift 355534
  have htrace : WordTrace (prefixWord ++ tailWord_355534) baseStart_355534 baseEnd_355534 := by
    simpa [prefixWord, tailWord_355534, baseEnd_355534] using wordTrace_append hprefix tailTrace_355534
  have hstable : (prefixWord ++ tailWord_355534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355534).length < 2 ^ (prefixWord ++ tailWord_355534).sum := by decide
  have hdescent : baseEnd_355534 < baseStart_355534 := by decide
  rcases family_descends (prefixWord ++ tailWord_355534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355565 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 5]
def baseStart_355565 : Nat := 118140960795 + 355565 * 2 ^ 59
def prefixEnd_355565 : Nat := 4983230072969 + 3 ^ 40 * 355565 * 2
def baseEnd_355565 : Nat := 81144777296002926223241

theorem tailTrace_355565 : CollatzResearch.WordTrace tailWord_355565 prefixEnd_355565 81144777296002926223241 := by
  unfold tailWord_355565
  simp only [CollatzResearch.WordTrace]
  refine ⟨12968520956856205512492149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8645680637904137008328099 12968520956856205512492149)
  ·
    refine ⟨1215798839705269266796139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12968520956856205512492149 1215798839705269266796139)
    ·
      refine ⟨1823698259557903900194209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1215798839705269266796139 1823698259557903900194209)
      ·
        refine ⟨1367773694668427925145657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1823698259557903900194209 1367773694668427925145657)
        ·
          refine ⟨1025830271001320943859243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1367773694668427925145657 1025830271001320943859243)
          ·
            refine ⟨1538745406501981415788865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025830271001320943859243 1538745406501981415788865)
            ·
              refine ⟨1154059054876486061841649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538745406501981415788865 1154059054876486061841649)
              ·
                refine ⟨865544291157364546381237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154059054876486061841649 865544291157364546381237)
                ·
                  refine ⟨81144777296002926223241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 865544291157364546381237 81144777296002926223241)
                  ·
                    rfl

theorem cell21_355565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_355565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355565 prefixEnd_355565 := by exact prefixLift 355565
  have htrace : WordTrace (prefixWord ++ tailWord_355565) baseStart_355565 baseEnd_355565 := by
    simpa [prefixWord, tailWord_355565, baseEnd_355565] using wordTrace_append hprefix tailTrace_355565
  have hstable : (prefixWord ++ tailWord_355565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355565).length < 2 ^ (prefixWord ++ tailWord_355565).sum := by decide
  have hdescent : baseEnd_355565 < baseStart_355565 := by decide
  rcases family_descends (prefixWord ++ tailWord_355565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355610 : List Nat := [3, 1, 1, 3, 3, 2, 2, 6]
def baseStart_355610 : Nat := 118140960795 + 355610 * 2 ^ 59
def prefixEnd_355610 : Nat := 4983230072969 + 3 ^ 40 * 355610 * 2
def baseEnd_355610 : Nat := 27051682303030949324383

theorem tailTrace_355610 : CollatzResearch.WordTrace tailWord_355610 prefixEnd_355610 27051682303030949324383 := by
  unfold tailWord_355610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242540560423294549470071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8646774827795452131920189 3242540560423294549470071)
  ·
    refine ⟨4863810840634941824205107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242540560423294549470071 4863810840634941824205107)
    ·
      refine ⟨7295716260952412736307661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4863810840634941824205107 7295716260952412736307661)
      ·
        refine ⟨2735893597857154776115373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7295716260952412736307661 2735893597857154776115373)
        ·
          refine ⟨1025960099196433041043265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2735893597857154776115373 1025960099196433041043265)
          ·
            refine ⟨769470074397324780782449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025960099196433041043265 769470074397324780782449)
            ·
              refine ⟨577102555797993585586837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769470074397324780782449 577102555797993585586837)
              ·
                refine ⟨27051682303030949324383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 577102555797993585586837 27051682303030949324383)
                ·
                  rfl

theorem cell21_355610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_355610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355610 prefixEnd_355610 := by exact prefixLift 355610
  have htrace : WordTrace (prefixWord ++ tailWord_355610) baseStart_355610 baseEnd_355610 := by
    simpa [prefixWord, tailWord_355610, baseEnd_355610] using wordTrace_append hprefix tailTrace_355610
  have hstable : (prefixWord ++ tailWord_355610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355610).length < 2 ^ (prefixWord ++ tailWord_355610).sum := by decide
  have hdescent : baseEnd_355610 < baseStart_355610 := by decide
  rcases family_descends (prefixWord ++ tailWord_355610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355613 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 4]
def baseStart_355613 : Nat := 118140960795 + 355613 * 2 ^ 59
def prefixEnd_355613 : Nat := 4983230072969 + 3 ^ 40 * 355613 * 2
def baseEnd_355613 : Nat := 81155731549965509423143

theorem tailTrace_355613 : CollatzResearch.WordTrace tailWord_355613 prefixEnd_355613 81155731549965509423143 := by
  unfold tailWord_355613
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970271660682309710239493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8646847773788206473492995 12970271660682309710239493)
  ·
    refine ⟨2431925936377933070669905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12970271660682309710239493 2431925936377933070669905)
    ·
      refine ⟨1823944452283449803002429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2431925936377933070669905 1823944452283449803002429)
      ·
        refine ⟨683979169606293676125911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1823944452283449803002429 683979169606293676125911)
        ·
          refine ⟨1025968754409440514188867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683979169606293676125911 1025968754409440514188867)
          ·
            refine ⟨1538953131614160771283301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025968754409440514188867 1538953131614160771283301)
            ·
              refine ⟨288553712177655144615619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1538953131614160771283301 288553712177655144615619)
              ·
                refine ⟨432830568266482716923429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288553712177655144615619 432830568266482716923429)
                ·
                  refine ⟨81155731549965509423143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432830568266482716923429 81155731549965509423143)
                  ·
                    rfl

theorem cell21_355613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_355613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355613 prefixEnd_355613 := by exact prefixLift 355613
  have htrace : WordTrace (prefixWord ++ tailWord_355613) baseStart_355613 baseEnd_355613 := by
    simpa [prefixWord, tailWord_355613, baseEnd_355613] using wordTrace_append hprefix tailTrace_355613
  have hstable : (prefixWord ++ tailWord_355613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355613).length < 2 ^ (prefixWord ++ tailWord_355613).sum := by decide
  have hdescent : baseEnd_355613 < baseStart_355613 := by decide
  rcases family_descends (prefixWord ++ tailWord_355613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355655 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 4]
def baseStart_355655 : Nat := 118140960795 + 355655 * 2 ^ 59
def prefixEnd_355655 : Nat := 4983230072969 + 3 ^ 40 * 355655 * 2
def baseEnd_355655 : Nat := 81165316522182769723057

theorem tailTrace_355655 : CollatzResearch.WordTrace tailWord_355655 prefixEnd_355655 81165316522182769723057 := by
  unfold tailWord_355655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12971803526530150883268419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8647869017686767255512279 12971803526530150883268419)
  ·
    refine ⟨19457705289795226324902629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12971803526530150883268419 19457705289795226324902629)
    ·
      refine ⟨3648319741836604935919243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19457705289795226324902629 3648319741836604935919243)
      ·
        refine ⟨5472479612754907403878865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648319741836604935919243 5472479612754907403878865)
        ·
          refine ⟨4104359709566180552909149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5472479612754907403878865 4104359709566180552909149)
          ·
            refine ⟨1539134891087317707340931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4104359709566180552909149 1539134891087317707340931)
            ·
              refine ⟨2308702336630976561011397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539134891087317707340931 2308702336630976561011397)
              ·
                refine ⟨432881688118308105189637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2308702336630976561011397 432881688118308105189637)
                ·
                  refine ⟨81165316522182769723057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432881688118308105189637 81165316522182769723057)
                  ·
                    rfl

theorem cell21_355655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_355655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355655 prefixEnd_355655 := by exact prefixLift 355655
  have htrace : WordTrace (prefixWord ++ tailWord_355655) baseStart_355655 baseEnd_355655 := by
    simpa [prefixWord, tailWord_355655, baseEnd_355655] using wordTrace_append hprefix tailTrace_355655
  have hstable : (prefixWord ++ tailWord_355655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355655).length < 2 ^ (prefixWord ++ tailWord_355655).sum := by decide
  have hdescent : baseEnd_355655 < baseStart_355655 := by decide
  rcases family_descends (prefixWord ++ tailWord_355655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355661 : List Nat := [1, 6, 1, 3, 2, 1, 1, 6]
def baseStart_355661 : Nat := 118140960795 + 355661 * 2 ^ 59
def prefixEnd_355661 : Nat := 4983230072969 + 3 ^ 40 * 355661 * 2
def baseEnd_355661 : Nat := 27055561934642697541015

theorem tailTrace_355661 : CollatzResearch.WordTrace tailWord_355661 prefixEnd_355661 27055561934642697541015 := by
  unfold tailWord_355661
  simp only [CollatzResearch.WordTrace]
  refine ⟨12972022364508413907986837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8648014909672275938657891 12972022364508413907986837)
  ·
    refine ⟨608063548336331901936883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12972022364508413907986837 608063548336331901936883)
    ·
      refine ⟨912095322504497852905325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608063548336331901936883 912095322504497852905325)
      ·
        refine ⟨342035745939186694839497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 912095322504497852905325 342035745939186694839497)
        ·
          refine ⟨256526809454390021129623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342035745939186694839497 256526809454390021129623)
          ·
            refine ⟨384790214181585031694435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256526809454390021129623 384790214181585031694435)
            ·
              refine ⟨577185321272377547541653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384790214181585031694435 577185321272377547541653)
              ·
                refine ⟨27055561934642697541015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 577185321272377547541653 27055561934642697541015)
                ·
                  rfl

theorem cell21_355661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 6].length) (baseStart_355661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355661 prefixEnd_355661 := by exact prefixLift 355661
  have htrace : WordTrace (prefixWord ++ tailWord_355661) baseStart_355661 baseEnd_355661 := by
    simpa [prefixWord, tailWord_355661, baseEnd_355661] using wordTrace_append hprefix tailTrace_355661
  have hstable : (prefixWord ++ tailWord_355661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355661).length < 2 ^ (prefixWord ++ tailWord_355661).sum := by decide
  have hdescent : baseEnd_355661 < baseStart_355661 := by decide
  rcases family_descends (prefixWord ++ tailWord_355661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355717 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 3]
def baseStart_355717 : Nat := 118140960795 + 355717 * 2 ^ 59
def prefixEnd_355717 : Nat := 4983230072969 + 3 ^ 40 * 355717 * 2
def baseEnd_355717 : Nat := 81179465766884439689597

theorem tailTrace_355717 : CollatzResearch.WordTrace tailWord_355717 prefixEnd_355717 81179465766884439689597 := by
  unfold tailWord_355717
  simp only [CollatzResearch.WordTrace]
  refine ⟨12974064852305535472025405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8649376568203690314683603 12974064852305535472025405)
  ·
    refine ⟨4865274319614575802009527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12974064852305535472025405 4865274319614575802009527)
    ·
      refine ⟨7297911479421863703014291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865274319614575802009527 7297911479421863703014291)
      ·
        refine ⟨10946867219132795554521437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297911479421863703014291 10946867219132795554521437)
        ·
          refine ⟨4105075207174798332945539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10946867219132795554521437 4105075207174798332945539)
          ·
            refine ⟨6157612810762197499418309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105075207174798332945539 6157612810762197499418309)
            ·
              refine ⟨1154552402017912031140933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6157612810762197499418309 1154552402017912031140933)
              ·
                refine ⟨216478575378358505838925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1154552402017912031140933 216478575378358505838925)
                ·
                  refine ⟨81179465766884439689597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216478575378358505838925 81179465766884439689597)
                  ·
                    rfl

theorem cell21_355717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_355717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355717 prefixEnd_355717 := by exact prefixLift 355717
  have htrace : WordTrace (prefixWord ++ tailWord_355717) baseStart_355717 baseEnd_355717 := by
    simpa [prefixWord, tailWord_355717, baseEnd_355717] using wordTrace_append hprefix tailTrace_355717
  have hstable : (prefixWord ++ tailWord_355717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355717).length < 2 ^ (prefixWord ++ tailWord_355717).sum := by decide
  have hdescent : baseEnd_355717 < baseStart_355717 := by decide
  rcases family_descends (prefixWord ++ tailWord_355717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355759 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_355759 : Nat := 118140960795 + 355759 * 2 ^ 59
def prefixEnd_355759 : Nat := 4983230072969 + 3 ^ 40 * 355759 * 2
def baseEnd_355759 : Nat := 81189050739101699989511

theorem tailTrace_355759 : CollatzResearch.WordTrace tailWord_355759 prefixEnd_355759 81189050739101699989511 := by
  unfold tailWord_355759
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975596718153376645054331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8650397812102251096702887 12975596718153376645054331)
  ·
    refine ⟨19463395077230064967581497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12975596718153376645054331 19463395077230064967581497)
    ·
      refine ⟨14597546307922548725686123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19463395077230064967581497 14597546307922548725686123)
      ·
        refine ⟨21896319461883823088529185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14597546307922548725686123 21896319461883823088529185)
        ·
          refine ⟨16422239596412867316396889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21896319461883823088529185 16422239596412867316396889)
          ·
            refine ⟨12316679697309650487297667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16422239596412867316396889 12316679697309650487297667)
            ·
              refine ⟨18475019545964475730946501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12316679697309650487297667 18475019545964475730946501)
              ·
                refine ⟨3464066164868339199552469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18475019545964475730946501 3464066164868339199552469)
                ·
                  refine ⟨81189050739101699989511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3464066164868339199552469 81189050739101699989511)
                  ·
                    rfl

theorem cell21_355759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_355759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355759 prefixEnd_355759 := by exact prefixLift 355759
  have htrace : WordTrace (prefixWord ++ tailWord_355759) baseStart_355759 baseEnd_355759 := by
    simpa [prefixWord, tailWord_355759, baseEnd_355759] using wordTrace_append hprefix tailTrace_355759
  have hstable : (prefixWord ++ tailWord_355759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355759).length < 2 ^ (prefixWord ++ tailWord_355759).sum := by decide
  have hdescent : baseEnd_355759 < baseStart_355759 := by decide
  rcases family_descends (prefixWord ++ tailWord_355759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355776 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_355776 : Nat := 118140960795 + 355776 * 2 ^ 59
def prefixEnd_355776 : Nat := 4983230072969 + 3 ^ 40 * 355776 * 2
def baseEnd_355776 : Nat := 81192930370713448206143

theorem tailTrace_355776 : CollatzResearch.WordTrace tailWord_355776 prefixEnd_355776 81192930370713448206143 := by
  unfold tailWord_355776
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488108379545894274211591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8650811172727859032282121 6488108379545894274211591)
  ·
    refine ⟨9732162569318841411317387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6488108379545894274211591 9732162569318841411317387)
    ·
      refine ⟨14598243853978262116976081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9732162569318841411317387 14598243853978262116976081)
      ·
        refine ⟨10948682890483696587732061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14598243853978262116976081 10948682890483696587732061)
        ·
          refine ⟨4105756083931386220399523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10948682890483696587732061 4105756083931386220399523)
          ·
            refine ⟨6158634125897079330599285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105756083931386220399523 6158634125897079330599285)
            ·
              refine ⟨577371949302851187243683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6158634125897079330599285 577371949302851187243683)
              ·
                refine ⟨866057923954276780865525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577371949302851187243683 866057923954276780865525)
                ·
                  refine ⟨81192930370713448206143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866057923954276780865525 81192930370713448206143)
                  ·
                    rfl

theorem cell21_355776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_355776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355776 prefixEnd_355776 := by exact prefixLift 355776
  have htrace : WordTrace (prefixWord ++ tailWord_355776) baseStart_355776 baseEnd_355776 := by
    simpa [prefixWord, tailWord_355776, baseEnd_355776] using wordTrace_append hprefix tailTrace_355776
  have hstable : (prefixWord ++ tailWord_355776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355776).length < 2 ^ (prefixWord ++ tailWord_355776).sum := by decide
  have hdescent : baseEnd_355776 < baseStart_355776 := by decide
  rcases family_descends (prefixWord ++ tailWord_355776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355821 : List Nat := [1, 5, 1, 3, 11]
def baseStart_355821 : Nat := 118140960795 + 355821 * 2 ^ 59
def prefixEnd_355821 : Nat := 4983230072969 + 3 ^ 40 * 355821 * 2
def baseEnd_355821 : Nat := 1002508641775350246371

theorem tailTrace_355821 : CollatzResearch.WordTrace tailWord_355821 prefixEnd_355821 1002508641775350246371 := by
  unfold tailWord_355821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12977858043928761233811317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8651905362619174155874211 12977858043928761233811317)
  ·
    refine ⟨1216674191618321365669811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12977858043928761233811317 1216674191618321365669811)
    ·
      refine ⟨1825011287427482048504717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216674191618321365669811 1825011287427482048504717)
      ·
        refine ⟨684379232785305768189269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1825011287427482048504717 684379232785305768189269)
        ·
          refine ⟨1002508641775350246371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 684379232785305768189269 1002508641775350246371)
          ·
            rfl

theorem cell21_355821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 11].length) (baseStart_355821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355821 prefixEnd_355821 := by exact prefixLift 355821
  have htrace : WordTrace (prefixWord ++ tailWord_355821) baseStart_355821 baseEnd_355821 := by
    simpa [prefixWord, tailWord_355821, baseEnd_355821] using wordTrace_append hprefix tailTrace_355821
  have hstable : (prefixWord ++ tailWord_355821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355821).length < 2 ^ (prefixWord ++ tailWord_355821).sum := by decide
  have hdescent : baseEnd_355821 < baseStart_355821 := by decide
  rcases family_descends (prefixWord ++ tailWord_355821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355866 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_355866 : Nat := 118140960795 + 355866 * 2 ^ 59
def prefixEnd_355866 : Nat := 4983230072969 + 3 ^ 40 * 355866 * 2
def baseEnd_355866 : Nat := 81213469596893291705959

theorem tailTrace_355866 : CollatzResearch.WordTrace tailWord_355866 prefixEnd_355866 81213469596893291705959 := by
  unfold tailWord_355866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244874832191433479799863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8652999552510489279466301 3244874832191433479799863)
  ·
    refine ⟨4867312248287150219699795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3244874832191433479799863 4867312248287150219699795)
    ·
      refine ⟨7300968372430725329549693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867312248287150219699795 7300968372430725329549693)
      ·
        refine ⟨2737863139661521998581135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7300968372430725329549693 2737863139661521998581135)
        ·
          refine ⟨4106794709492282997871703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737863139661521998581135 4106794709492282997871703)
          ·
            refine ⟨6160192064238424496807555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106794709492282997871703 6160192064238424496807555)
            ·
              refine ⟨9240288096357636745211333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160192064238424496807555 9240288096357636745211333)
              ·
                refine ⟨1732554018067056889727125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9240288096357636745211333 1732554018067056889727125)
                ·
                  refine ⟨81213469596893291705959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1732554018067056889727125 81213469596893291705959)
                  ·
                    rfl

theorem cell21_355866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_355866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355866 prefixEnd_355866 := by exact prefixLift 355866
  have htrace : WordTrace (prefixWord ++ tailWord_355866) baseStart_355866 baseEnd_355866 := by
    simpa [prefixWord, tailWord_355866, baseEnd_355866] using wordTrace_append hprefix tailTrace_355866
  have hstable : (prefixWord ++ tailWord_355866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355866).length < 2 ^ (prefixWord ++ tailWord_355866).sum := by decide
  have hdescent : baseEnd_355866 < baseStart_355866 := by decide
  rcases family_descends (prefixWord ++ tailWord_355866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355886 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_355886 : Nat := 118140960795 + 355886 * 2 ^ 59
def prefixEnd_355886 : Nat := 4983230072969 + 3 ^ 40 * 355886 * 2
def baseEnd_355886 : Nat := 81218033869377701372585

theorem tailTrace_355886 : CollatzResearch.WordTrace tailWord_355886 prefixEnd_355886 81218033869377701372585 := by
  unfold tailWord_355886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1622528598586659666865939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8653485859128851556618341 1622528598586659666865939)
  ·
    refine ⟨2433792897879989500298909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1622528598586659666865939 2433792897879989500298909)
    ·
      refine ⟨912672336704996062612091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2433792897879989500298909 912672336704996062612091)
      ·
        refine ⟨1369008505057494093918137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912672336704996062612091 1369008505057494093918137)
        ·
          refine ⟨1026756378793120570438603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1369008505057494093918137 1026756378793120570438603)
          ·
            refine ⟨1540134568189680855657905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026756378793120570438603 1540134568189680855657905)
            ·
              refine ⟨1155100926142260641743429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540134568189680855657905 1155100926142260641743429)
              ·
                refine ⟨216581423651673870326893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1155100926142260641743429 216581423651673870326893)
                ·
                  refine ⟨81218033869377701372585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216581423651673870326893 81218033869377701372585)
                  ·
                    rfl

theorem cell21_355886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_355886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355886 prefixEnd_355886 := by exact prefixLift 355886
  have htrace : WordTrace (prefixWord ++ tailWord_355886) baseStart_355886 baseEnd_355886 := by
    simpa [prefixWord, tailWord_355886, baseEnd_355886] using wordTrace_append hprefix tailTrace_355886
  have hstable : (prefixWord ++ tailWord_355886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355886).length < 2 ^ (prefixWord ++ tailWord_355886).sum := by decide
  have hdescent : baseEnd_355886 < baseStart_355886 := by decide
  rcases family_descends (prefixWord ++ tailWord_355886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355996 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_355996 : Nat := 118140960795 + 355996 * 2 ^ 59
def prefixEnd_355996 : Nat := 4983230072969 + 3 ^ 40 * 355996 * 2
def baseEnd_355996 : Nat := 81243137368041954539027

theorem tailTrace_355996 : CollatzResearch.WordTrace tailWord_355996 prefixEnd_355996 81243137368041954539027 := by
  unfold tailWord_355996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6492120409147383060715921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8656160545529844080954561 6492120409147383060715921)
  ·
    refine ⟨4869090306860537295536941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6492120409147383060715921 4869090306860537295536941)
    ·
      refine ⟨1825908865072701485826353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4869090306860537295536941 1825908865072701485826353)
      ·
        refine ⟨1369431648804526114369765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1825908865072701485826353 1369431648804526114369765)
        ·
          refine ⟨256768434150848646444331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1369431648804526114369765 256768434150848646444331)
          ·
            refine ⟨385152651226272969666497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256768434150848646444331 385152651226272969666497)
            ·
              refine ⟨288864488419704727249873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385152651226272969666497 288864488419704727249873)
              ·
                refine ⟨216648366314778545437405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288864488419704727249873 216648366314778545437405)
                ·
                  refine ⟨81243137368041954539027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216648366314778545437405 81243137368041954539027)
                  ·
                    rfl

theorem cell21_355996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_355996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_355996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_355996 prefixEnd_355996 := by exact prefixLift 355996
  have htrace : WordTrace (prefixWord ++ tailWord_355996) baseStart_355996 baseEnd_355996 := by
    simpa [prefixWord, tailWord_355996, baseEnd_355996] using wordTrace_append hprefix tailTrace_355996
  have hstable : (prefixWord ++ tailWord_355996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355996).length < 2 ^ (prefixWord ++ tailWord_355996).sum := by decide
  have hdescent : baseEnd_355996 < baseStart_355996 := by decide
  rcases family_descends (prefixWord ++ tailWord_355996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356021 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 5]
def baseStart_356021 : Nat := 118140960795 + 356021 * 2 ^ 59
def prefixEnd_356021 : Nat := 4983230072969 + 3 ^ 40 * 356021 * 2
def baseEnd_356021 : Nat := 81248842708647466622309

theorem tailTrace_356021 : CollatzResearch.WordTrace tailWord_356021 prefixEnd_356021 81248842708647466622309 := by
  unfold tailWord_356021
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985152643204195391091917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8656768428802796927394611 12985152643204195391091917)
  ·
    refine ⟨4869432241201573271659469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12985152643204195391091917 4869432241201573271659469)
    ·
      refine ⟨1826037090450589976872301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4869432241201573271659469 1826037090450589976872301)
      ·
        refine ⟨684763908918971241327113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1826037090450589976872301 684763908918971241327113)
        ·
          refine ⟨513572931689228430995335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 684763908918971241327113 513572931689228430995335)
          ·
            refine ⟨770359397533842646493003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513572931689228430995335 770359397533842646493003)
            ·
              refine ⟨1155539096300763969739505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770359397533842646493003 1155539096300763969739505)
              ·
                refine ⟨866654322225572977304629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155539096300763969739505 866654322225572977304629)
                ·
                  refine ⟨81248842708647466622309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866654322225572977304629 81248842708647466622309)
                  ·
                    rfl

theorem cell21_356021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_356021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356021 prefixEnd_356021 := by exact prefixLift 356021
  have htrace : WordTrace (prefixWord ++ tailWord_356021) baseStart_356021 baseEnd_356021 := by
    simpa [prefixWord, tailWord_356021, baseEnd_356021] using wordTrace_append hprefix tailTrace_356021
  have hstable : (prefixWord ++ tailWord_356021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356021).length < 2 ^ (prefixWord ++ tailWord_356021).sum := by decide
  have hdescent : baseEnd_356021 < baseStart_356021 := by decide
  rcases family_descends (prefixWord ++ tailWord_356021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356052 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_356052 : Nat := 118140960795 + 356052 * 2 ^ 59
def prefixEnd_356052 : Nat := 4983230072969 + 3 ^ 40 * 356052 * 2
def baseEnd_356052 : Nat := 81255917330998301605579

theorem tailTrace_356052 : CollatzResearch.WordTrace tailWord_356052 prefixEnd_356052 81255917330998301605579 := by
  unfold tailWord_356052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6493141653045943842735205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8657522204061258456980273 6493141653045943842735205)
  ·
    refine ⟨1217464059946114470512851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6493141653045943842735205 1217464059946114470512851)
    ·
      refine ⟨1826196089919171705769277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217464059946114470512851 1826196089919171705769277)
      ·
        refine ⟨684823533719689389663479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1826196089919171705769277 684823533719689389663479)
        ·
          refine ⟨1027235300579534084495219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684823533719689389663479 1027235300579534084495219)
          ·
            refine ⟨1540852950869301126742829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1027235300579534084495219 1540852950869301126742829)
            ·
              refine ⟨577819856575987922528561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1540852950869301126742829 577819856575987922528561)
              ·
                refine ⟨433364892431990941896421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577819856575987922528561 433364892431990941896421)
                ·
                  refine ⟨81255917330998301605579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433364892431990941896421 81255917330998301605579)
                  ·
                    rfl

theorem cell21_356052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_356052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356052 prefixEnd_356052 := by exact prefixLift 356052
  have htrace : WordTrace (prefixWord ++ tailWord_356052) baseStart_356052 baseEnd_356052 := by
    simpa [prefixWord, tailWord_356052, baseEnd_356052] using wordTrace_append hprefix tailTrace_356052
  have hstable : (prefixWord ++ tailWord_356052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356052).length < 2 ^ (prefixWord ++ tailWord_356052).sum := by decide
  have hdescent : baseEnd_356052 < baseStart_356052 := by decide
  rcases family_descends (prefixWord ++ tailWord_356052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356097 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 3]
def baseStart_356097 : Nat := 118140960795 + 356097 * 2 ^ 59
def prefixEnd_356097 : Nat := 4983230072969 + 3 ^ 40 * 356097 * 2
def baseEnd_356097 : Nat := 81266186944088223355487

theorem tailTrace_356097 : CollatzResearch.WordTrace tailWord_356097 prefixEnd_356097 81266186944088223355487 := by
  unfold tailWord_356097
  simp only [CollatzResearch.WordTrace]
  refine ⟨12987924590928860370858545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8658616393952573580572363 12987924590928860370858545)
  ·
    refine ⟨9740943443196645278143909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12987924590928860370858545 9740943443196645278143909)
    ·
      refine ⟨1826426895599370989651983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9740943443196645278143909 1826426895599370989651983)
      ·
        refine ⟨2739640343399056484477975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826426895599370989651983 2739640343399056484477975)
        ·
          refine ⟨4109460515098584726716963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739640343399056484477975 4109460515098584726716963)
          ·
            refine ⟨6164190772647877090075445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109460515098584726716963 6164190772647877090075445)
            ·
              refine ⟨577892884935738477194573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6164190772647877090075445 577892884935738477194573)
              ·
                refine ⟨216709831850901928947965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 577892884935738477194573 216709831850901928947965)
                ·
                  refine ⟨81266186944088223355487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216709831850901928947965 81266186944088223355487)
                  ·
                    rfl

theorem cell21_356097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_356097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356097 prefixEnd_356097 := by exact prefixLift 356097
  have htrace : WordTrace (prefixWord ++ tailWord_356097) baseStart_356097 baseEnd_356097 := by
    simpa [prefixWord, tailWord_356097, baseEnd_356097] using wordTrace_append hprefix tailTrace_356097
  have hstable : (prefixWord ++ tailWord_356097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356097).length < 2 ^ (prefixWord ++ tailWord_356097).sum := by decide
  have hdescent : baseEnd_356097 < baseStart_356097 := by decide
  rcases family_descends (prefixWord ++ tailWord_356097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356108 : List Nat := [2, 2, 1, 2, 2, 1, 11]
def baseStart_356108 : Nat := 118140960795 + 356108 * 2 ^ 59
def prefixEnd_356108 : Nat := 4983230072969 + 3 ^ 40 * 356108 * 2
def baseEnd_356108 : Nat := 9029855254883849852459

theorem tailTrace_356108 : CollatzResearch.WordTrace tailWord_356108 prefixEnd_356108 9029855254883849852459 := by
  unfold tailWord_356108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6494162896944504624754489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8658883862592672833005985 6494162896944504624754489)
  ·
    refine ⟨4870622172708378468565867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6494162896944504624754489 4870622172708378468565867)
    ·
      refine ⟨7305933259062567702848801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4870622172708378468565867 7305933259062567702848801)
      ·
        refine ⟨5479449944296925777136601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7305933259062567702848801 5479449944296925777136601)
        ·
          refine ⟨4109587458222694332852451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5479449944296925777136601 4109587458222694332852451)
          ·
            refine ⟨6164381187334041499278677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4109587458222694332852451 6164381187334041499278677)
            ·
              refine ⟨9029855254883849852459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6164381187334041499278677 9029855254883849852459)
              ·
                rfl

theorem cell21_356108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 11].length) (baseStart_356108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356108 prefixEnd_356108 := by exact prefixLift 356108
  have htrace : WordTrace (prefixWord ++ tailWord_356108) baseStart_356108 baseEnd_356108 := by
    simpa [prefixWord, tailWord_356108, baseEnd_356108] using wordTrace_append hprefix tailTrace_356108
  have hstable : (prefixWord ++ tailWord_356108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356108).length < 2 ^ (prefixWord ++ tailWord_356108).sum := by decide
  have hdescent : baseEnd_356108 < baseStart_356108 := by decide
  rcases family_descends (prefixWord ++ tailWord_356108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356114 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_356114 : Nat := 118140960795 + 356114 * 2 ^ 59
def prefixEnd_356114 : Nat := 4983230072969 + 3 ^ 40 * 356114 * 2
def baseEnd_356114 : Nat := 81270066575699971572119

theorem tailTrace_356114 : CollatzResearch.WordTrace tailWord_356114 prefixEnd_356114 81270066575699971572119 := by
  unfold tailWord_356114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247136157966818068556849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8659029754578181516151597 3247136157966818068556849)
  ·
    refine ⟨2435352118475113551417637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3247136157966818068556849 2435352118475113551417637)
    ·
      refine ⟨456628522214083790890807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2435352118475113551417637 456628522214083790890807)
      ·
        refine ⟨684942783321125686336211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456628522214083790890807 684942783321125686336211)
        ·
          refine ⟨1027414174981688529504317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684942783321125686336211 1027414174981688529504317)
          ·
            refine ⟨385280315618133198564119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1027414174981688529504317 385280315618133198564119)
            ·
              refine ⟨577920473427199797846179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385280315618133198564119 577920473427199797846179)
              ·
                refine ⟨866880710140799696769269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577920473427199797846179 866880710140799696769269)
                ·
                  refine ⟨81270066575699971572119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866880710140799696769269 81270066575699971572119)
                  ·
                    rfl

theorem cell21_356114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_356114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356114 prefixEnd_356114 := by exact prefixLift 356114
  have htrace : WordTrace (prefixWord ++ tailWord_356114) baseStart_356114 baseEnd_356114 := by
    simpa [prefixWord, tailWord_356114, baseEnd_356114] using wordTrace_append hprefix tailTrace_356114
  have hstable : (prefixWord ++ tailWord_356114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356114).length < 2 ^ (prefixWord ++ tailWord_356114).sum := by decide
  have hdescent : baseEnd_356114 < baseStart_356114 := by decide
  rcases family_descends (prefixWord ++ tailWord_356114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356277 : List Nat := [1, 3, 3, 2, 1, 4, 7]
def baseStart_356277 : Nat := 118140960795 + 356277 * 2 ^ 59
def prefixEnd_356277 : Nat := 4983230072969 + 3 ^ 40 * 356277 * 2
def baseEnd_356277 : Nat := 9034140599605323372791

theorem tailTrace_356277 : CollatzResearch.WordTrace tailWord_356277 prefixEnd_356277 9034140599605323372791 := by
  unfold tailWord_356277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12994489730276751112411085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8662993153517834074940723 12994489730276751112411085)
  ·
    refine ⟨4872933648853781667154157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12994489730276751112411085 4872933648853781667154157)
    ·
      refine ⟨1827350118320168125182809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4872933648853781667154157 1827350118320168125182809)
      ·
        refine ⟨1370512588740126093887107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1827350118320168125182809 1370512588740126093887107)
        ·
          refine ⟨2055768883110189140830661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370512588740126093887107 2055768883110189140830661)
          ·
            refine ⟨385456665583160463905749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2055768883110189140830661 385456665583160463905749)
            ·
              refine ⟨9034140599605323372791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 385456665583160463905749 9034140599605323372791)
              ·
                rfl

theorem cell21_356277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 7].length) (baseStart_356277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356277 prefixEnd_356277 := by exact prefixLift 356277
  have htrace : WordTrace (prefixWord ++ tailWord_356277) baseStart_356277 baseEnd_356277 := by
    simpa [prefixWord, tailWord_356277, baseEnd_356277] using wordTrace_append hprefix tailTrace_356277
  have hstable : (prefixWord ++ tailWord_356277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356277).length < 2 ^ (prefixWord ++ tailWord_356277).sum := by decide
  have hdescent : baseEnd_356277 < baseStart_356277 := by decide
  rcases family_descends (prefixWord ++ tailWord_356277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356305 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_356305 : Nat := 118140960795 + 356305 * 2 ^ 59
def prefixEnd_356305 : Nat := 4983230072969 + 3 ^ 40 * 356305 * 2
def baseEnd_356305 : Nat := 81313655377926083888395

theorem tailTrace_356305 : CollatzResearch.WordTrace tailWord_356305 prefixEnd_356305 81313655377926083888395 := by
  unfold tailWord_356305
  simp only [CollatzResearch.WordTrace]
  refine ⟨12995510974175311894430369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8663673982783541262953579 12995510974175311894430369)
  ·
    refine ⟨9746633230631483920822777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12995510974175311894430369 9746633230631483920822777)
    ·
      refine ⟨7309974922973612940617083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9746633230631483920822777 7309974922973612940617083)
      ·
        refine ⟨10964962384460419410925625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7309974922973612940617083 10964962384460419410925625)
        ·
          refine ⟨8223721788345314558194219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10964962384460419410925625 8223721788345314558194219)
          ·
            refine ⟨12335582682517971837291329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223721788345314558194219 12335582682517971837291329)
            ·
              refine ⟨9251687011888478877968497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12335582682517971837291329 9251687011888478877968497)
              ·
                refine ⟨6938765258916359158476373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9251687011888478877968497 6938765258916359158476373)
                ·
                  refine ⟨81313655377926083888395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6938765258916359158476373 81313655377926083888395)
                  ·
                    rfl

theorem cell21_356305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_356305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356305 prefixEnd_356305 := by exact prefixLift 356305
  have htrace : WordTrace (prefixWord ++ tailWord_356305) baseStart_356305 baseEnd_356305 := by
    simpa [prefixWord, tailWord_356305, baseEnd_356305] using wordTrace_append hprefix tailTrace_356305
  have hstable : (prefixWord ++ tailWord_356305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356305).length < 2 ^ (prefixWord ++ tailWord_356305).sum := by decide
  have hdescent : baseEnd_356305 < baseStart_356305 := by decide
  rcases family_descends (prefixWord ++ tailWord_356305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356342 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_356342 : Nat := 118140960795 + 356342 * 2 ^ 59
def prefixEnd_356342 : Nat := 4983230072969 + 3 ^ 40 * 356342 * 2
def baseEnd_356342 : Nat := 81322099282022241771653

theorem tailTrace_356342 : CollatzResearch.WordTrace tailWord_356342 prefixEnd_356342 81322099282022241771653 := by
  unfold tailWord_356342
  simp only [CollatzResearch.WordTrace]
  refine ⟨812303779690079200845455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8664573650027511475684853 812303779690079200845455)
  ·
    refine ⟨1218455669535118801268183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 812303779690079200845455 1218455669535118801268183)
    ·
      refine ⟨1827683504302678201902275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218455669535118801268183 1827683504302678201902275)
      ·
        refine ⟨2741525256454017302853413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827683504302678201902275 2741525256454017302853413)
        ·
          refine ⟨514035985585128244285015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2741525256454017302853413 514035985585128244285015)
          ·
            refine ⟨771053978377692366427523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514035985585128244285015 771053978377692366427523)
            ·
              refine ⟨1156580967566538549641285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771053978377692366427523 1156580967566538549641285)
              ·
                refine ⟨216858931418725978057741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1156580967566538549641285 216858931418725978057741)
                ·
                  refine ⟨81322099282022241771653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216858931418725978057741 81322099282022241771653)
                  ·
                    rfl

theorem cell21_356342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_356342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356342 prefixEnd_356342 := by exact prefixLift 356342
  have htrace : WordTrace (prefixWord ++ tailWord_356342) baseStart_356342 baseEnd_356342 := by
    simpa [prefixWord, tailWord_356342, baseEnd_356342] using wordTrace_append hprefix tailTrace_356342
  have hstable : (prefixWord ++ tailWord_356342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356342).length < 2 ^ (prefixWord ++ tailWord_356342).sum := by decide
  have hdescent : baseEnd_356342 < baseStart_356342 := by decide
  rcases family_descends (prefixWord ++ tailWord_356342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356412 : List Nat := [2, 2, 2, 2, 2, 1, 2, 8]
def baseStart_356412 : Nat := 118140960795 + 356412 * 2 ^ 59
def prefixEnd_356412 : Nat := 4983230072969 + 3 ^ 40 * 356412 * 2
def baseEnd_356412 : Nat := 27112691411905891868281

theorem tailTrace_356412 : CollatzResearch.WordTrace tailWord_356412 prefixEnd_356412 27112691411905891868281 := by
  unfold tailWord_356412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499706792393834584287745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8666275723191779445716993 6499706792393834584287745)
  ·
    refine ⟨4874780094295375938215809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6499706792393834584287745 4874780094295375938215809)
    ·
      refine ⟨3656085070721531953661857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4874780094295375938215809 3656085070721531953661857)
      ·
        refine ⟨2742063803041148965246393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3656085070721531953661857 2742063803041148965246393)
        ·
          refine ⟨2056547852280861723934795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2742063803041148965246393 2056547852280861723934795)
          ·
            refine ⟨3084821778421292585902193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056547852280861723934795 3084821778421292585902193)
            ·
              refine ⟨2313616333815969439426645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084821778421292585902193 2313616333815969439426645)
              ·
                refine ⟨27112691411905891868281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2313616333815969439426645 27112691411905891868281)
                ·
                  rfl

theorem cell21_356412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_356412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356412 prefixEnd_356412 := by exact prefixLift 356412
  have htrace : WordTrace (prefixWord ++ tailWord_356412) baseStart_356412 baseEnd_356412 := by
    simpa [prefixWord, tailWord_356412, baseEnd_356412] using wordTrace_append hprefix tailTrace_356412
  have hstable : (prefixWord ++ tailWord_356412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356412).length < 2 ^ (prefixWord ++ tailWord_356412).sum := by decide
  have hdescent : baseEnd_356412 < baseStart_356412 := by decide
  rcases family_descends (prefixWord ++ tailWord_356412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356429 : List Nat := [1, 6, 1, 1, 1, 1, 3, 7]
def baseStart_356429 : Nat := 118140960795 + 356429 * 2 ^ 59
def prefixEnd_356429 : Nat := 4983230072969 + 3 ^ 40 * 356429 * 2
def baseEnd_356429 : Nat := 27113984622443141273825

theorem tailTrace_356429 : CollatzResearch.WordTrace tailWord_356429 prefixEnd_356429 27113984622443141273825 := by
  unfold tailWord_356429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13000033625726081071944341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8666689083817387381296227 13000033625726081071944341)
  ·
    refine ⟨609376576205910050247391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13000033625726081071944341 609376576205910050247391)
    ·
      refine ⟨914064864308865075371087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 609376576205910050247391 914064864308865075371087)
      ·
        refine ⟨1371097296463297613056631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914064864308865075371087 1371097296463297613056631)
        ·
          refine ⟨2056645944694946419584947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371097296463297613056631 2056645944694946419584947)
          ·
            refine ⟨3084968917042419629377421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056645944694946419584947 3084968917042419629377421)
            ·
              refine ⟨1156863343890907361016533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3084968917042419629377421 1156863343890907361016533)
              ·
                refine ⟨27113984622443141273825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1156863343890907361016533 27113984622443141273825)
                ·
                  rfl

theorem cell21_356429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 7].length) (baseStart_356429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356429 prefixEnd_356429 := by exact prefixLift 356429
  have htrace : WordTrace (prefixWord ++ tailWord_356429) baseStart_356429 baseEnd_356429 := by
    simpa [prefixWord, tailWord_356429, baseEnd_356429] using wordTrace_append hprefix tailTrace_356429
  have hstable : (prefixWord ++ tailWord_356429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356429).length < 2 ^ (prefixWord ++ tailWord_356429).sum := by decide
  have hdescent : baseEnd_356429 < baseStart_356429 := by decide
  rcases family_descends (prefixWord ++ tailWord_356429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356457 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_356457 : Nat := 118140960795 + 356457 * 2 ^ 59
def prefixEnd_356457 : Nat := 4983230072969 + 3 ^ 40 * 356457 * 2
def baseEnd_356457 : Nat := 81348343848807597354751

theorem tailTrace_356457 : CollatzResearch.WordTrace tailWord_356457 prefixEnd_356457 81348343848807597354751 := by
  unfold tailWord_356457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13001054869624641853963625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8667369913083094569309083 13001054869624641853963625)
  ·
    refine ⟨9750791152218481390472719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13001054869624641853963625 9750791152218481390472719)
    ·
      refine ⟨14626186728327722085709079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9750791152218481390472719 14626186728327722085709079)
      ·
        refine ⟨21939280092491583128563619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14626186728327722085709079 21939280092491583128563619)
        ·
          refine ⟨32908920138737374692845429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21939280092491583128563619 32908920138737374692845429)
          ·
            refine ⟨3085211263006628877454259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32908920138737374692845429 3085211263006628877454259)
            ·
              refine ⟨4627816894509943316181389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085211263006628877454259 4627816894509943316181389)
              ·
                refine ⟨1735431335441228743568021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4627816894509943316181389 1735431335441228743568021)
                ·
                  refine ⟨81348343848807597354751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1735431335441228743568021 81348343848807597354751)
                  ·
                    rfl

theorem cell21_356457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_356457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356457 prefixEnd_356457 := by exact prefixLift 356457
  have htrace : WordTrace (prefixWord ++ tailWord_356457) baseStart_356457 baseEnd_356457 := by
    simpa [prefixWord, tailWord_356457, baseEnd_356457] using wordTrace_append hprefix tailTrace_356457
  have hstable : (prefixWord ++ tailWord_356457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356457).length < 2 ^ (prefixWord ++ tailWord_356457).sum := by decide
  have hdescent : baseEnd_356457 < baseStart_356457 := by decide
  rcases family_descends (prefixWord ++ tailWord_356457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356460 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_356460 : Nat := 118140960795 + 356460 * 2 ^ 59
def prefixEnd_356460 : Nat := 4983230072969 + 3 ^ 40 * 356460 * 2
def baseEnd_356460 : Nat := 81349028489680258804745

theorem tailTrace_356460 : CollatzResearch.WordTrace tailWord_356460 prefixEnd_356460 81349028489680258804745 := by
  unfold tailWord_356460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500582144306886683161417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8667442859075848910881889 6500582144306886683161417)
  ·
    refine ⟨4875436608230165012371063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6500582144306886683161417 4875436608230165012371063)
    ·
      refine ⟨7313154912345247518556595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4875436608230165012371063 7313154912345247518556595)
      ·
        refine ⟨10969732368517871277834893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313154912345247518556595 10969732368517871277834893)
        ·
          refine ⟨4113649638194201729188085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10969732368517871277834893 4113649638194201729188085)
          ·
            refine ⟨385654653580706412111383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4113649638194201729188085 385654653580706412111383)
            ·
              refine ⟨578481980371059618167075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385654653580706412111383 578481980371059618167075)
              ·
                refine ⟨867722970556589427250613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578481980371059618167075 867722970556589427250613)
                ·
                  refine ⟨81349028489680258804745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 867722970556589427250613 81349028489680258804745)
                  ·
                    rfl

theorem cell21_356460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_356460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356460 prefixEnd_356460 := by exact prefixLift 356460
  have htrace : WordTrace (prefixWord ++ tailWord_356460) baseStart_356460 baseEnd_356460 := by
    simpa [prefixWord, tailWord_356460, baseEnd_356460] using wordTrace_append hprefix tailTrace_356460
  have hstable : (prefixWord ++ tailWord_356460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356460).length < 2 ^ (prefixWord ++ tailWord_356460).sum := by decide
  have hdescent : baseEnd_356460 < baseStart_356460 := by decide
  rcases family_descends (prefixWord ++ tailWord_356460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356609 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 8]
def baseStart_356609 : Nat := 118140960795 + 356609 * 2 ^ 59
def prefixEnd_356609 : Nat := 4983230072969 + 3 ^ 40 * 356609 * 2
def baseEnd_356609 : Nat := 81383032319689110821107

theorem tailTrace_356609 : CollatzResearch.WordTrace tailWord_356609 prefixEnd_356609 81383032319689110821107 := by
  unfold tailWord_356609
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006598765073971813496881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8671065843382647875664587 13006598765073971813496881)
  ·
    refine ⟨9754949073805478860122661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13006598765073971813496881 9754949073805478860122661)
    ·
      refine ⟨1829052951338527286272999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9754949073805478860122661 1829052951338527286272999)
      ·
        refine ⟨2743579427007790929409499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829052951338527286272999 2743579427007790929409499)
        ·
          refine ⟨4115369140511686394114249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743579427007790929409499 4115369140511686394114249)
          ·
            refine ⟨3086526855383764795585687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115369140511686394114249 3086526855383764795585687)
            ·
              refine ⟨4629790283075647193378531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086526855383764795585687 4629790283075647193378531)
              ·
                refine ⟨6944685424613470790067797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629790283075647193378531 6944685424613470790067797)
                ·
                  refine ⟨81383032319689110821107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6944685424613470790067797 81383032319689110821107)
                  ·
                    rfl

theorem cell21_356609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_356609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356609 prefixEnd_356609 := by exact prefixLift 356609
  have htrace : WordTrace (prefixWord ++ tailWord_356609) baseStart_356609 baseEnd_356609 := by
    simpa [prefixWord, tailWord_356609, baseEnd_356609] using wordTrace_append hprefix tailTrace_356609
  have hstable : (prefixWord ++ tailWord_356609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356609).length < 2 ^ (prefixWord ++ tailWord_356609).sum := by decide
  have hdescent : baseEnd_356609 < baseStart_356609 := by decide
  rcases family_descends (prefixWord ++ tailWord_356609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356640 : List Nat := [2, 1, 1, 5, 2, 1, 1, 8]
def baseStart_356640 : Nat := 118140960795 + 356640 * 2 ^ 59
def prefixEnd_356640 : Nat := 4983230072969 + 3 ^ 40 * 356640 * 2
def baseEnd_356640 : Nat := 27130035647346648601459

theorem tailTrace_356640 : CollatzResearch.WordTrace tailWord_356640 prefixEnd_356640 27130035647346648601459 := by
  unfold tailWord_356640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6503864713980832053937687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8671819618641109405250249 6503864713980832053937687)
  ·
    refine ⟨9755797070971248080906531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6503864713980832053937687 9755797070971248080906531)
    ·
      refine ⟨14633695606456872121359797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9755797070971248080906531 14633695606456872121359797)
      ·
        refine ⟨1371908963105331761377481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14633695606456872121359797 1371908963105331761377481)
        ·
          refine ⟨1028931722328998821033111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1371908963105331761377481 1028931722328998821033111)
          ·
            refine ⟨1543397583493498231549667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028931722328998821033111 1543397583493498231549667)
            ·
              refine ⟨2315096375240247347324501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543397583493498231549667 2315096375240247347324501)
              ·
                refine ⟨27130035647346648601459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2315096375240247347324501 27130035647346648601459)
                ·
                  rfl

theorem cell21_356640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_356640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356640 prefixEnd_356640 := by exact prefixLift 356640
  have htrace : WordTrace (prefixWord ++ tailWord_356640) baseStart_356640 baseEnd_356640 := by
    simpa [prefixWord, tailWord_356640, baseEnd_356640] using wordTrace_append hprefix tailTrace_356640
  have hstable : (prefixWord ++ tailWord_356640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356640).length < 2 ^ (prefixWord ++ tailWord_356640).sum := by decide
  have hdescent : baseEnd_356640 < baseStart_356640 := by decide
  rcases family_descends (prefixWord ++ tailWord_356640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356688 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_356688 : Nat := 118140960795 + 356688 * 2 ^ 59
def prefixEnd_356688 : Nat := 4983230072969 + 3 ^ 40 * 356688 * 2
def baseEnd_356688 : Nat := 81401061196002529004279

theorem tailTrace_356688 : CollatzResearch.WordTrace tailWord_356688 prefixEnd_356688 81401061196002529004279 := by
  unfold tailWord_356688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504740065893884152811359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8672986754525178870415145 6504740065893884152811359)
  ·
    refine ⟨9757110098840826229217039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6504740065893884152811359 9757110098840826229217039)
    ·
      refine ⟨14635665148261239343825559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9757110098840826229217039 14635665148261239343825559)
      ·
        refine ⟨21953497722391859015738339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14635665148261239343825559 21953497722391859015738339)
        ·
          refine ⟨32930246583587788523607509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21953497722391859015738339 32930246583587788523607509)
          ·
            refine ⟨771802654302838793522051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32930246583587788523607509 771802654302838793522051)
            ·
              refine ⟨1157703981454258190283077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771802654302838793522051 1157703981454258190283077)
              ·
                refine ⟨217069496522673410678077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1157703981454258190283077 217069496522673410678077)
                ·
                  refine ⟨81401061196002529004279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217069496522673410678077 81401061196002529004279)
                  ·
                    rfl

theorem cell21_356688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_356688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356688 prefixEnd_356688 := by exact prefixLift 356688
  have htrace : WordTrace (prefixWord ++ tailWord_356688) baseStart_356688 baseEnd_356688 := by
    simpa [prefixWord, tailWord_356688, baseEnd_356688] using wordTrace_append hprefix tailTrace_356688
  have hstable : (prefixWord ++ tailWord_356688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356688).length < 2 ^ (prefixWord ++ tailWord_356688).sum := by decide
  have hdescent : baseEnd_356688 < baseStart_356688 := by decide
  rcases family_descends (prefixWord ++ tailWord_356688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356747 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 5]
def baseStart_356747 : Nat := 118140960795 + 356747 * 2 ^ 59
def prefixEnd_356747 : Nat := 4983230072969 + 3 ^ 40 * 356747 * 2
def baseEnd_356747 : Nat := 81414525799831537520825

theorem tailTrace_356747 : CollatzResearch.WordTrace tailWord_356747 prefixEnd_356747 81414525799831537520825 := by
  unfold tailWord_356747
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011632038574021382020495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8674421359049347588013663 13011632038574021382020495)
  ·
    refine ⟨19517448057861032073030743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011632038574021382020495 19517448057861032073030743)
    ·
      refine ⟨29276172086791548109546115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19517448057861032073030743 29276172086791548109546115)
      ·
        refine ⟨43914258130187322164319173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29276172086791548109546115 43914258130187322164319173)
        ·
          refine ⟨8233923399410122905809845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43914258130187322164319173 8233923399410122905809845)
          ·
            refine ⟨771930318694699022419673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8233923399410122905809845 771930318694699022419673)
            ·
              refine ⟨578947739021024266814755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771930318694699022419673 578947739021024266814755)
              ·
                refine ⟨868421608531536400222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578947739021024266814755 868421608531536400222133)
                ·
                  refine ⟨81414525799831537520825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 868421608531536400222133 81414525799831537520825)
                  ·
                    rfl

theorem cell21_356747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_356747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356747 prefixEnd_356747 := by exact prefixLift 356747
  have htrace : WordTrace (prefixWord ++ tailWord_356747) baseStart_356747 baseEnd_356747 := by
    simpa [prefixWord, tailWord_356747, baseEnd_356747] using wordTrace_append hprefix tailTrace_356747
  have hstable : (prefixWord ++ tailWord_356747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356747).length < 2 ^ (prefixWord ++ tailWord_356747).sum := by decide
  have hdescent : baseEnd_356747 < baseStart_356747 := by decide
  rcases family_descends (prefixWord ++ tailWord_356747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356812 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_356812 : Nat := 118140960795 + 356812 * 2 ^ 59
def prefixEnd_356812 : Nat := 4983230072969 + 3 ^ 40 * 356812 * 2
def baseEnd_356812 : Nat := 81429359685405868937359

theorem tailTrace_356812 : CollatzResearch.WordTrace tailWord_356812 prefixEnd_356812 81429359685405868937359 := by
  unfold tailWord_356812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507001391669268741568345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8676001855559024988757793 6507001391669268741568345)
  ·
    refine ⟨4880251043751951556176259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6507001391669268741568345 4880251043751951556176259)
    ·
      refine ⟨7320376565627927334264389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4880251043751951556176259 7320376565627927334264389)
      ·
        refine ⟨1372570606055236375174573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7320376565627927334264389 1372570606055236375174573)
        ·
          refine ⟨514713977270713640690465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1372570606055236375174573 514713977270713640690465)
          ·
            refine ⟨386035482953035230517849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514713977270713640690465 386035482953035230517849)
            ·
              refine ⟨289526612214776422888387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386035482953035230517849 289526612214776422888387)
              ·
                refine ⟨434289918322164634332581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289526612214776422888387 434289918322164634332581)
                ·
                  refine ⟨81429359685405868937359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 434289918322164634332581 81429359685405868937359)
                  ·
                    rfl

theorem cell21_356812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_356812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356812 prefixEnd_356812 := by exact prefixLift 356812
  have htrace : WordTrace (prefixWord ++ tailWord_356812) baseStart_356812 baseEnd_356812 := by
    simpa [prefixWord, tailWord_356812, baseEnd_356812] using wordTrace_append hprefix tailTrace_356812
  have hstable : (prefixWord ++ tailWord_356812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356812).length < 2 ^ (prefixWord ++ tailWord_356812).sum := by decide
  have hdescent : baseEnd_356812 < baseStart_356812 := by decide
  rcases family_descends (prefixWord ++ tailWord_356812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356927 : List Nat := [1, 1, 2, 2, 3, 2, 2, 8]
def baseStart_356927 : Nat := 118140960795 + 356927 * 2 ^ 59
def prefixEnd_356927 : Nat := 4983230072969 + 3 ^ 40 * 356927 * 2
def baseEnd_356927 : Nat := 27151868084063741506819

theorem tailTrace_356927 : CollatzResearch.WordTrace tailWord_356927 prefixEnd_356927 27151868084063741506819 := by
  unfold tailWord_356927
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018197177921912123573035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8678798118614608082382023 13018197177921912123573035)
  ·
    refine ⟨19527295766882868185359553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13018197177921912123573035 19527295766882868185359553)
    ·
      refine ⟨14645471825162151139019665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19527295766882868185359553 14645471825162151139019665)
      ·
        refine ⟨10984103868871613354264749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14645471825162151139019665 10984103868871613354264749)
        ·
          refine ⟨4119038950826855007849281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10984103868871613354264749 4119038950826855007849281)
          ·
            refine ⟨3089279213120141255886961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4119038950826855007849281 3089279213120141255886961)
            ·
              refine ⟨2316959409840105941915221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089279213120141255886961 2316959409840105941915221)
              ·
                refine ⟨27151868084063741506819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2316959409840105941915221 27151868084063741506819)
                ·
                  rfl

theorem cell21_356927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_356927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356927 prefixEnd_356927 := by exact prefixLift 356927
  have htrace : WordTrace (prefixWord ++ tailWord_356927) baseStart_356927 baseEnd_356927 := by
    simpa [prefixWord, tailWord_356927, baseEnd_356927] using wordTrace_append hprefix tailTrace_356927
  have hstable : (prefixWord ++ tailWord_356927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356927).length < 2 ^ (prefixWord ++ tailWord_356927).sum := by decide
  have hdescent : baseEnd_356927 < baseStart_356927 := by decide
  rcases family_descends (prefixWord ++ tailWord_356927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356975 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 3]
def baseStart_356975 : Nat := 118140960795 + 356975 * 2 ^ 59
def prefixEnd_356975 : Nat := 4983230072969 + 3 ^ 40 * 356975 * 2
def baseEnd_356975 : Nat := 81466558506153807720359

theorem tailTrace_356975 : CollatzResearch.WordTrace tailWord_356975 prefixEnd_356975 81466558506153807720359 := by
  unfold tailWord_356975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13019947881748016321320379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8679965254498677547546919 13019947881748016321320379)
  ·
    refine ⟨19529921822622024481980569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13019947881748016321320379 19529921822622024481980569)
    ·
      refine ⟨14647441366966518361485427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19529921822622024481980569 14647441366966518361485427)
      ·
        refine ⟨21971162050449777542228141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14647441366966518361485427 21971162050449777542228141)
        ·
          refine ⟨8239185768918666578335553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21971162050449777542228141 8239185768918666578335553)
          ·
            refine ⟨6179389326688999933751665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8239185768918666578335553 6179389326688999933751665)
            ·
              refine ⟨4634541995016749950313749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6179389326688999933751665 4634541995016749950313749)
              ·
                refine ⟨217244156016410153920957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4634541995016749950313749 217244156016410153920957)
                ·
                  refine ⟨81466558506153807720359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217244156016410153920957 81466558506153807720359)
                  ·
                    rfl

theorem cell21_356975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 3].length) (baseStart_356975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356975 prefixEnd_356975 := by exact prefixLift 356975
  have htrace : WordTrace (prefixWord ++ tailWord_356975) baseStart_356975 baseEnd_356975 := by
    simpa [prefixWord, tailWord_356975, baseEnd_356975] using wordTrace_append hprefix tailTrace_356975
  have hstable : (prefixWord ++ tailWord_356975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356975).length < 2 ^ (prefixWord ++ tailWord_356975).sum := by decide
  have hdescent : baseEnd_356975 < baseStart_356975 := by decide
  rcases family_descends (prefixWord ++ tailWord_356975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356981 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 4]
def baseStart_356981 : Nat := 118140960795 + 356981 * 2 ^ 59
def prefixEnd_356981 : Nat := 4983230072969 + 3 ^ 40 * 356981 * 2
def baseEnd_356981 : Nat := 81467927787899130620347

theorem tailTrace_356981 : CollatzResearch.WordTrace tailWord_356981 prefixEnd_356981 81467927787899130620347 := by
  unfold tailWord_356981
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020166719726279346038797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8680111146484186230692531 13020166719726279346038797)
  ·
    refine ⟨4882562519897354754764549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13020166719726279346038797 4882562519897354754764549)
    ·
      refine ⟨915480472480754016518353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4882562519897354754764549 915480472480754016518353)
      ·
        refine ⟨686610354360565512388765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 915480472480754016518353 686610354360565512388765)
        ·
          refine ⟨257478882885212067145787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 686610354360565512388765 257478882885212067145787)
          ·
            refine ⟨386218324327818100718681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257478882885212067145787 386218324327818100718681)
            ·
              refine ⟨289663743245863575539011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386218324327818100718681 289663743245863575539011)
              ·
                refine ⟨434495614868795363308517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289663743245863575539011 434495614868795363308517)
                ·
                  refine ⟨81467927787899130620347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 434495614868795363308517 81467927787899130620347)
                  ·
                    rfl

theorem cell21_356981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_356981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_356981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_356981 prefixEnd_356981 := by exact prefixLift 356981
  have htrace : WordTrace (prefixWord ++ tailWord_356981) baseStart_356981 baseEnd_356981 := by
    simpa [prefixWord, tailWord_356981, baseEnd_356981] using wordTrace_append hprefix tailTrace_356981
  have hstable : (prefixWord ++ tailWord_356981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356981).length < 2 ^ (prefixWord ++ tailWord_356981).sum := by decide
  have hdescent : baseEnd_356981 < baseStart_356981 := by decide
  rcases family_descends (prefixWord ++ tailWord_356981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357037 : List Nat := [1, 5, 2, 1, 1, 4, 1, 6]
def baseStart_357037 : Nat := 118140960795 + 357037 * 2 ^ 59
def prefixEnd_357037 : Nat := 4983230072969 + 3 ^ 40 * 357037 * 2
def baseEnd_357037 : Nat := 27160235916951825895633

theorem tailTrace_357037 : CollatzResearch.WordTrace tailWord_357037 prefixEnd_357037 27160235916951825895633 := by
  unfold tailWord_357037
  simp only [CollatzResearch.WordTrace]
  refine ⟨13022209207523400910077365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8681472805015600606718243 13022209207523400910077365)
  ·
    refine ⟨1220832113205318835319753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13022209207523400910077365 1220832113205318835319753)
    ·
      refine ⟨915624084903989126489815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1220832113205318835319753 915624084903989126489815)
      ·
        refine ⟨1373436127355983689734723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915624084903989126489815 1373436127355983689734723)
        ·
          refine ⟨2060154191033975534602085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373436127355983689734723 2060154191033975534602085)
          ·
            refine ⟨386278910818870412737891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2060154191033975534602085 386278910818870412737891)
            ·
              refine ⟨579418366228305619106837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386278910818870412737891 579418366228305619106837)
              ·
                refine ⟨27160235916951825895633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 579418366228305619106837 27160235916951825895633)
                ·
                  rfl

theorem cell21_357037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 6].length) (baseStart_357037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357037 prefixEnd_357037 := by exact prefixLift 357037
  have htrace : WordTrace (prefixWord ++ tailWord_357037) baseStart_357037 baseEnd_357037 := by
    simpa [prefixWord, tailWord_357037, baseEnd_357037] using wordTrace_append hprefix tailTrace_357037
  have hstable : (prefixWord ++ tailWord_357037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357037).length < 2 ^ (prefixWord ++ tailWord_357037).sum := by decide
  have hdescent : baseEnd_357037 < baseStart_357037 := by decide
  rcases family_descends (prefixWord ++ tailWord_357037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357048 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_357048 : Nat := 118140960795 + 357048 * 2 ^ 59
def prefixEnd_357048 : Nat := 4983230072969 + 3 ^ 40 * 357048 * 2
def baseEnd_357048 : Nat := 81483218100721903003543

theorem tailTrace_357048 : CollatzResearch.WordTrace tailWord_357048 prefixEnd_357048 81483218100721903003543 := by
  unfold tailWord_357048
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511305205241774894363899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8681740273655699859151865 6511305205241774894363899)
  ·
    refine ⟨9766957807862662341545849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6511305205241774894363899 9766957807862662341545849)
    ·
      refine ⟨7325218355896996756159387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9766957807862662341545849 7325218355896996756159387)
      ·
        refine ⟨10987827533845495134239081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325218355896996756159387 10987827533845495134239081)
        ·
          refine ⟨8240870650384121350679311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10987827533845495134239081 8240870650384121350679311)
          ·
            refine ⟨12361305975576182026018967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240870650384121350679311 12361305975576182026018967)
            ·
              refine ⟨18541958963364273039028451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12361305975576182026018967 18541958963364273039028451)
              ·
                refine ⟨27812938445046409558542677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18541958963364273039028451 27812938445046409558542677)
                ·
                  refine ⟨81483218100721903003543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27812938445046409558542677 81483218100721903003543)
                  ·
                    rfl

theorem cell21_357048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_357048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357048 prefixEnd_357048 := by exact prefixLift 357048
  have htrace : WordTrace (prefixWord ++ tailWord_357048) baseStart_357048 baseEnd_357048 := by
    simpa [prefixWord, tailWord_357048, baseEnd_357048] using wordTrace_append hprefix tailTrace_357048
  have hstable : (prefixWord ++ tailWord_357048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357048).length < 2 ^ (prefixWord ++ tailWord_357048).sum := by decide
  have hdescent : baseEnd_357048 < baseStart_357048 := by decide
  rcases family_descends (prefixWord ++ tailWord_357048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357068 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_357068 : Nat := 118140960795 + 357068 * 2 ^ 59
def prefixEnd_357068 : Nat := 4983230072969 + 3 ^ 40 * 357068 * 2
def baseEnd_357068 : Nat := 81487782373206312670169

theorem tailTrace_357068 : CollatzResearch.WordTrace tailWord_357068 prefixEnd_357068 81487782373206312670169 := by
  unfold tailWord_357068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511669935205546602227929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8682226580274062136303905 6511669935205546602227929)
  ·
    refine ⟨4883752451404159951670947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6511669935205546602227929 4883752451404159951670947)
    ·
      refine ⟨7325628677106239927506421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883752451404159951670947 7325628677106239927506421)
      ·
        refine ⟨686777688478709993203727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7325628677106239927506421 686777688478709993203727)
        ·
          refine ⟨1030166532718064989805591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686777688478709993203727 1030166532718064989805591)
          ·
            refine ⟨1545249799077097484708387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030166532718064989805591 1545249799077097484708387)
            ·
              refine ⟨2317874698615646227062581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545249799077097484708387 2317874698615646227062581)
              ·
                refine ⟨217300752995216833787117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2317874698615646227062581 217300752995216833787117)
                ·
                  refine ⟨81487782373206312670169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217300752995216833787117 81487782373206312670169)
                  ·
                    rfl

theorem cell21_357068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_357068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357068 prefixEnd_357068 := by exact prefixLift 357068
  have htrace : WordTrace (prefixWord ++ tailWord_357068) baseStart_357068 baseEnd_357068 := by
    simpa [prefixWord, tailWord_357068, baseEnd_357068] using wordTrace_append hprefix tailTrace_357068
  have hstable : (prefixWord ++ tailWord_357068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357068).length < 2 ^ (prefixWord ++ tailWord_357068).sum := by decide
  have hdescent : baseEnd_357068 < baseStart_357068 := by decide
  rcases family_descends (prefixWord ++ tailWord_357068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357079 : List Nat := [1, 1, 3, 2, 1, 5, 8]
def baseStart_357079 : Nat := 118140960795 + 357079 * 2 ^ 59
def prefixEnd_357079 : Nat := 4983230072969 + 3 ^ 40 * 357079 * 2
def baseEnd_357079 : Nat := 9054476969230304220757

theorem tailTrace_357079 : CollatzResearch.WordTrace tailWord_357079 prefixEnd_357079 9054476969230304220757 := by
  unfold tailWord_357079
  simp only [CollatzResearch.WordTrace]
  refine ⟨13023741073371242083106291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8682494048914161388737527 13023741073371242083106291)
  ·
    refine ⟨19535611610056863124659437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13023741073371242083106291 19535611610056863124659437)
    ·
      refine ⟨7325854353771323671747289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19535611610056863124659437 7325854353771323671747289)
      ·
        refine ⟨5494390765328492753810467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7325854353771323671747289 5494390765328492753810467)
        ·
          refine ⟨8241586147992739130715701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5494390765328492753810467 8241586147992739130715701)
          ·
            refine ⟨772648701374319293504597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8241586147992739130715701 772648701374319293504597)
            ·
              refine ⟨9054476969230304220757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 772648701374319293504597 9054476969230304220757)
              ·
                rfl

theorem cell21_357079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 8].length) (baseStart_357079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357079 prefixEnd_357079 := by exact prefixLift 357079
  have htrace : WordTrace (prefixWord ++ tailWord_357079) baseStart_357079 baseEnd_357079 := by
    simpa [prefixWord, tailWord_357079, baseEnd_357079] using wordTrace_append hprefix tailTrace_357079
  have hstable : (prefixWord ++ tailWord_357079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357079).length < 2 ^ (prefixWord ++ tailWord_357079).sum := by decide
  have hdescent : baseEnd_357079 < baseStart_357079 := by decide
  rcases family_descends (prefixWord ++ tailWord_357079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357141 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 4]
def baseStart_357141 : Nat := 118140960795 + 357141 * 2 ^ 59
def prefixEnd_357141 : Nat := 4983230072969 + 3 ^ 40 * 357141 * 2
def baseEnd_357141 : Nat := 81504441967774407953353

theorem tailTrace_357141 : CollatzResearch.WordTrace tailWord_357141 prefixEnd_357141 81504441967774407953353 := by
  unfold tailWord_357141
  simp only [CollatzResearch.WordTrace]
  refine ⟨13026002399146626671863277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8684001599431084447908851 13026002399146626671863277)
  ·
    refine ⟨4884750899679985001948729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13026002399146626671863277 4884750899679985001948729)
    ·
      refine ⟨3663563174759988751461547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4884750899679985001948729 3663563174759988751461547)
      ·
        refine ⟨5495344762139983127192321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663563174759988751461547 5495344762139983127192321)
        ·
          refine ⟨4121508571604987345394241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5495344762139983127192321 4121508571604987345394241)
          ·
            refine ⟨3091131428703740509045681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4121508571604987345394241 3091131428703740509045681)
            ·
              refine ⟨2318348571527805381784261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3091131428703740509045681 2318348571527805381784261)
              ·
                refine ⟨434690357161463509084549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2318348571527805381784261 434690357161463509084549)
                ·
                  refine ⟨81504441967774407953353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 434690357161463509084549 81504441967774407953353)
                  ·
                    rfl

theorem cell21_357141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_357141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357141 prefixEnd_357141 := by exact prefixLift 357141
  have htrace : WordTrace (prefixWord ++ tailWord_357141) baseStart_357141 baseEnd_357141 := by
    simpa [prefixWord, tailWord_357141, baseEnd_357141] using wordTrace_append hprefix tailTrace_357141
  have hstable : (prefixWord ++ tailWord_357141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357141).length < 2 ^ (prefixWord ++ tailWord_357141).sum := by decide
  have hdescent : baseEnd_357141 < baseStart_357141 := by decide
  rcases family_descends (prefixWord ++ tailWord_357141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357200 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_357200 : Nat := 118140960795 + 357200 * 2 ^ 59
def prefixEnd_357200 : Nat := 4983230072969 + 3 ^ 40 * 357200 * 2
def baseEnd_357200 : Nat := 81517906571603416469899

theorem tailTrace_357200 : CollatzResearch.WordTrace tailWord_357200 prefixEnd_357200 81517906571603416469899 := by
  unfold tailWord_357200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514077152966439874130527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8685436203955253165507369 6514077152966439874130527)
  ·
    refine ⟨9771115729449659811195791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6514077152966439874130527 9771115729449659811195791)
    ·
      refine ⟨14656673594174489716793687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9771115729449659811195791 14656673594174489716793687)
      ·
        refine ⟨21985010391261734575190531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14656673594174489716793687 21985010391261734575190531)
        ·
          refine ⟨32977515586892601862785797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21985010391261734575190531 32977515586892601862785797)
          ·
            refine ⟨6183284172542362849272337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32977515586892601862785797 6183284172542362849272337)
            ·
              refine ⟨4637463129406772136954253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183284172542362849272337 4637463129406772136954253)
              ·
                refine ⟨1739048673527539551357845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4637463129406772136954253 1739048673527539551357845)
                ·
                  refine ⟨81517906571603416469899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1739048673527539551357845 81517906571603416469899)
                  ·
                    rfl

theorem cell21_357200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_357200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357200 prefixEnd_357200 := by exact prefixLift 357200
  have htrace : WordTrace (prefixWord ++ tailWord_357200) baseStart_357200 baseEnd_357200 := by
    simpa [prefixWord, tailWord_357200, baseEnd_357200] using wordTrace_append hprefix tailTrace_357200
  have hstable : (prefixWord ++ tailWord_357200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357200).length < 2 ^ (prefixWord ++ tailWord_357200).sum := by decide
  have hdescent : baseEnd_357200 < baseStart_357200 := by decide
  rcases family_descends (prefixWord ++ tailWord_357200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357352 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_357352 : Nat := 118140960795 + 357352 * 2 ^ 59
def prefixEnd_357352 : Nat := 4983230072969 + 3 ^ 40 * 357352 * 2
def baseEnd_357352 : Nat := 81552595042484929936255

theorem tailTrace_357352 : CollatzResearch.WordTrace tailWord_357352 prefixEnd_357352 81552595042484929936255 := by
  unfold tailWord_357352
  simp only [CollatzResearch.WordTrace]
  refine ⟨6516849100691104853897155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8689132134254806471862873 6516849100691104853897155)
  ·
    refine ⟨9775273651036657280845733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6516849100691104853897155 9775273651036657280845733)
    ·
      refine ⟨1832863809569373240158575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9775273651036657280845733 1832863809569373240158575)
      ·
        refine ⟨2749295714354059860237863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1832863809569373240158575 2749295714354059860237863)
        ·
          refine ⟨4123943571531089790356795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749295714354059860237863 4123943571531089790356795)
          ·
            refine ⟨6185915357296634685535193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4123943571531089790356795 6185915357296634685535193)
            ·
              refine ⟨4639436517972476014151395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6185915357296634685535193 4639436517972476014151395)
              ·
                refine ⟨6959154776958714021227093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4639436517972476014151395 6959154776958714021227093)
                ·
                  refine ⟨81552595042484929936255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6959154776958714021227093 81552595042484929936255)
                  ·
                    rfl

theorem cell21_357352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_357352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357352 prefixEnd_357352 := by exact prefixLift 357352
  have htrace : WordTrace (prefixWord ++ tailWord_357352) baseStart_357352 baseEnd_357352 := by
    simpa [prefixWord, tailWord_357352, baseEnd_357352] using wordTrace_append hprefix tailTrace_357352
  have hstable : (prefixWord ++ tailWord_357352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357352).length < 2 ^ (prefixWord ++ tailWord_357352).sum := by decide
  have hdescent : baseEnd_357352 < baseStart_357352 := by decide
  rcases family_descends (prefixWord ++ tailWord_357352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357369 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 4]
def baseStart_357369 : Nat := 118140960795 + 357369 * 2 ^ 59
def prefixEnd_357369 : Nat := 4983230072969 + 3 ^ 40 * 357369 * 2
def baseEnd_357369 : Nat := 81556474674096678152887

theorem tailTrace_357369 : CollatzResearch.WordTrace tailWord_357369 prefixEnd_357369 81556474674096678152887 := by
  unfold tailWord_357369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13034318242320621611163161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8689545494880414407442107 13034318242320621611163161)
  ·
    refine ⟨9775738681740466208372371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13034318242320621611163161 9775738681740466208372371)
    ·
      refine ⟨14663608022610699312558557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9775738681740466208372371 14663608022610699312558557)
      ·
        refine ⟨5498853008479012242209459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14663608022610699312558557 5498853008479012242209459)
        ·
          refine ⟨8248279512718518363314189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5498853008479012242209459 8248279512718518363314189)
          ·
            refine ⟨3093104817269444386242821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8248279512718518363314189 3093104817269444386242821)
            ·
              refine ⟨579957153238020822420529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3093104817269444386242821 579957153238020822420529)
              ·
                refine ⟨434967864928515616815397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579957153238020822420529 434967864928515616815397)
                ·
                  refine ⟨81556474674096678152887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 434967864928515616815397 81556474674096678152887)
                  ·
                    rfl

theorem cell21_357369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_357369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357369 prefixEnd_357369 := by exact prefixLift 357369
  have htrace : WordTrace (prefixWord ++ tailWord_357369) baseStart_357369 baseEnd_357369 := by
    simpa [prefixWord, tailWord_357369, baseEnd_357369] using wordTrace_append hprefix tailTrace_357369
  have hstable : (prefixWord ++ tailWord_357369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357369).length < 2 ^ (prefixWord ++ tailWord_357369).sum := by decide
  have hdescent : baseEnd_357369 < baseStart_357369 := by decide
  rcases family_descends (prefixWord ++ tailWord_357369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357372 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_357372 : Nat := 118140960795 + 357372 * 2 ^ 59
def prefixEnd_357372 : Nat := 4983230072969 + 3 ^ 40 * 357372 * 2
def baseEnd_357372 : Nat := 81557159314969339602881

theorem tailTrace_357372 : CollatzResearch.WordTrace tailWord_357372 prefixEnd_357372 81557159314969339602881 := by
  unfold tailWord_357372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517213830654876561761185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8689618440873168749014913 6517213830654876561761185)
  ·
    refine ⟨4887910372991157421320889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6517213830654876561761185 4887910372991157421320889)
    ·
      refine ⟨3665932779743368065990667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4887910372991157421320889 3665932779743368065990667)
      ·
        refine ⟨5498899169615052098986001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665932779743368065990667 5498899169615052098986001)
        ·
          refine ⟨4124174377211289074239501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5498899169615052098986001 4124174377211289074239501)
          ·
            refine ⟨1546565391454233402839813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4124174377211289074239501 1546565391454233402839813)
            ·
              refine ⟨289981010897668763032465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1546565391454233402839813 289981010897668763032465)
              ·
                refine ⟨217485758173251572274349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289981010897668763032465 217485758173251572274349)
                ·
                  refine ⟨81557159314969339602881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217485758173251572274349 81557159314969339602881)
                  ·
                    rfl

theorem cell21_357372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_357372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357372 prefixEnd_357372 := by exact prefixLift 357372
  have htrace : WordTrace (prefixWord ++ tailWord_357372) baseStart_357372 baseEnd_357372 := by
    simpa [prefixWord, tailWord_357372, baseEnd_357372] using wordTrace_append hprefix tailTrace_357372
  have hstable : (prefixWord ++ tailWord_357372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357372).length < 2 ^ (prefixWord ++ tailWord_357372).sum := by decide
  have hdescent : baseEnd_357372 < baseStart_357372 := by decide
  rcases family_descends (prefixWord ++ tailWord_357372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357400 : List Nat := [2, 1, 2, 3, 2, 3, 3, 5]
def baseStart_357400 : Nat := 118140960795 + 357400 * 2 ^ 59
def prefixEnd_357400 : Nat := 4983230072969 + 3 ^ 40 * 357400 * 2
def baseEnd_357400 : Nat := 27187849765482504378719

theorem tailTrace_357400 : CollatzResearch.WordTrace tailWord_357400 prefixEnd_357400 27187849765482504378719 := by
  unfold tailWord_357400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517724452604156952770827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8690299270138875937027769 6517724452604156952770827)
  ·
    refine ⟨9776586678906235429156241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6517724452604156952770827 9776586678906235429156241)
    ·
      refine ⟨7332440009179676571867181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9776586678906235429156241 7332440009179676571867181)
      ·
        refine ⟨2749665003442378714450193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7332440009179676571867181 2749665003442378714450193)
        ·
          refine ⟨2062248752581784035837645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2749665003442378714450193 2062248752581784035837645)
          ·
            refine ⟨773343282218169013439117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2062248752581784035837645 773343282218169013439117)
            ·
              refine ⟨290003730831813380039669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 773343282218169013439117 290003730831813380039669)
              ·
                refine ⟨27187849765482504378719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290003730831813380039669 27187849765482504378719)
                ·
                  rfl

theorem cell21_357400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_357400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357400 prefixEnd_357400 := by exact prefixLift 357400
  have htrace : WordTrace (prefixWord ++ tailWord_357400) baseStart_357400 baseEnd_357400 := by
    simpa [prefixWord, tailWord_357400, baseEnd_357400] using wordTrace_append hprefix tailTrace_357400
  have hstable : (prefixWord ++ tailWord_357400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357400).length < 2 ^ (prefixWord ++ tailWord_357400).sum := by decide
  have hdescent : baseEnd_357400 < baseStart_357400 := by decide
  rcases family_descends (prefixWord ++ tailWord_357400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357473 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_357473 : Nat := 118140960795 + 357473 * 2 ^ 59
def prefixEnd_357473 : Nat := 4983230072969 + 3 ^ 40 * 357473 * 2
def baseEnd_357473 : Nat := 81580208891015608419341

theorem tailTrace_357473 : CollatzResearch.WordTrace tailWord_357473 prefixEnd_357473 81580208891015608419341 := by
  unfold tailWord_357473
  simp only [CollatzResearch.WordTrace]
  refine ⟨13038111433943847372949073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8692074289295898248632715 13038111433943847372949073)
  ·
    refine ⟨9778583575457885529711805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13038111433943847372949073 9778583575457885529711805)
    ·
      refine ⟨3666968840796707073641927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9778583575457885529711805 3666968840796707073641927)
      ·
        refine ⟨5500453261195060610462891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666968840796707073641927 5500453261195060610462891)
        ·
          refine ⟨8250679891792590915694337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5500453261195060610462891 8250679891792590915694337)
          ·
            refine ⟨6188009918844443186770753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8250679891792590915694337 6188009918844443186770753)
            ·
              refine ⟨4641007439133332390078065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6188009918844443186770753 4641007439133332390078065)
              ·
                refine ⟨3480755579349999292558549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4641007439133332390078065 3480755579349999292558549)
                ·
                  refine ⟨81580208891015608419341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3480755579349999292558549 81580208891015608419341)
                  ·
                    rfl

theorem cell21_357473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_357473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357473 prefixEnd_357473 := by exact prefixLift 357473
  have htrace : WordTrace (prefixWord ++ tailWord_357473) baseStart_357473 baseEnd_357473 := by
    simpa [prefixWord, tailWord_357473, baseEnd_357473] using wordTrace_append hprefix tailTrace_357473
  have hstable : (prefixWord ++ tailWord_357473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357473).length < 2 ^ (prefixWord ++ tailWord_357473).sum := by decide
  have hdescent : baseEnd_357473 < baseStart_357473 := by decide
  rcases family_descends (prefixWord ++ tailWord_357473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357493 : List Nat := [1, 3, 4, 3, 1, 1, 2, 6]
def baseStart_357493 : Nat := 118140960795 + 357493 * 2 ^ 59
def prefixEnd_357493 : Nat := 4983230072969 + 3 ^ 40 * 357493 * 2
def baseEnd_357493 : Nat := 27194924387833339361989

theorem tailTrace_357493 : CollatzResearch.WordTrace tailWord_357493 prefixEnd_357493 27194924387833339361989 := by
  unfold tailWord_357493
  simp only [CollatzResearch.WordTrace]
  refine ⟨13038840893871390788677133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8692560595914260525784755 13038840893871390788677133)
  ·
    refine ⟨4889565335201771545753925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13038840893871390788677133 4889565335201771545753925)
    ·
      refine ⟨916793500350332164828861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4889565335201771545753925 916793500350332164828861)
      ·
        refine ⟨343797562631374561810823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 916793500350332164828861 343797562631374561810823)
        ·
          refine ⟨515696343947061842716235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343797562631374561810823 515696343947061842716235)
          ·
            refine ⟨773544515920592764074353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515696343947061842716235 773544515920592764074353)
            ·
              refine ⟨580158386940444573055765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773544515920592764074353 580158386940444573055765)
              ·
                refine ⟨27194924387833339361989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 580158386940444573055765 27194924387833339361989)
                ·
                  rfl

theorem cell21_357493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 6].length) (baseStart_357493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357493 prefixEnd_357493 := by exact prefixLift 357493
  have htrace : WordTrace (prefixWord ++ tailWord_357493) baseStart_357493 baseEnd_357493 := by
    simpa [prefixWord, tailWord_357493, baseEnd_357493] using wordTrace_append hprefix tailTrace_357493
  have hstable : (prefixWord ++ tailWord_357493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357493).length < 2 ^ (prefixWord ++ tailWord_357493).sum := by decide
  have hdescent : baseEnd_357493 < baseStart_357493 := by decide
  rcases family_descends (prefixWord ++ tailWord_357493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357535 : List Nat := [1, 1, 2, 6, 2, 9]
def baseStart_357535 : Nat := 118140960795 + 357535 * 2 ^ 59
def prefixEnd_357535 : Nat := 4983230072969 + 3 ^ 40 * 357535 * 2
def baseEnd_357535 : Nat := 3022013264285825125403

theorem tailTrace_357535 : CollatzResearch.WordTrace tailWord_357535 prefixEnd_357535 3022013264285825125403 := by
  unfold tailWord_357535
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040372759719231961706059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8693581839812821307804039 13040372759719231961706059)
  ·
    refine ⟨19560559139578847942559089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13040372759719231961706059 19560559139578847942559089)
    ·
      refine ⟨14670419354684135956919317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19560559139578847942559089 14670419354684135956919317)
      ·
        refine ⟨687675907250818872980593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14670419354684135956919317 687675907250818872980593)
        ·
          refine ⟨515756930438114154735445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687675907250818872980593 515756930438114154735445)
          ·
            refine ⟨3022013264285825125403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 515756930438114154735445 3022013264285825125403)
            ·
              rfl

theorem cell21_357535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 9].length) (baseStart_357535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357535 prefixEnd_357535 := by exact prefixLift 357535
  have htrace : WordTrace (prefixWord ++ tailWord_357535) baseStart_357535 baseEnd_357535 := by
    simpa [prefixWord, tailWord_357535, baseEnd_357535] using wordTrace_append hprefix tailTrace_357535
  have hstable : (prefixWord ++ tailWord_357535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357535).length < 2 ^ (prefixWord ++ tailWord_357535).sum := by decide
  have hdescent : baseEnd_357535 < baseStart_357535 := by decide
  rcases family_descends (prefixWord ++ tailWord_357535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357566 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_357566 : Nat := 118140960795 + 357566 * 2 ^ 59
def prefixEnd_357566 : Nat := 4983230072969 + 3 ^ 40 * 357566 * 2
def baseEnd_357566 : Nat := 81601432758068113369151

theorem tailTrace_357566 : CollatzResearch.WordTrace tailWord_357566 prefixEnd_357566 81601432758068113369151 := by
  unfold tailWord_357566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630187927825865532010569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8694335615071282837389701 1630187927825865532010569)
  ·
    refine ⟨1222640945869399149007927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1630187927825865532010569 1222640945869399149007927)
    ·
      refine ⟨1833961418804098723511891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1222640945869399149007927 1833961418804098723511891)
      ·
        refine ⟨2750942128206148085267837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833961418804098723511891 2750942128206148085267837)
        ·
          refine ⟨1031603298077305531975439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2750942128206148085267837 1031603298077305531975439)
          ·
            refine ⟨1547404947115958297963159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031603298077305531975439 1547404947115958297963159)
            ·
              refine ⟨2321107420673937446944739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547404947115958297963159 2321107420673937446944739)
              ·
                refine ⟨3481661131010906170417109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321107420673937446944739 3481661131010906170417109)
                ·
                  refine ⟨81601432758068113369151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3481661131010906170417109 81601432758068113369151)
                  ·
                    rfl

theorem cell21_357566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_357566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357566 prefixEnd_357566 := by exact prefixLift 357566
  have htrace : WordTrace (prefixWord ++ tailWord_357566) baseStart_357566 baseEnd_357566 := by
    simpa [prefixWord, tailWord_357566, baseEnd_357566] using wordTrace_append hprefix tailTrace_357566
  have hstable : (prefixWord ++ tailWord_357566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357566).length < 2 ^ (prefixWord ++ tailWord_357566).sum := by decide
  have hdescent : baseEnd_357566 < baseStart_357566 := by decide
  rcases family_descends (prefixWord ++ tailWord_357566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357569 : List Nat := [1, 2, 6, 1, 1, 2, 3, 5]
def baseStart_357569 : Nat := 118140960795 + 357569 * 2 ^ 59
def prefixEnd_357569 : Nat := 4983230072969 + 3 ^ 40 * 357569 * 2
def baseEnd_357569 : Nat := 27200705799646924939715

theorem tailTrace_357569 : CollatzResearch.WordTrace tailWord_357569 prefixEnd_357569 27200705799646924939715 := by
  unfold tailWord_357569
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041612841596055768443761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8694408561064037178962507 13041612841596055768443761)
  ·
    refine ⟨9781209631197041826332821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13041612841596055768443761 9781209631197041826332821)
    ·
      refine ⟨458494201462361335609351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9781209631197041826332821 458494201462361335609351)
      ·
        refine ⟨687741302193542003414027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458494201462361335609351 687741302193542003414027)
        ·
          refine ⟨1031611953290313005121041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687741302193542003414027 1031611953290313005121041)
          ·
            refine ⟨773708964967734753840781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031611953290313005121041 773708964967734753840781)
            ·
              refine ⟨290140861862900532690293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 773708964967734753840781 290140861862900532690293)
              ·
                refine ⟨27200705799646924939715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290140861862900532690293 27200705799646924939715)
                ·
                  rfl

theorem cell21_357569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 5].length) (baseStart_357569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357569 prefixEnd_357569 := by exact prefixLift 357569
  have htrace : WordTrace (prefixWord ++ tailWord_357569) baseStart_357569 baseEnd_357569 := by
    simpa [prefixWord, tailWord_357569, baseEnd_357569] using wordTrace_append hprefix tailTrace_357569
  have hstable : (prefixWord ++ tailWord_357569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357569).length < 2 ^ (prefixWord ++ tailWord_357569).sum := by decide
  have hdescent : baseEnd_357569 < baseStart_357569 := by decide
  rcases family_descends (prefixWord ++ tailWord_357569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357620 : List Nat := [2, 6, 1, 2, 2, 1, 2, 5]
def baseStart_357620 : Nat := 118140960795 + 357620 * 2 ^ 59
def prefixEnd_357620 : Nat := 4983230072969 + 3 ^ 40 * 357620 * 2
def baseEnd_357620 : Nat := 27204585431258673156347

theorem tailTrace_357620 : CollatzResearch.WordTrace tailWord_357620 prefixEnd_357620 27204585431258673156347 := by
  unfold tailWord_357620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521736482205645739275157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8695648642940860985700209 6521736482205645739275157)
  ·
    refine ⟨305706397603389644028523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6521736482205645739275157 305706397603389644028523)
    ·
      refine ⟨458559596405084466042785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305706397603389644028523 458559596405084466042785)
      ·
        refine ⟨343919697303813349532089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458559596405084466042785 343919697303813349532089)
        ·
          refine ⟨257939772977860012149067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343919697303813349532089 257939772977860012149067)
          ·
            refine ⟨386909659466790018223601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257939772977860012149067 386909659466790018223601)
            ·
              refine ⟨290182244600092513667701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386909659466790018223601 290182244600092513667701)
              ·
                refine ⟨27204585431258673156347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 290182244600092513667701 27204585431258673156347)
                ·
                  rfl

theorem cell21_357620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_357620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357620 prefixEnd_357620 := by exact prefixLift 357620
  have htrace : WordTrace (prefixWord ++ tailWord_357620) baseStart_357620 baseEnd_357620 := by
    simpa [prefixWord, tailWord_357620, baseEnd_357620] using wordTrace_append hprefix tailTrace_357620
  have hstable : (prefixWord ++ tailWord_357620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357620).length < 2 ^ (prefixWord ++ tailWord_357620).sum := by decide
  have hdescent : baseEnd_357620 < baseStart_357620 := by decide
  rcases family_descends (prefixWord ++ tailWord_357620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357625 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_357625 : Nat := 118140960795 + 357625 * 2 ^ 59
def prefixEnd_357625 : Nat := 4983230072969 + 3 ^ 40 * 357625 * 2
def baseEnd_357625 : Nat := 81614897361897121885697

theorem tailTrace_357625 : CollatzResearch.WordTrace tailWord_357625 prefixEnd_357625 81614897361897121885697 := by
  unfold tailWord_357625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043655329393177332482329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8695770219595451554988219 13043655329393177332482329)
  ·
    refine ⟨9782741497044882999361747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13043655329393177332482329 9782741497044882999361747)
    ·
      refine ⟨14674112245567324499042621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9782741497044882999361747 14674112245567324499042621)
      ·
        refine ⟨5502792092087746687140983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14674112245567324499042621 5502792092087746687140983)
        ·
          refine ⟨8254188138131620030711475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5502792092087746687140983 8254188138131620030711475)
          ·
            refine ⟨12381282207197430046067213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254188138131620030711475 12381282207197430046067213)
            ·
              refine ⟨4642980827699036267275205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12381282207197430046067213 4642980827699036267275205)
              ·
                refine ⟨870558905193569300114101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4642980827699036267275205 870558905193569300114101)
                ·
                  refine ⟨81614897361897121885697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870558905193569300114101 81614897361897121885697)
                  ·
                    rfl

theorem cell21_357625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_357625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357625 prefixEnd_357625 := by exact prefixLift 357625
  have htrace : WordTrace (prefixWord ++ tailWord_357625) baseStart_357625 baseEnd_357625 := by
    simpa [prefixWord, tailWord_357625, baseEnd_357625] using wordTrace_append hprefix tailTrace_357625
  have hstable : (prefixWord ++ tailWord_357625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357625).length < 2 ^ (prefixWord ++ tailWord_357625).sum := by decide
  have hdescent : baseEnd_357625 < baseStart_357625 := by decide
  rcases family_descends (prefixWord ++ tailWord_357625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357634 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_357634 : Nat := 118140960795 + 357634 * 2 ^ 59
def prefixEnd_357634 : Nat := 4983230072969 + 3 ^ 40 * 357634 * 2
def baseEnd_357634 : Nat := 81616951284515106235679

theorem tailTrace_357634 : CollatzResearch.WordTrace tailWord_357634 prefixEnd_357634 81616951284515106235679 := by
  unfold tailWord_357634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260995896590142967389989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8695989057573714579706637 3260995896590142967389989)
  ·
    refine ⟨611436730610651806385623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3260995896590142967389989 611436730610651806385623)
    ·
      refine ⟨917155095915977709578435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611436730610651806385623 917155095915977709578435)
      ·
        refine ⟨1375732643873966564367653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917155095915977709578435 1375732643873966564367653)
        ·
          refine ⟨257949870726368730818935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1375732643873966564367653 257949870726368730818935)
          ·
            refine ⟨386924806089553096228403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257949870726368730818935 386924806089553096228403)
            ·
              refine ⟨580387209134329644342605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386924806089553096228403 580387209134329644342605)
              ·
                refine ⟨217645203425373616628477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580387209134329644342605 217645203425373616628477)
                ·
                  refine ⟨81616951284515106235679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217645203425373616628477 81616951284515106235679)
                  ·
                    rfl

theorem cell21_357634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_357634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357634 prefixEnd_357634 := by exact prefixLift 357634
  have htrace : WordTrace (prefixWord ++ tailWord_357634) baseStart_357634 baseEnd_357634 := by
    simpa [prefixWord, tailWord_357634, baseEnd_357634] using wordTrace_append hprefix tailTrace_357634
  have hstable : (prefixWord ++ tailWord_357634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357634).length < 2 ^ (prefixWord ++ tailWord_357634).sum := by decide
  have hdescent : baseEnd_357634 < baseStart_357634 := by decide
  rcases family_descends (prefixWord ++ tailWord_357634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357656 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_357656 : Nat := 118140960795 + 357656 * 2 ^ 59
def prefixEnd_357656 : Nat := 4983230072969 + 3 ^ 40 * 357656 * 2
def baseEnd_357656 : Nat := 81621971984247956868967

theorem tailTrace_357656 : CollatzResearch.WordTrace tailWord_357656 prefixEnd_357656 81621971984247956868967 := by
  unfold tailWord_357656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6522392996140434813430411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8696523994853913084573881 6522392996140434813430411)
  ·
    refine ⟨9783589494210652220145617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6522392996140434813430411 9783589494210652220145617)
    ·
      refine ⟨7337692120657989165109213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9783589494210652220145617 7337692120657989165109213)
      ·
        refine ⟨2751634545246745936915955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7337692120657989165109213 2751634545246745936915955)
        ·
          refine ⟨4127451817870118905373933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751634545246745936915955 4127451817870118905373933)
          ·
            refine ⟨1547794431701294589515225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4127451817870118905373933 1547794431701294589515225)
            ·
              refine ⟨1160845823775970942136419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1547794431701294589515225 1160845823775970942136419)
              ·
                refine ⟨1741268735663956413204629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160845823775970942136419 1741268735663956413204629)
                ·
                  refine ⟨81621971984247956868967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1741268735663956413204629 81621971984247956868967)
                  ·
                    rfl

theorem cell21_357656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_357656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357656 prefixEnd_357656 := by exact prefixLift 357656
  have htrace : WordTrace (prefixWord ++ tailWord_357656) baseStart_357656 baseEnd_357656 := by
    simpa [prefixWord, tailWord_357656, baseEnd_357656] using wordTrace_append hprefix tailTrace_357656
  have hstable : (prefixWord ++ tailWord_357656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357656).length < 2 ^ (prefixWord ++ tailWord_357656).sum := by decide
  have hdescent : baseEnd_357656 < baseStart_357656 := by decide
  rcases family_descends (prefixWord ++ tailWord_357656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357794 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_357794 : Nat := 118140960795 + 357794 * 2 ^ 59
def prefixEnd_357794 : Nat := 4983230072969 + 3 ^ 40 * 357794 * 2
def baseEnd_357794 : Nat := 81653465464390383568685

theorem tailTrace_357794 : CollatzResearch.WordTrace tailWord_357794 prefixEnd_357794 81653465464390383568685 := by
  unfold tailWord_357794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3262454816445229798846109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8699879510520612796922957 3262454816445229798846109)
  ·
    refine ⟨1223420556166961174567291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3262454816445229798846109 1223420556166961174567291)
    ·
      refine ⟨1835130834250441761850937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223420556166961174567291 1835130834250441761850937)
      ·
        refine ⟨1376348125687831321388203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1835130834250441761850937 1376348125687831321388203)
        ·
          refine ⟨2064522188531746982082305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376348125687831321388203 2064522188531746982082305)
          ·
            refine ⟨1548391641398810236561729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2064522188531746982082305 1548391641398810236561729)
            ·
              refine ⟨1161293731049107677421297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548391641398810236561729 1161293731049107677421297)
              ·
                refine ⟨870970298286830758065973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1161293731049107677421297 870970298286830758065973)
                ·
                  refine ⟨81653465464390383568685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870970298286830758065973 81653465464390383568685)
                  ·
                    rfl

theorem cell21_357794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_357794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357794 prefixEnd_357794 := by exact prefixLift 357794
  have htrace : WordTrace (prefixWord ++ tailWord_357794) baseStart_357794 baseEnd_357794 := by
    simpa [prefixWord, tailWord_357794, baseEnd_357794] using wordTrace_append hprefix tailTrace_357794
  have hstable : (prefixWord ++ tailWord_357794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357794).length < 2 ^ (prefixWord ++ tailWord_357794).sum := by decide
  have hdescent : baseEnd_357794 < baseStart_357794 := by decide
  rcases family_descends (prefixWord ++ tailWord_357794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357867 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_357867 : Nat := 118140960795 + 357867 * 2 ^ 59
def prefixEnd_357867 : Nat := 4983230072969 + 3 ^ 40 * 357867 * 2
def baseEnd_357867 : Nat := 81670125058958478851869

theorem tailTrace_357867 : CollatzResearch.WordTrace tailWord_357867 prefixEnd_357867 81670125058958478851869 := by
  unfold tailWord_357867
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052481794516452662791855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8701654529677635108527903 13052481794516452662791855)
  ·
    refine ⟨19578722691774678994187783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13052481794516452662791855 19578722691774678994187783)
    ·
      refine ⟨29368084037662018491281675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19578722691774678994187783 29368084037662018491281675)
      ·
        refine ⟨44052126056493027736922513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29368084037662018491281675 44052126056493027736922513)
        ·
          refine ⟨33039094542369770802691885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44052126056493027736922513 33039094542369770802691885)
          ·
            refine ⟨12389660453388664051009457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33039094542369770802691885 12389660453388664051009457)
            ·
              refine ⟨9292245340041498038257093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12389660453388664051009457 9292245340041498038257093)
              ·
                refine ⟨1742296001257780882173205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9292245340041498038257093 1742296001257780882173205)
                ·
                  refine ⟨81670125058958478851869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1742296001257780882173205 81670125058958478851869)
                  ·
                    rfl

theorem cell21_357867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_357867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357867 prefixEnd_357867 := by exact prefixLift 357867
  have htrace : WordTrace (prefixWord ++ tailWord_357867) baseStart_357867 baseEnd_357867 := by
    simpa [prefixWord, tailWord_357867, baseEnd_357867] using wordTrace_append hprefix tailTrace_357867
  have hstable : (prefixWord ++ tailWord_357867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357867).length < 2 ^ (prefixWord ++ tailWord_357867).sum := by decide
  have hdescent : baseEnd_357867 < baseStart_357867 := by decide
  rcases family_descends (prefixWord ++ tailWord_357867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357884 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_357884 : Nat := 118140960795 + 357884 * 2 ^ 59
def prefixEnd_357884 : Nat := 4983230072969 + 3 ^ 40 * 357884 * 2
def baseEnd_357884 : Nat := 81674004690570227068501

theorem tailTrace_357884 : CollatzResearch.WordTrace tailWord_357884 prefixEnd_357884 81674004690570227068501 := by
  unfold tailWord_357884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6526550917727432283080353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8702067890303243044107137 6526550917727432283080353)
  ·
    refine ⟨4894913188295574212310265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6526550917727432283080353 4894913188295574212310265)
    ·
      refine ⟨3671184891221680659232699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4894913188295574212310265 3671184891221680659232699)
      ·
        refine ⟨5506777336832520988849049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3671184891221680659232699 5506777336832520988849049)
        ·
          refine ⟨4130083002624390741636787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5506777336832520988849049 4130083002624390741636787)
          ·
            refine ⟨6195124503936586112455181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130083002624390741636787 6195124503936586112455181)
            ·
              refine ⟨2323171688976219792170693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6195124503936586112455181 2323171688976219792170693)
              ·
                refine ⟨435594691683041211032005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2323171688976219792170693 435594691683041211032005)
                ·
                  refine ⟨81674004690570227068501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435594691683041211032005 81674004690570227068501)
                  ·
                    rfl

theorem cell21_357884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_357884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357884 prefixEnd_357884 := by exact prefixLift 357884
  have htrace : WordTrace (prefixWord ++ tailWord_357884) baseStart_357884 baseEnd_357884 := by
    simpa [prefixWord, tailWord_357884, baseEnd_357884] using wordTrace_append hprefix tailTrace_357884
  have hstable : (prefixWord ++ tailWord_357884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357884).length < 2 ^ (prefixWord ++ tailWord_357884).sum := by decide
  have hdescent : baseEnd_357884 < baseStart_357884 := by decide
  rcases family_descends (prefixWord ++ tailWord_357884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357946 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_357946 : Nat := 118140960795 + 357946 * 2 ^ 59
def prefixEnd_357946 : Nat := 4983230072969 + 3 ^ 40 * 357946 * 2
def baseEnd_357946 : Nat := 81688153935271897035041

theorem tailTrace_357946 : CollatzResearch.WordTrace tailWord_357946 prefixEnd_357946 81688153935271897035041 := by
  unfold tailWord_357946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263840790307562288729423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8703575440820166103278461 3263840790307562288729423)
  ·
    refine ⟨4895761185461343433094135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3263840790307562288729423 4895761185461343433094135)
    ·
      refine ⟨7343641778192015149641203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4895761185461343433094135 7343641778192015149641203)
      ·
        refine ⟨11015462667288022724461805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7343641778192015149641203 11015462667288022724461805)
        ·
          refine ⟨4130798500233008521673177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11015462667288022724461805 4130798500233008521673177)
          ·
            refine ⟨3098098875174756391254883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4130798500233008521673177 3098098875174756391254883)
            ·
              refine ⟨4647148312762134586882325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3098098875174756391254883 4647148312762134586882325)
              ·
                refine ⟨217835077160725058760109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4647148312762134586882325 217835077160725058760109)
                ·
                  refine ⟨81688153935271897035041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217835077160725058760109 81688153935271897035041)
                  ·
                    rfl

theorem cell21_357946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_357946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357946 prefixEnd_357946 := by exact prefixLift 357946
  have htrace : WordTrace (prefixWord ++ tailWord_357946) baseStart_357946 baseEnd_357946 := by
    simpa [prefixWord, tailWord_357946, baseEnd_357946] using wordTrace_append hprefix tailTrace_357946
  have hstable : (prefixWord ++ tailWord_357946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357946).length < 2 ^ (prefixWord ++ tailWord_357946).sum := by decide
  have hdescent : baseEnd_357946 < baseStart_357946 := by decide
  rcases family_descends (prefixWord ++ tailWord_357946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357980 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_357980 : Nat := 118140960795 + 357980 * 2 ^ 59
def prefixEnd_357980 : Nat := 4983230072969 + 3 ^ 40 * 357980 * 2
def baseEnd_357980 : Nat := 81695913198495393468305

theorem tailTrace_357980 : CollatzResearch.WordTrace tailWord_357980 prefixEnd_357980 81695913198495393468305 := by
  unfold tailWord_357980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528301621553536480827697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8704402162071381974436929 6528301621553536480827697)
  ·
    refine ⟨4896226216165152360620773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6528301621553536480827697 4896226216165152360620773)
    ·
      refine ⟨918042415530966067616395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4896226216165152360620773 918042415530966067616395)
      ·
        refine ⟨1377063623296449101424593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918042415530966067616395 1377063623296449101424593)
        ·
          refine ⟨1032797717472336826068445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377063623296449101424593 1032797717472336826068445)
          ·
            refine ⟨387299144052126309775667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032797717472336826068445 387299144052126309775667)
            ·
              refine ⟨580948716078189464663501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387299144052126309775667 580948716078189464663501)
              ·
                refine ⟨217855768529321049248813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580948716078189464663501 217855768529321049248813)
                ·
                  refine ⟨81695913198495393468305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217855768529321049248813 81695913198495393468305)
                  ·
                    rfl

theorem cell21_357980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_357980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_357980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_357980 prefixEnd_357980 := by exact prefixLift 357980
  have htrace : WordTrace (prefixWord ++ tailWord_357980) baseStart_357980 baseEnd_357980 := by
    simpa [prefixWord, tailWord_357980, baseEnd_357980] using wordTrace_append hprefix tailTrace_357980
  have hstable : (prefixWord ++ tailWord_357980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357980).length < 2 ^ (prefixWord ++ tailWord_357980).sum := by decide
  have hdescent : baseEnd_357980 < baseStart_357980 := by decide
  rcases family_descends (prefixWord ++ tailWord_357980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358070 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_358070 : Nat := 118140960795 + 358070 * 2 ^ 59
def prefixEnd_358070 : Nat := 4983230072969 + 3 ^ 40 * 358070 * 2
def baseEnd_358070 : Nat := 81716452424675236968121

theorem tailTrace_358070 : CollatzResearch.WordTrace tailWord_358070 prefixEnd_358070 81716452424675236968121 := by
  unfold tailWord_358070
  simp only [CollatzResearch.WordTrace]
  refine ⟨816242863298813645776979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8706590541854012221621109 816242863298813645776979)
  ·
    refine ⟨1224364294948220468665469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 816242863298813645776979 1224364294948220468665469)
    ·
      refine ⟨459136610605582675749551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1224364294948220468665469 459136610605582675749551)
      ·
        refine ⟨688704915908374013624327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459136610605582675749551 688704915908374013624327)
        ·
          refine ⟨1033057373862561020436491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688704915908374013624327 1033057373862561020436491)
          ·
            refine ⟨1549586060793841530654737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033057373862561020436491 1549586060793841530654737)
            ·
              refine ⟨1162189545595381147991053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549586060793841530654737 1162189545595381147991053)
              ·
                refine ⟨435821079598267930496645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1162189545595381147991053 435821079598267930496645)
                ·
                  refine ⟨81716452424675236968121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435821079598267930496645 81716452424675236968121)
                  ·
                    rfl

theorem cell21_358070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_358070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358070 prefixEnd_358070 := by exact prefixLift 358070
  have htrace : WordTrace (prefixWord ++ tailWord_358070) baseStart_358070 baseEnd_358070 := by
    simpa [prefixWord, tailWord_358070, baseEnd_358070] using wordTrace_append hprefix tailTrace_358070
  have hstable : (prefixWord ++ tailWord_358070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358070).length < 2 ^ (prefixWord ++ tailWord_358070).sum := by decide
  have hdescent : baseEnd_358070 < baseStart_358070 := by decide
  rcases family_descends (prefixWord ++ tailWord_358070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358112 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_358112 : Nat := 118140960795 + 358112 * 2 ^ 59
def prefixEnd_358112 : Nat := 4983230072969 + 3 ^ 40 * 358112 * 2
def baseEnd_358112 : Nat := 81726037396892497268035

theorem tailTrace_358112 : CollatzResearch.WordTrace tailWord_358112 prefixEnd_358112 81726037396892497268035 := by
  unfold tailWord_358112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6530708839314429752730295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8707611785752573003640393 6530708839314429752730295)
  ·
    refine ⟨9796063258971644629095443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6530708839314429752730295 9796063258971644629095443)
    ·
      refine ⟨14694094888457466943643165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9796063258971644629095443 14694094888457466943643165)
      ·
        refine ⟨5510285583171550103866187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14694094888457466943643165 5510285583171550103866187)
        ·
          refine ⟨8265428374757325155799281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5510285583171550103866187 8265428374757325155799281)
          ·
            refine ⟨6199071281067993866849461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8265428374757325155799281 6199071281067993866849461)
            ·
              refine ⟨581162932600124425017137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6199071281067993866849461 581162932600124425017137)
              ·
                refine ⟨435872199450093318762853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581162932600124425017137 435872199450093318762853)
                ·
                  refine ⟨81726037396892497268035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435872199450093318762853 81726037396892497268035)
                  ·
                    rfl

theorem cell21_358112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_358112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358112 prefixEnd_358112 := by exact prefixLift 358112
  have htrace : WordTrace (prefixWord ++ tailWord_358112) baseStart_358112 baseEnd_358112 := by
    simpa [prefixWord, tailWord_358112, baseEnd_358112] using wordTrace_append hprefix tailTrace_358112
  have hstable : (prefixWord ++ tailWord_358112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358112).length < 2 ^ (prefixWord ++ tailWord_358112).sum := by decide
  have hdescent : baseEnd_358112 < baseStart_358112 := by decide
  rcases family_descends (prefixWord ++ tailWord_358112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358126 : List Nat := [4, 1, 2, 1, 1, 2, 2, 8]
def baseStart_358126 : Nat := 118140960795 + 358126 * 2 ^ 59
def prefixEnd_358126 : Nat := 4983230072969 + 3 ^ 40 * 358126 * 2
def baseEnd_358126 : Nat := 27243077462543861344891

theorem tailTrace_358126 : CollatzResearch.WordTrace tailWord_358126 prefixEnd_358126 27243077462543861344891 := by
  unfold tailWord_358126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632741037572267487058779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8707952200385426597646821 1632741037572267487058779)
  ·
    refine ⟨2449111556358401230588169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632741037572267487058779 2449111556358401230588169)
    ·
      refine ⟨1836833667268800922941127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2449111556358401230588169 1836833667268800922941127)
      ·
        refine ⟨2755250500903201384411691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1836833667268800922941127 2755250500903201384411691)
        ·
          refine ⟨4132875751354802076617537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2755250500903201384411691 4132875751354802076617537)
          ·
            refine ⟨3099656813516101557463153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4132875751354802076617537 3099656813516101557463153)
            ·
              refine ⟨2324742610137076168097365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3099656813516101557463153 2324742610137076168097365)
              ·
                refine ⟨27243077462543861344891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2324742610137076168097365 27243077462543861344891)
                ·
                  rfl

theorem cell21_358126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_358126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358126 prefixEnd_358126 := by exact prefixLift 358126
  have htrace : WordTrace (prefixWord ++ tailWord_358126) baseStart_358126 baseEnd_358126 := by
    simpa [prefixWord, tailWord_358126, baseEnd_358126] using wordTrace_append hprefix tailTrace_358126
  have hstable : (prefixWord ++ tailWord_358126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358126).length < 2 ^ (prefixWord ++ tailWord_358126).sum := by decide
  have hdescent : baseEnd_358126 < baseStart_358126 := by decide
  rcases family_descends (prefixWord ++ tailWord_358126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358129 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 4]
def baseStart_358129 : Nat := 118140960795 + 358129 * 2 ^ 59
def prefixEnd_358129 : Nat := 4983230072969 + 3 ^ 40 * 358129 * 2
def baseEnd_358129 : Nat := 81729917028504245484667

theorem tailTrace_358129 : CollatzResearch.WordTrace tailWord_358129 prefixEnd_358129 81729917028504245484667 := by
  unfold tailWord_358129
  simp only [CollatzResearch.WordTrace]
  refine ⟨13062037719567271408829441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8708025146378180939219627 13062037719567271408829441)
  ·
    refine ⟨9796528289675453556622081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13062037719567271408829441 9796528289675453556622081)
    ·
      refine ⟨7347396217256590167466561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9796528289675453556622081 7347396217256590167466561)
      ·
        refine ⟨5510547162942442625599921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7347396217256590167466561 5510547162942442625599921)
        ·
          refine ⟨4132910372206831969199941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5510547162942442625599921 4132910372206831969199941)
          ·
            refine ⟨774920694788780994224989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4132910372206831969199941 774920694788780994224989)
            ·
              refine ⟨290595260545792872834371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 774920694788780994224989 290595260545792872834371)
              ·
                refine ⟨435892890818689309251557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290595260545792872834371 435892890818689309251557)
                ·
                  refine ⟨81729917028504245484667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435892890818689309251557 81729917028504245484667)
                  ·
                    rfl

theorem cell21_358129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_358129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358129 prefixEnd_358129 := by exact prefixLift 358129
  have htrace : WordTrace (prefixWord ++ tailWord_358129) baseStart_358129 baseEnd_358129 := by
    simpa [prefixWord, tailWord_358129, baseEnd_358129] using wordTrace_append hprefix tailTrace_358129
  have hstable : (prefixWord ++ tailWord_358129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358129).length < 2 ^ (prefixWord ++ tailWord_358129).sum := by decide
  have hdescent : baseEnd_358129 < baseStart_358129 := by decide
  rcases family_descends (prefixWord ++ tailWord_358129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358188 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_358188 : Nat := 118140960795 + 358188 * 2 ^ 59
def prefixEnd_358188 : Nat := 4983230072969 + 3 ^ 40 * 358188 * 2
def baseEnd_358188 : Nat := 81743381632333254001213

theorem tailTrace_358188 : CollatzResearch.WordTrace tailWord_358188 prefixEnd_358188 81743381632333254001213 := by
  unfold tailWord_358188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532094813176762242613609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8709459750902349656818145 6532094813176762242613609)
  ·
    refine ⟨4899071109882571681960207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6532094813176762242613609 4899071109882571681960207)
    ·
      refine ⟨7348606664823857522940311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899071109882571681960207 7348606664823857522940311)
      ·
        refine ⟨11022909997235786284410467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348606664823857522940311 11022909997235786284410467)
        ·
          refine ⟨16534364995853679426615701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11022909997235786284410467 16534364995853679426615701)
          ·
            refine ⟨775048359180641223122611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16534364995853679426615701 775048359180641223122611)
            ·
              refine ⟨1162572538770961834683917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775048359180641223122611 1162572538770961834683917)
              ·
                refine ⟨435964702039110688006469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1162572538770961834683917 435964702039110688006469)
                ·
                  refine ⟨81743381632333254001213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435964702039110688006469 81743381632333254001213)
                  ·
                    rfl

theorem cell21_358188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_358188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358188 prefixEnd_358188 := by exact prefixLift 358188
  have htrace : WordTrace (prefixWord ++ tailWord_358188) baseStart_358188 baseEnd_358188 := by
    simpa [prefixWord, tailWord_358188, baseEnd_358188] using wordTrace_append hprefix tailTrace_358188
  have hstable : (prefixWord ++ tailWord_358188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358188).length < 2 ^ (prefixWord ++ tailWord_358188).sum := by decide
  have hdescent : baseEnd_358188 < baseStart_358188 := by decide
  rcases family_descends (prefixWord ++ tailWord_358188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358202 : List Nat := [3, 1, 1, 1, 5, 1, 2, 7]
def baseStart_358202 : Nat := 118140960795 + 358202 * 2 ^ 59
def prefixEnd_358202 : Nat := 4983230072969 + 3 ^ 40 * 358202 * 2
def baseEnd_358202 : Nat := 27248858874357446922617

theorem tailTrace_358202 : CollatzResearch.WordTrace tailWord_358202 prefixEnd_358202 27248858874357446922617 := by
  unfold tailWord_358202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266175062075701219059215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8709800165535203250824573 3266175062075701219059215)
  ·
    refine ⟨4899262593113551828588823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266175062075701219059215 4899262593113551828588823)
    ·
      refine ⟨7348893889670327742883235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899262593113551828588823 7348893889670327742883235)
      ·
        refine ⟨11023340834505491614324853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348893889670327742883235 11023340834505491614324853)
        ·
          refine ⟨1033438203234889838842955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11023340834505491614324853 1033438203234889838842955)
          ·
            refine ⟨1550157304852334758264433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033438203234889838842955 1550157304852334758264433)
            ·
              refine ⟨1162617978639251068698325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550157304852334758264433 1162617978639251068698325)
              ·
                refine ⟨27248858874357446922617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1162617978639251068698325 27248858874357446922617)
                ·
                  rfl

theorem cell21_358202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_358202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358202 prefixEnd_358202 := by exact prefixLift 358202
  have htrace : WordTrace (prefixWord ++ tailWord_358202) baseStart_358202 baseEnd_358202 := by
    simpa [prefixWord, tailWord_358202, baseEnd_358202] using wordTrace_append hprefix tailTrace_358202
  have hstable : (prefixWord ++ tailWord_358202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358202).length < 2 ^ (prefixWord ++ tailWord_358202).sum := by decide
  have hdescent : baseEnd_358202 < baseStart_358202 := by decide
  rcases family_descends (prefixWord ++ tailWord_358202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358236 : List Nat := [2, 2, 4, 2, 2, 2, 1, 6]
def baseStart_358236 : Nat := 118140960795 + 358236 * 2 ^ 59
def prefixEnd_358236 : Nat := 4983230072969 + 3 ^ 40 * 358236 * 2
def baseEnd_358236 : Nat := 27251445295431945733705

theorem tailTrace_358236 : CollatzResearch.WordTrace tailWord_358236 prefixEnd_358236 27251445295431945733705 := by
  unfold tailWord_358236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532970165089814341487281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8710626886786419121983041 6532970165089814341487281)
  ·
    refine ⟨4899727623817360756115461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6532970165089814341487281 4899727623817360756115461)
    ·
      refine ⟨918698929465755141771649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4899727623817360756115461 918698929465755141771649)
      ·
        refine ⟨689024197099316356328737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918698929465755141771649 689024197099316356328737)
        ·
          refine ⟨516768147824487267246553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689024197099316356328737 516768147824487267246553)
          ·
            refine ⟨387576110868365450434915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516768147824487267246553 387576110868365450434915)
            ·
              refine ⟨581364166302548175652373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387576110868365450434915 581364166302548175652373)
              ·
                refine ⟨27251445295431945733705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 581364166302548175652373 27251445295431945733705)
                ·
                  rfl

theorem cell21_358236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_358236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358236 prefixEnd_358236 := by exact prefixLift 358236
  have htrace : WordTrace (prefixWord ++ tailWord_358236) baseStart_358236 baseEnd_358236 := by
    simpa [prefixWord, tailWord_358236, baseEnd_358236] using wordTrace_append hprefix tailTrace_358236
  have hstable : (prefixWord ++ tailWord_358236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358236).length < 2 ^ (prefixWord ++ tailWord_358236).sum := by decide
  have hdescent : baseEnd_358236 < baseStart_358236 := by decide
  rcases family_descends (prefixWord ++ tailWord_358236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358312 : List Nat := [2, 1, 6, 2, 1, 1, 1, 7]
def baseStart_358312 : Nat := 118140960795 + 358312 * 2 ^ 59
def prefixEnd_358312 : Nat := 4983230072969 + 3 ^ 40 * 358312 * 2
def baseEnd_358312 : Nat := 27257226707245531311431

theorem tailTrace_358312 : CollatzResearch.WordTrace tailWord_358312 prefixEnd_358312 27257226707245531311431 := by
  unfold tailWord_358312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6534356138952146831370595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8712474851936195775160793 6534356138952146831370595)
  ·
    refine ⟨9801534208428220247055893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6534356138952146831370595 9801534208428220247055893)
    ·
      refine ⟨459446916020072824080745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9801534208428220247055893 459446916020072824080745)
      ·
        refine ⟨344585187015054618060559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459446916020072824080745 344585187015054618060559)
        ·
          refine ⟨516877780522581927090839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344585187015054618060559 516877780522581927090839)
          ·
            refine ⟨775316670783872890636259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516877780522581927090839 775316670783872890636259)
            ·
              refine ⟨1162975006175809335954389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775316670783872890636259 1162975006175809335954389)
              ·
                refine ⟨27257226707245531311431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1162975006175809335954389 27257226707245531311431)
                ·
                  rfl

theorem cell21_358312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_358312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358312 prefixEnd_358312 := by exact prefixLift 358312
  have htrace : WordTrace (prefixWord ++ tailWord_358312) baseStart_358312 baseEnd_358312 := by
    simpa [prefixWord, tailWord_358312, baseEnd_358312] using wordTrace_append hprefix tailTrace_358312
  have hstable : (prefixWord ++ tailWord_358312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358312).length < 2 ^ (prefixWord ++ tailWord_358312).sum := by decide
  have hdescent : baseEnd_358312 < baseStart_358312 := by decide
  rcases family_descends (prefixWord ++ tailWord_358312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358318 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_358318 : Nat := 118140960795 + 358318 * 2 ^ 59
def prefixEnd_358318 : Nat := 4983230072969 + 3 ^ 40 * 358318 * 2
def baseEnd_358318 : Nat := 81773049403481916834281

theorem tailTrace_358318 : CollatzResearch.WordTrace tailWord_358318 prefixEnd_358318 81773049403481916834281 := by
  unfold tailWord_358318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633616389485319585932451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8712620743921704458306405 1633616389485319585932451)
  ·
    refine ⟨2450424584227979378898677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1633616389485319585932451 2450424584227979378898677)
    ·
      refine ⟨229727304771373066771751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2450424584227979378898677 229727304771373066771751)
      ·
        refine ⟨344590957157059600157627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229727304771373066771751 344590957157059600157627)
        ·
          refine ⟨516886435735589400236441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344590957157059600157627 516886435735589400236441)
          ·
            refine ⟨387664826801692050177331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516886435735589400236441 387664826801692050177331)
            ·
              refine ⟨581497240202538075265997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387664826801692050177331 581497240202538075265997)
              ·
                refine ⟨218061465075951778224749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 581497240202538075265997 218061465075951778224749)
                ·
                  refine ⟨81773049403481916834281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218061465075951778224749 81773049403481916834281)
                  ·
                    rfl

theorem cell21_358318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_358318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358318 prefixEnd_358318 := by exact prefixLift 358318
  have htrace : WordTrace (prefixWord ++ tailWord_358318) baseStart_358318 baseEnd_358318 := by
    simpa [prefixWord, tailWord_358318, baseEnd_358318] using wordTrace_append hprefix tailTrace_358318
  have hstable : (prefixWord ++ tailWord_358318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358318).length < 2 ^ (prefixWord ++ tailWord_358318).sum := by decide
  have hdescent : baseEnd_358318 < baseStart_358318 := by decide
  rcases family_descends (prefixWord ++ tailWord_358318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358357 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 4]
def baseStart_358357 : Nat := 118140960795 + 358357 * 2 ^ 59
def prefixEnd_358357 : Nat := 4983230072969 + 3 ^ 40 * 358357 * 2
def baseEnd_358357 : Nat := 81781949734826515684201

theorem tailTrace_358357 : CollatzResearch.WordTrace tailWord_358357 prefixEnd_358357 81781949734826515684201 := by
  unfold tailWord_358357
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070353562741266348129325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8713569041827510898752883 13070353562741266348129325)
  ·
    refine ⟨4901382586027974880548497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13070353562741266348129325 4901382586027974880548497)
    ·
      refine ⟨3676036939520981160411373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4901382586027974880548497 3676036939520981160411373)
      ·
        refine ⟨1378513852320367935154265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3676036939520981160411373 1378513852320367935154265)
        ·
          refine ⟨1033885389240275951365699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378513852320367935154265 1033885389240275951365699)
          ·
            refine ⟨1550828083860413927048549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033885389240275951365699 1550828083860413927048549)
            ·
              refine ⟨290780265723827611321603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1550828083860413927048549 290780265723827611321603)
              ·
                refine ⟨436170398585741416982405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290780265723827611321603 436170398585741416982405)
                ·
                  refine ⟨81781949734826515684201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436170398585741416982405 81781949734826515684201)
                  ·
                    rfl

theorem cell21_358357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_358357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358357 prefixEnd_358357 := by exact prefixLift 358357
  have htrace : WordTrace (prefixWord ++ tailWord_358357) baseStart_358357 baseEnd_358357 := by
    simpa [prefixWord, tailWord_358357, baseEnd_358357] using wordTrace_append hprefix tailTrace_358357
  have hstable : (prefixWord ++ tailWord_358357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358357).length < 2 ^ (prefixWord ++ tailWord_358357).sum := by decide
  have hdescent : baseEnd_358357 < baseStart_358357 := by decide
  rcases family_descends (prefixWord ++ tailWord_358357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358368 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_358368 : Nat := 118140960795 + 358368 * 2 ^ 59
def prefixEnd_358368 : Nat := 4983230072969 + 3 ^ 40 * 358368 * 2
def baseEnd_358368 : Nat := 81784460084692941000845

theorem tailTrace_358368 : CollatzResearch.WordTrace tailWord_358368 prefixEnd_358368 81784460084692941000845 := by
  unfold tailWord_358368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535377382850707613389879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8713836510467610151186505 6535377382850707613389879)
  ·
    refine ⟨9803066074276061420084819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6535377382850707613389879 9803066074276061420084819)
    ·
      refine ⟨14704599111414092130127229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9803066074276061420084819 14704599111414092130127229)
      ·
        refine ⟨5514224666780284548797711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14704599111414092130127229 5514224666780284548797711)
        ·
          refine ⟨8271337000170426823196567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514224666780284548797711 8271337000170426823196567)
          ·
            refine ⟨12407005500255640234794851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8271337000170426823196567 12407005500255640234794851)
            ·
              refine ⟨18610508250383460352192277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12407005500255640234794851 18610508250383460352192277)
              ·
                refine ⟨872367574236724704009013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18610508250383460352192277 872367574236724704009013)
                ·
                  refine ⟨81784460084692941000845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 872367574236724704009013 81784460084692941000845)
                  ·
                    rfl

theorem cell21_358368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_358368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358368 prefixEnd_358368 := by exact prefixLift 358368
  have htrace : WordTrace (prefixWord ++ tailWord_358368) baseStart_358368 baseEnd_358368 := by
    simpa [prefixWord, tailWord_358368, baseEnd_358368] using wordTrace_append hprefix tailTrace_358368
  have hstable : (prefixWord ++ tailWord_358368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358368).length < 2 ^ (prefixWord ++ tailWord_358368).sum := by decide
  have hdescent : baseEnd_358368 < baseStart_358368 := by decide
  rcases family_descends (prefixWord ++ tailWord_358368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358461 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 5]
def baseStart_358461 : Nat := 118140960795 + 358461 * 2 ^ 59
def prefixEnd_358461 : Nat := 4983230072969 + 3 ^ 40 * 358461 * 2
def baseEnd_358461 : Nat := 81805683951745445950655

theorem tailTrace_358461 : CollatzResearch.WordTrace tailWord_358461 prefixEnd_358461 81805683951745445950655 := by
  unfold tailWord_358461
  simp only [CollatzResearch.WordTrace]
  refine ⟨13074146754364492109915237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8716097836242994739943491 13074146754364492109915237)
  ·
    refine ⟨2451402516443342270609107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13074146754364492109915237 2451402516443342270609107)
    ·
      refine ⟨3677103774665013405913661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451402516443342270609107 3677103774665013405913661)
      ·
        refine ⟨1378913915499380027217623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3677103774665013405913661 1378913915499380027217623)
        ·
          refine ⟨2068370873249070040826435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378913915499380027217623 2068370873249070040826435)
          ·
            refine ⟨3102556309873605061239653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068370873249070040826435 3102556309873605061239653)
            ·
              refine ⟨581729308101300948982435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3102556309873605061239653 581729308101300948982435)
              ·
                refine ⟨872593962151951423473653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581729308101300948982435 872593962151951423473653)
                ·
                  refine ⟨81805683951745445950655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 872593962151951423473653 81805683951745445950655)
                  ·
                    rfl

theorem cell21_358461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_358461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358461 prefixEnd_358461 := by exact prefixLift 358461
  have htrace : WordTrace (prefixWord ++ tailWord_358461) baseStart_358461 baseEnd_358461 := by
    simpa [prefixWord, tailWord_358461, baseEnd_358461] using wordTrace_append hprefix tailTrace_358461
  have hstable : (prefixWord ++ tailWord_358461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358461).length < 2 ^ (prefixWord ++ tailWord_358461).sum := by decide
  have hdescent : baseEnd_358461 < baseStart_358461 := by decide
  rcases family_descends (prefixWord ++ tailWord_358461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358489 : List Nat := [1, 2, 1, 2, 2, 1, 5, 7]
def baseStart_358489 : Nat := 118140960795 + 358489 * 2 ^ 59
def prefixEnd_358489 : Nat := 4983230072969 + 3 ^ 40 * 358489 * 2
def baseEnd_358489 : Nat := 27270691311074539827977

theorem tailTrace_358489 : CollatzResearch.WordTrace tailWord_358489 prefixEnd_358489 27270691311074539827977 := by
  unfold tailWord_358489
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075167998263052891934521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8716778665508701927956347 13075167998263052891934521)
  ·
    refine ⟨9806375998697289668950891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13075167998263052891934521 9806375998697289668950891)
    ·
      refine ⟨14709563998045934503426337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9806375998697289668950891 14709563998045934503426337)
      ·
        refine ⟨11032172998534450877569753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14709563998045934503426337 11032172998534450877569753)
        ·
          refine ⟨8274129748900838158177315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11032172998534450877569753 8274129748900838158177315)
          ·
            refine ⟨12411194623351257237265973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274129748900838158177315 12411194623351257237265973)
            ·
              refine ⟨1163549495939180365993685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12411194623351257237265973 1163549495939180365993685)
              ·
                refine ⟨27270691311074539827977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1163549495939180365993685 27270691311074539827977)
                ·
                  rfl

theorem cell21_358489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_358489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358489 prefixEnd_358489 := by exact prefixLift 358489
  have htrace : WordTrace (prefixWord ++ tailWord_358489) baseStart_358489 baseEnd_358489 := by
    simpa [prefixWord, tailWord_358489, baseEnd_358489] using wordTrace_append hprefix tailTrace_358489
  have hstable : (prefixWord ++ tailWord_358489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358489).length < 2 ^ (prefixWord ++ tailWord_358489).sum := by decide
  have hdescent : baseEnd_358489 < baseStart_358489 := by decide
  rcases family_descends (prefixWord ++ tailWord_358489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358689 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 3]
def baseStart_358689 : Nat := 118140960795 + 358689 * 2 ^ 59
def prefixEnd_358689 : Nat := 4983230072969 + 3 ^ 40 * 358689 * 2
def baseEnd_358689 : Nat := 81857716658067716150189

theorem tailTrace_358689 : CollatzResearch.WordTrace tailWord_358689 prefixEnd_358689 81857716658067716150189 := by
  unfold tailWord_358689
  simp only [CollatzResearch.WordTrace]
  refine ⟨13082462597538487049215121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8721641731692324699476747 13082462597538487049215121)
  ·
    refine ⟨9811846948153865286911341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13082462597538487049215121 9811846948153865286911341)
    ·
      refine ⟨3679442605557699482591753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9811846948153865286911341 3679442605557699482591753)
      ·
        refine ⟨2759581954168274611943815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3679442605557699482591753 2759581954168274611943815)
        ·
          refine ⟨4139372931252411917915723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759581954168274611943815 4139372931252411917915723)
          ·
            refine ⟨6209059396878617876873585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139372931252411917915723 6209059396878617876873585)
            ·
              refine ⟨4656794547658963407655189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209059396878617876873585 4656794547658963407655189)
              ·
                refine ⟨218287244421513909733837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4656794547658963407655189 218287244421513909733837)
                ·
                  refine ⟨81857716658067716150189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218287244421513909733837 81857716658067716150189)
                  ·
                    rfl

theorem cell21_358689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_358689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358689 prefixEnd_358689 := by exact prefixLift 358689
  have htrace : WordTrace (prefixWord ++ tailWord_358689) baseStart_358689 baseEnd_358689 := by
    simpa [prefixWord, tailWord_358689, baseEnd_358689] using wordTrace_append hprefix tailTrace_358689
  have hstable : (prefixWord ++ tailWord_358689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358689).length < 2 ^ (prefixWord ++ tailWord_358689).sum := by decide
  have hdescent : baseEnd_358689 < baseStart_358689 := by decide
  rcases family_descends (prefixWord ++ tailWord_358689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358731 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 9]
def baseStart_358731 : Nat := 118140960795 + 358731 * 2 ^ 59
def prefixEnd_358731 : Nat := 4983230072969 + 3 ^ 40 * 358731 * 2
def baseEnd_358731 : Nat := 81867301630284976450103

theorem tailTrace_358731 : CollatzResearch.WordTrace tailWord_358731 prefixEnd_358731 81867301630284976450103 := by
  unfold tailWord_358731
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083994463386328222244047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8722662975590885481496031 13083994463386328222244047)
  ·
    refine ⟨19625991695079492333366071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13083994463386328222244047 19625991695079492333366071)
    ·
      refine ⟨29438987542619238500049107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19625991695079492333366071 29438987542619238500049107)
      ·
        refine ⟨44158481313928857750073661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29438987542619238500049107 44158481313928857750073661)
        ·
          refine ⟨16559430492723321656277623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44158481313928857750073661 16559430492723321656277623)
          ·
            refine ⟨24839145739084982484416435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16559430492723321656277623 24839145739084982484416435)
            ·
              refine ⟨37258718608627473726624653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24839145739084982484416435 37258718608627473726624653)
              ·
                refine ⟨13972019478235302647484245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37258718608627473726624653 13972019478235302647484245)
                ·
                  refine ⟨81867301630284976450103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13972019478235302647484245 81867301630284976450103)
                  ·
                    rfl

theorem cell21_358731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_358731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358731 prefixEnd_358731 := by exact prefixLift 358731
  have htrace : WordTrace (prefixWord ++ tailWord_358731) baseStart_358731 baseEnd_358731 := by
    simpa [prefixWord, tailWord_358731, baseEnd_358731] using wordTrace_append hprefix tailTrace_358731
  have hstable : (prefixWord ++ tailWord_358731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358731).length < 2 ^ (prefixWord ++ tailWord_358731).sum := by decide
  have hdescent : baseEnd_358731 < baseStart_358731 := by decide
  rcases family_descends (prefixWord ++ tailWord_358731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358793 : List Nat := [1, 2, 1, 1, 6, 2, 8]
def baseStart_358793 : Nat := 118140960795 + 358793 * 2 ^ 59
def prefixEnd_358793 : Nat := 4983230072969 + 3 ^ 40 * 358793 * 2
def baseEnd_358793 : Nat := 9097938986109627379627

theorem tailTrace_358793 : CollatzResearch.WordTrace tailWord_358793 prefixEnd_358793 9097938986109627379627 := by
  unfold tailWord_358793
  simp only [CollatzResearch.WordTrace]
  refine ⟨13086255789161712811001033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8724170526107808540667355 13086255789161712811001033)
  ·
    refine ⟨9814691841871284608250775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13086255789161712811001033 9814691841871284608250775)
    ·
      refine ⟨14722037762806926912376163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9814691841871284608250775 14722037762806926912376163)
      ·
        refine ⟨22083056644210390368564245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14722037762806926912376163 22083056644210390368564245)
        ·
          refine ⟨1035143280197362048526449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22083056644210390368564245 1035143280197362048526449)
          ·
            refine ⟨776357460148021536394837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035143280197362048526449 776357460148021536394837)
            ·
              refine ⟨9097938986109627379627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 776357460148021536394837 9097938986109627379627)
              ·
                rfl

theorem cell21_358793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 8].length) (baseStart_358793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358793 prefixEnd_358793 := by exact prefixLift 358793
  have htrace : WordTrace (prefixWord ++ tailWord_358793) baseStart_358793 baseEnd_358793 := by
    simpa [prefixWord, tailWord_358793, baseEnd_358793] using wordTrace_append hprefix tailTrace_358793
  have hstable : (prefixWord ++ tailWord_358793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358793).length < 2 ^ (prefixWord ++ tailWord_358793).sum := by decide
  have hdescent : baseEnd_358793 < baseStart_358793 := by decide
  rcases family_descends (prefixWord ++ tailWord_358793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358796 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_358796 : Nat := 118140960795 + 358796 * 2 ^ 59
def prefixEnd_358796 : Nat := 4983230072969 + 3 ^ 40 * 358796 * 2
def baseEnd_358796 : Nat := 81882135515859307866637

theorem tailTrace_358796 : CollatzResearch.WordTrace tailWord_358796 prefixEnd_358796 81882135515859307866637 := by
  unfold tailWord_358796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6543182604075422161680121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8724243472100562882240161 6543182604075422161680121)
  ·
    refine ⟨4907386953056566621260091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6543182604075422161680121 4907386953056566621260091)
    ·
      refine ⟨7361080429584849931890137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4907386953056566621260091 7361080429584849931890137)
      ·
        refine ⟨5520810322188637448917603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7361080429584849931890137 5520810322188637448917603)
        ·
          refine ⟨8281215483282956173376405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520810322188637448917603 8281215483282956173376405)
          ·
            refine ⟨388181975778888570627019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8281215483282956173376405 388181975778888570627019)
            ·
              refine ⟨582272963668332855940529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388181975778888570627019 582272963668332855940529)
              ·
                refine ⟨436704722751249641955397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582272963668332855940529 436704722751249641955397)
                ·
                  refine ⟨81882135515859307866637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436704722751249641955397 81882135515859307866637)
                  ·
                    rfl

theorem cell21_358796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_358796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358796 prefixEnd_358796 := by exact prefixLift 358796
  have htrace : WordTrace (prefixWord ++ tailWord_358796) baseStart_358796 baseEnd_358796 := by
    simpa [prefixWord, tailWord_358796, baseEnd_358796] using wordTrace_append hprefix tailTrace_358796
  have hstable : (prefixWord ++ tailWord_358796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358796).length < 2 ^ (prefixWord ++ tailWord_358796).sum := by decide
  have hdescent : baseEnd_358796 < baseStart_358796 := by decide
  rcases family_descends (prefixWord ++ tailWord_358796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358813 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 4]
def baseStart_358813 : Nat := 118140960795 + 358813 * 2 ^ 59
def prefixEnd_358813 : Nat := 4983230072969 + 3 ^ 40 * 358813 * 2
def baseEnd_358813 : Nat := 81886015147471056083269

theorem tailTrace_358813 : CollatzResearch.WordTrace tailWord_358813 prefixEnd_358813 81886015147471056083269 := by
  unfold tailWord_358813
  simp only [CollatzResearch.WordTrace]
  refine ⟨13086985249089256226729093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8724656832726170817819395 13086985249089256226729093)
  ·
    refine ⟨2453809734204235542511705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13086985249089256226729093 2453809734204235542511705)
    ·
      refine ⟨1840357300653176656883779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2453809734204235542511705 1840357300653176656883779)
      ·
        refine ⟨2760535950979764985325669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840357300653176656883779 2760535950979764985325669)
        ·
          refine ⟨517600490808705934748563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2760535950979764985325669 517600490808705934748563)
          ·
            refine ⟨776400736213058902122845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517600490808705934748563 776400736213058902122845)
            ·
              refine ⟨291150276079897088296067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776400736213058902122845 291150276079897088296067)
              ·
                refine ⟨436725414119845632444101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291150276079897088296067 436725414119845632444101)
                ·
                  refine ⟨81886015147471056083269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436725414119845632444101 81886015147471056083269)
                  ·
                    rfl

theorem cell21_358813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_358813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358813 prefixEnd_358813 := by exact prefixLift 358813
  have htrace : WordTrace (prefixWord ++ tailWord_358813) baseStart_358813 baseEnd_358813 := by
    simpa [prefixWord, tailWord_358813, baseEnd_358813] using wordTrace_append hprefix tailTrace_358813
  have hstable : (prefixWord ++ tailWord_358813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358813).length < 2 ^ (prefixWord ++ tailWord_358813).sum := by decide
  have hdescent : baseEnd_358813 < baseStart_358813 := by decide
  rcases family_descends (prefixWord ++ tailWord_358813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358858 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_358858 : Nat := 118140960795 + 358858 * 2 ^ 59
def prefixEnd_358858 : Nat := 4983230072969 + 3 ^ 40 * 358858 * 2
def baseEnd_358858 : Nat := 81896284760560977833177

theorem tailTrace_358858 : CollatzResearch.WordTrace tailWord_358858 prefixEnd_358858 81896284760560977833177 := by
  unfold tailWord_358858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272156633481557228029307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8725751022617485941411485 3272156633481557228029307)
  ·
    refine ⟨4908234950222335842043961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3272156633481557228029307 4908234950222335842043961)
    ·
      refine ⟨3681176212666751881532971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4908234950222335842043961 3681176212666751881532971)
      ·
        refine ⟨5521764319000127822299457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681176212666751881532971 5521764319000127822299457)
        ·
          refine ⟨4141323239250095866724593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5521764319000127822299457 4141323239250095866724593)
          ·
            refine ⟨3105992429437571900043445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4141323239250095866724593 3105992429437571900043445)
            ·
              refine ⟨291186790259772365629073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3105992429437571900043445 291186790259772365629073)
              ·
                refine ⟨218390092694829274221805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291186790259772365629073 218390092694829274221805)
                ·
                  refine ⟨81896284760560977833177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218390092694829274221805 81896284760560977833177)
                  ·
                    rfl

theorem cell21_358858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_358858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358858 prefixEnd_358858 := by exact prefixLift 358858
  have htrace : WordTrace (prefixWord ++ tailWord_358858) baseStart_358858 baseEnd_358858 := by
    simpa [prefixWord, tailWord_358858, baseEnd_358858] using wordTrace_append hprefix tailTrace_358858
  have hstable : (prefixWord ++ tailWord_358858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358858).length < 2 ^ (prefixWord ++ tailWord_358858).sum := by decide
  have hdescent : baseEnd_358858 < baseStart_358858 := by decide
  rcases family_descends (prefixWord ++ tailWord_358858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358869 : List Nat := [1, 3, 2, 3, 1, 2, 1, 8]
def baseStart_358869 : Nat := 118140960795 + 358869 * 2 ^ 59
def prefixEnd_358869 : Nat := 4983230072969 + 3 ^ 40 * 358869 * 2
def baseEnd_358869 : Nat := 27299598370142467716607

theorem tailTrace_358869 : CollatzResearch.WordTrace tailWord_358869 prefixEnd_358869 27299598370142467716607 := by
  unfold tailWord_358869
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089027736886377790767661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8726018491257585193845107 13089027736886377790767661)
  ·
    refine ⟨4908385401332391671537873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13089027736886377790767661 4908385401332391671537873)
    ·
      refine ⟨3681289050999293753653405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4908385401332391671537873 3681289050999293753653405)
      ·
        refine ⟨1380483394124735157620027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3681289050999293753653405 1380483394124735157620027)
        ·
          refine ⟨2070725091187102736430041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380483394124735157620027 2070725091187102736430041)
          ·
            refine ⟨1553043818390327052322531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070725091187102736430041 1553043818390327052322531)
            ·
              refine ⟨2329565727585490578483797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553043818390327052322531 2329565727585490578483797)
              ·
                refine ⟨27299598370142467716607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2329565727585490578483797 27299598370142467716607)
                ·
                  rfl

theorem cell21_358869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_358869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358869 prefixEnd_358869 := by exact prefixLift 358869
  have htrace : WordTrace (prefixWord ++ tailWord_358869) baseStart_358869 baseEnd_358869 := by
    simpa [prefixWord, tailWord_358869, baseEnd_358869] using wordTrace_append hprefix tailTrace_358869
  have hstable : (prefixWord ++ tailWord_358869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358869).length < 2 ^ (prefixWord ++ tailWord_358869).sum := by decide
  have hdescent : baseEnd_358869 < baseStart_358869 := by decide
  rcases family_descends (prefixWord ++ tailWord_358869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358982 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_358982 : Nat := 118140960795 + 358982 * 2 ^ 59
def prefixEnd_358982 : Nat := 4983230072969 + 3 ^ 40 * 358982 * 2
def baseEnd_358982 : Nat := 81924583249964317766257

theorem tailTrace_358982 : CollatzResearch.WordTrace tailWord_358982 prefixEnd_358982 81924583249964317766257 := by
  unfold tailWord_358982
  simp only [CollatzResearch.WordTrace]
  refine ⟨409160912046156190300975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8728766123651332059754133 409160912046156190300975)
  ·
    refine ⟨613741368069234285451463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409160912046156190300975 613741368069234285451463)
    ·
      refine ⟨920612052103851428177195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613741368069234285451463 920612052103851428177195)
      ·
        refine ⟨1380918078155777142265793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920612052103851428177195 1380918078155777142265793)
        ·
          refine ⟨1035688558616832856699345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380918078155777142265793 1035688558616832856699345)
          ·
            refine ⟨776766418962624642524509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035688558616832856699345 776766418962624642524509)
            ·
              refine ⟨291287407110984240946691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776766418962624642524509 291287407110984240946691)
              ·
                refine ⟨436931110666476361420037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291287407110984240946691 436931110666476361420037)
                ·
                  refine ⟨81924583249964317766257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436931110666476361420037 81924583249964317766257)
                  ·
                    rfl

theorem cell21_358982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_358982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_358982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_358982 prefixEnd_358982 := by exact prefixLift 358982
  have htrace : WordTrace (prefixWord ++ tailWord_358982) baseStart_358982 baseEnd_358982 := by
    simpa [prefixWord, tailWord_358982, baseEnd_358982] using wordTrace_append hprefix tailTrace_358982
  have hstable : (prefixWord ++ tailWord_358982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358982).length < 2 ^ (prefixWord ++ tailWord_358982).sum := by decide
  have hdescent : baseEnd_358982 < baseStart_358982 := by decide
  rcases family_descends (prefixWord ++ tailWord_358982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359021 : List Nat := [1, 5, 1, 1, 3, 1, 9]
def baseStart_359021 : Nat := 118140960795 + 359021 * 2 ^ 59
def prefixEnd_359021 : Nat := 4983230072969 + 3 ^ 40 * 359021 * 2
def baseEnd_359021 : Nat := 9103720397923212957353

theorem tailTrace_359021 : CollatzResearch.WordTrace tailWord_359021 prefixEnd_359021 9103720397923212957353 := by
  unfold tailWord_359021
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094571632335707750300917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8729714421557138500200611 13094571632335707750300917)
  ·
    refine ⟨1227616090531472601590711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13094571632335707750300917 1227616090531472601590711)
    ·
      refine ⟨1841424135797208902386067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227616090531472601590711 1841424135797208902386067)
      ·
        refine ⟨2762136203695813353579101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841424135797208902386067 2762136203695813353579101)
        ·
          refine ⟨1035801076385930007592163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2762136203695813353579101 1035801076385930007592163)
          ·
            refine ⟨1553701614578895011388245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035801076385930007592163 1553701614578895011388245)
            ·
              refine ⟨9103720397923212957353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1553701614578895011388245 9103720397923212957353)
              ·
                rfl

theorem cell21_359021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 9].length) (baseStart_359021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359021 prefixEnd_359021 := by exact prefixLift 359021
  have htrace : WordTrace (prefixWord ++ tailWord_359021) baseStart_359021 baseEnd_359021 := by
    simpa [prefixWord, tailWord_359021, baseEnd_359021] using wordTrace_append hprefix tailTrace_359021
  have hstable : (prefixWord ++ tailWord_359021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359021).length < 2 ^ (prefixWord ++ tailWord_359021).sum := by decide
  have hdescent : baseEnd_359021 < baseStart_359021 := by decide
  rcases family_descends (prefixWord ++ tailWord_359021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359035 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_359035 : Nat := 118140960795 + 359035 * 2 ^ 59
def prefixEnd_359035 : Nat := 4983230072969 + 3 ^ 40 * 359035 * 2
def baseEnd_359035 : Nat := 81936678572048003382815

theorem tailTrace_359035 : CollatzResearch.WordTrace tailWord_359035 prefixEnd_359035 81936678572048003382815 := by
  unfold tailWord_359035
  simp only [CollatzResearch.WordTrace]
  refine ⟨13095082254284988141310559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8730054836189992094207039 13095082254284988141310559)
  ·
    refine ⟨19642623381427482211965839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13095082254284988141310559 19642623381427482211965839)
    ·
      refine ⟨29463935072141223317948759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19642623381427482211965839 29463935072141223317948759)
      ·
        refine ⟨44195902608211834976923139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29463935072141223317948759 44195902608211834976923139)
        ·
          refine ⟨66293853912317752465384709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44195902608211834976923139 66293853912317752465384709)
          ·
            refine ⟨12430097608559578587259633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66293853912317752465384709 12430097608559578587259633)
            ·
              refine ⟨9322573206419683940444725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12430097608559578587259633 9322573206419683940444725)
              ·
                refine ⟨873991238101845369416693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9322573206419683940444725 873991238101845369416693)
                ·
                  refine ⟨81936678572048003382815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 873991238101845369416693 81936678572048003382815)
                  ·
                    rfl

theorem cell21_359035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_359035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359035 prefixEnd_359035 := by exact prefixLift 359035
  have htrace : WordTrace (prefixWord ++ tailWord_359035) baseStart_359035 baseEnd_359035 := by
    simpa [prefixWord, tailWord_359035, baseEnd_359035] using wordTrace_append hprefix tailTrace_359035
  have hstable : (prefixWord ++ tailWord_359035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359035).length < 2 ^ (prefixWord ++ tailWord_359035).sum := by decide
  have hdescent : baseEnd_359035 < baseStart_359035 := by decide
  rcases family_descends (prefixWord ++ tailWord_359035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359114 : List Nat := [3, 1, 2, 1, 4, 2, 3, 5]
def baseStart_359114 : Nat := 118140960795 + 359114 * 2 ^ 59
def prefixEnd_359114 : Nat := 4983230072969 + 3 ^ 40 * 359114 * 2
def baseEnd_359114 : Nat := 27318235816120473855329

theorem tailTrace_359114 : CollatzResearch.WordTrace tailWord_359114 prefixEnd_359114 27318235816120473855329 := by
  unfold tailWord_359114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274490905249696158359099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8731975747332523088957597 3274490905249696158359099)
  ·
    refine ⟨4911736357874544237538649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3274490905249696158359099 4911736357874544237538649)
    ·
      refine ⟨3683802268405908178153987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4911736357874544237538649 3683802268405908178153987)
      ·
        refine ⟨5525703402608862267230981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3683802268405908178153987 5525703402608862267230981)
        ·
          refine ⟨1036069387989161675105809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5525703402608862267230981 1036069387989161675105809)
          ·
            refine ⟨777052040991871256329357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036069387989161675105809 777052040991871256329357)
            ·
              refine ⟨291394515371951721123509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 777052040991871256329357 291394515371951721123509)
              ·
                refine ⟨27318235816120473855329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 291394515371951721123509 27318235816120473855329)
                ·
                  rfl

theorem cell21_359114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_359114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359114 prefixEnd_359114 := by exact prefixLift 359114
  have htrace : WordTrace (prefixWord ++ tailWord_359114) baseStart_359114 baseEnd_359114 := by
    simpa [prefixWord, tailWord_359114, baseEnd_359114] using wordTrace_append hprefix tailTrace_359114
  have hstable : (prefixWord ++ tailWord_359114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359114).length < 2 ^ (prefixWord ++ tailWord_359114).sum := by decide
  have hdescent : baseEnd_359114 < baseStart_359114 := by decide
  rcases family_descends (prefixWord ++ tailWord_359114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359210 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_359210 : Nat := 118140960795 + 359210 * 2 ^ 59
def prefixEnd_359210 : Nat := 4983230072969 + 3 ^ 40 * 359210 * 2
def baseEnd_359210 : Nat := 81976615956286587965791

theorem tailTrace_359210 : CollatzResearch.WordTrace tailWord_359210 prefixEnd_359210 81976615956286587965791 := by
  unfold tailWord_359210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3275366257162748257232771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8734310019100662019287389 3275366257162748257232771)
  ·
    refine ⟨4913049385744122385849157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3275366257162748257232771 4913049385744122385849157)
    ·
      refine ⟨921196759827022947346717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4913049385744122385849157 921196759827022947346717)
      ·
        refine ⟨345448784935133605255019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 921196759827022947346717 345448784935133605255019)
        ·
          refine ⟨518173177402700407882529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345448784935133605255019 518173177402700407882529)
          ·
            refine ⟨388629883052025305911897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518173177402700407882529 388629883052025305911897)
            ·
              refine ⟨291472412289018979433923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388629883052025305911897 291472412289018979433923)
              ·
                refine ⟨437208618433528469150885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291472412289018979433923 437208618433528469150885)
                ·
                  refine ⟨81976615956286587965791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437208618433528469150885 81976615956286587965791)
                  ·
                    rfl

theorem cell21_359210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_359210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359210 prefixEnd_359210 := by exact prefixLift 359210
  have htrace : WordTrace (prefixWord ++ tailWord_359210) baseStart_359210 baseEnd_359210 := by
    simpa [prefixWord, tailWord_359210, baseEnd_359210] using wordTrace_append hprefix tailTrace_359210
  have hstable : (prefixWord ++ tailWord_359210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359210).length < 2 ^ (prefixWord ++ tailWord_359210).sum := by decide
  have hdescent : baseEnd_359210 < baseStart_359210 := by decide
  rcases family_descends (prefixWord ++ tailWord_359210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359249 : List Nat := [1, 2, 2, 1, 7, 8]
def baseStart_359249 : Nat := 118140960795 + 359249 * 2 ^ 59
def prefixEnd_359249 : Nat := 4983230072969 + 3 ^ 40 * 359249 * 2
def baseEnd_359249 : Nat := 3036500603245599511693

theorem tailTrace_359249 : CollatzResearch.WordTrace tailWord_359249 prefixEnd_359249 3036500603245599511693 := by
  unfold tailWord_359249
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102887475509702689600801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8735258317006468459733867 13102887475509702689600801)
  ·
    refine ⟨9827165606632277017200601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13102887475509702689600801 9827165606632277017200601)
    ·
      refine ⟨7370374204974207762900451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9827165606632277017200601 7370374204974207762900451)
      ·
        refine ⟨11055561307461311644350677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7370374204974207762900451 11055561307461311644350677)
        ·
          refine ⟨259114718143624491664469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11055561307461311644350677 259114718143624491664469)
          ·
            refine ⟨3036500603245599511693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 259114718143624491664469 3036500603245599511693)
            ·
              rfl

theorem cell21_359249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 8].length) (baseStart_359249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359249 prefixEnd_359249 := by exact prefixLift 359249
  have htrace : WordTrace (prefixWord ++ tailWord_359249) baseStart_359249 baseEnd_359249 := by
    simpa [prefixWord, tailWord_359249, baseEnd_359249] using wordTrace_append hprefix tailTrace_359249
  have hstable : (prefixWord ++ tailWord_359249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359249).length < 2 ^ (prefixWord ++ tailWord_359249).sum := by decide
  have hdescent : baseEnd_359249 < baseStart_359249 := by decide
  rcases family_descends (prefixWord ++ tailWord_359249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359252 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_359252 : Nat := 118140960795 + 359252 * 2 ^ 59
def prefixEnd_359252 : Nat := 4983230072969 + 3 ^ 40 * 359252 * 2
def baseEnd_359252 : Nat := 81986200928503848265705

theorem tailTrace_359252 : CollatzResearch.WordTrace tailWord_359252 prefixEnd_359252 81986200928503848265705 := by
  unfold tailWord_359252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551498447249417100980005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8735331262999222801306673 6551498447249417100980005)
  ·
    refine ⟨1228405958859265706433751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6551498447249417100980005 1228405958859265706433751)
    ·
      refine ⟨1842608938288898559650627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228405958859265706433751 1842608938288898559650627)
      ·
        refine ⟨2763913407433347839475941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842608938288898559650627 2763913407433347839475941)
        ·
          refine ⟨518233763893752719901739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2763913407433347839475941 518233763893752719901739)
          ·
            refine ⟨777350645840629079852609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518233763893752719901739 777350645840629079852609)
            ·
              refine ⟨583012984380471809889457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777350645840629079852609 583012984380471809889457)
              ·
                refine ⟨437259738285353857417093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583012984380471809889457 437259738285353857417093)
                ·
                  refine ⟨81986200928503848265705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437259738285353857417093 81986200928503848265705)
                  ·
                    rfl

theorem cell21_359252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_359252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359252 prefixEnd_359252 := by exact prefixLift 359252
  have htrace : WordTrace (prefixWord ++ tailWord_359252) baseStart_359252 baseEnd_359252 := by
    simpa [prefixWord, tailWord_359252, baseEnd_359252] using wordTrace_append hprefix tailTrace_359252
  have hstable : (prefixWord ++ tailWord_359252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359252).length < 2 ^ (prefixWord ++ tailWord_359252).sum := by decide
  have hdescent : baseEnd_359252 < baseStart_359252 := by decide
  rcases family_descends (prefixWord ++ tailWord_359252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359263 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_359263 : Nat := 118140960795 + 359263 * 2 ^ 59
def prefixEnd_359263 : Nat := 4983230072969 + 3 ^ 40 * 359263 * 2
def baseEnd_359263 : Nat := 81988711278370273582349

theorem tailTrace_359263 : CollatzResearch.WordTrace tailWord_359263 prefixEnd_359263 81988711278370273582349 := by
  unfold tailWord_359263
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103398097458983080610443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8735598731639322053740295 13103398097458983080610443)
  ·
    refine ⟨19655097146188474620915665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13103398097458983080610443 19655097146188474620915665)
    ·
      refine ⟨14741322859641355965686749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19655097146188474620915665 14741322859641355965686749)
      ·
        refine ⟨5527996072365508487132531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14741322859641355965686749 5527996072365508487132531)
        ·
          refine ⟨8291994108548262730698797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5527996072365508487132531 8291994108548262730698797)
          ·
            refine ⟨3109497790705598524012049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8291994108548262730698797 3109497790705598524012049)
            ·
              refine ⟨2332123343029198893009037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3109497790705598524012049 2332123343029198893009037)
              ·
                refine ⟨874546253635949584878389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2332123343029198893009037 874546253635949584878389)
                ·
                  refine ⟨81988711278370273582349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 874546253635949584878389 81988711278370273582349)
                  ·
                    rfl

theorem cell21_359263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_359263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359263 prefixEnd_359263 := by exact prefixLift 359263
  have htrace : WordTrace (prefixWord ++ tailWord_359263) baseStart_359263 baseEnd_359263 := by
    simpa [prefixWord, tailWord_359263, baseEnd_359263] using wordTrace_append hprefix tailTrace_359263
  have hstable : (prefixWord ++ tailWord_359263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359263).length < 2 ^ (prefixWord ++ tailWord_359263).sum := by decide
  have hdescent : baseEnd_359263 < baseStart_359263 := by decide
  rcases family_descends (prefixWord ++ tailWord_359263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359370 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_359370 : Nat := 118140960795 + 359370 * 2 ^ 59
def prefixEnd_359370 : Nat := 4983230072969 + 3 ^ 40 * 359370 * 2
def baseEnd_359370 : Nat := 82013130136161865298797

theorem tailTrace_359370 : CollatzResearch.WordTrace tailWord_359370 prefixEnd_359370 82013130136161865298797 := by
  unfold tailWord_359370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276825177017835088688891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8738200472047560236503709 3276825177017835088688891)
  ·
    refine ⟨4915237765526752633033337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3276825177017835088688891 4915237765526752633033337)
    ·
      refine ⟨3686428324145064474775003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4915237765526752633033337 3686428324145064474775003)
      ·
        refine ⟨5529642486217596712162505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686428324145064474775003 5529642486217596712162505)
        ·
          refine ⟨4147231864663197534121879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529642486217596712162505 4147231864663197534121879)
          ·
            refine ⟨6220847796994796301182819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147231864663197534121879 6220847796994796301182819)
            ·
              refine ⟨9331271695492194451774229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220847796994796301182819 9331271695492194451774229)
              ·
                refine ⟨437403360726196614926917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9331271695492194451774229 437403360726196614926917)
                ·
                  refine ⟨82013130136161865298797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437403360726196614926917 82013130136161865298797)
                  ·
                    rfl

theorem cell21_359370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_359370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359370 prefixEnd_359370 := by exact prefixLift 359370
  have htrace : WordTrace (prefixWord ++ tailWord_359370) baseStart_359370 baseEnd_359370 := by
    simpa [prefixWord, tailWord_359370, baseEnd_359370] using wordTrace_append hprefix tailTrace_359370
  have hstable : (prefixWord ++ tailWord_359370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359370).length < 2 ^ (prefixWord ++ tailWord_359370).sum := by decide
  have hdescent : baseEnd_359370 < baseStart_359370 := by decide
  rcases family_descends (prefixWord ++ tailWord_359370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359384 : List Nat := [2, 1, 2, 2, 2, 3, 1, 8]
def baseStart_359384 : Nat := 118140960795 + 359384 * 2 ^ 59
def prefixEnd_359384 : Nat := 4983230072969 + 3 ^ 40 * 359384 * 2
def baseEnd_359384 : Nat := 27338775042300317355145

theorem tailTrace_359384 : CollatzResearch.WordTrace tailWord_359384 prefixEnd_359384 27338775042300317355145 := by
  unfold tailWord_359384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553905665010310372882603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8738540886680413830510137 6553905665010310372882603)
  ·
    refine ⟨9830858497515465559323905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553905665010310372882603 9830858497515465559323905)
    ·
      refine ⟨7373143873136599169492929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9830858497515465559323905 7373143873136599169492929)
      ·
        refine ⟨5529857904852449377119697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7373143873136599169492929 5529857904852449377119697)
        ·
          refine ⟨4147393428639337032839773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529857904852449377119697 4147393428639337032839773)
          ·
            refine ⟨1555272535739751387314915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4147393428639337032839773 1555272535739751387314915)
            ·
              refine ⟨2332908803609627080972373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555272535739751387314915 2332908803609627080972373)
              ·
                refine ⟨27338775042300317355145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2332908803609627080972373 27338775042300317355145)
                ·
                  rfl

theorem cell21_359384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_359384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359384 prefixEnd_359384 := by exact prefixLift 359384
  have htrace : WordTrace (prefixWord ++ tailWord_359384) baseStart_359384 baseEnd_359384 := by
    simpa [prefixWord, tailWord_359384, baseEnd_359384] using wordTrace_append hprefix tailTrace_359384
  have hstable : (prefixWord ++ tailWord_359384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359384).length < 2 ^ (prefixWord ++ tailWord_359384).sum := by decide
  have hdescent : baseEnd_359384 < baseStart_359384 := by decide
  rcases family_descends (prefixWord ++ tailWord_359384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359466 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 3]
def baseStart_359466 : Nat := 118140960795 + 359466 * 2 ^ 59
def prefixEnd_359466 : Nat := 4983230072969 + 3 ^ 40 * 359466 * 2
def baseEnd_359466 : Nat := 82035038644087031698601

theorem tailTrace_359466 : CollatzResearch.WordTrace tailWord_359466 prefixEnd_359466 82035038644087031698601 := by
  unfold tailWord_359466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277700528930887187562563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8740534743815699166833501 3277700528930887187562563)
  ·
    refine ⟨4916550793396330781343845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277700528930887187562563 4916550793396330781343845)
    ·
      refine ⟨921853273761812021501971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4916550793396330781343845 921853273761812021501971)
      ·
        refine ⟨1382779910642718032252957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921853273761812021501971 1382779910642718032252957)
        ·
          refine ⟨518542466491019262094859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1382779910642718032252957 518542466491019262094859)
          ·
            refine ⟨777813699736528893142289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518542466491019262094859 777813699736528893142289)
            ·
              refine ⟨583360274802396669856717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777813699736528893142289 583360274802396669856717)
              ·
                refine ⟨218760103050898751196269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 583360274802396669856717 218760103050898751196269)
                ·
                  refine ⟨82035038644087031698601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218760103050898751196269 82035038644087031698601)
                  ·
                    rfl

theorem cell21_359466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_359466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359466 prefixEnd_359466 := by exact prefixLift 359466
  have htrace : WordTrace (prefixWord ++ tailWord_359466) baseStart_359466 baseEnd_359466 := by
    simpa [prefixWord, tailWord_359466, baseEnd_359466] using wordTrace_append hprefix tailTrace_359466
  have hstable : (prefixWord ++ tailWord_359466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359466).length < 2 ^ (prefixWord ++ tailWord_359466).sum := by decide
  have hdescent : baseEnd_359466 < baseStart_359466 := by decide
  rcases family_descends (prefixWord ++ tailWord_359466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359491 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 5]
def baseStart_359491 : Nat := 118140960795 + 359491 * 2 ^ 59
def prefixEnd_359491 : Nat := 4983230072969 + 3 ^ 40 * 359491 * 2
def baseEnd_359491 : Nat := 82040743984692543781883

theorem tailTrace_359491 : CollatzResearch.WordTrace tailWord_359491 prefixEnd_359491 82040743984692543781883 := by
  unfold tailWord_359491
  simp only [CollatzResearch.WordTrace]
  refine ⟨13111713940632978019910327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8741142627088652013273551 13111713940632978019910327)
  ·
    refine ⟨19667570910949467029865491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13111713940632978019910327 19667570910949467029865491)
    ·
      refine ⟨29501356366424200544798237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19667570910949467029865491 29501356366424200544798237)
      ·
        refine ⟨11063008637409075204299339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29501356366424200544798237 11063008637409075204299339)
        ·
          refine ⟨16594512956113612806449009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11063008637409075204299339 16594512956113612806449009)
          ·
            refine ⟨12445884717085209604836757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16594512956113612806449009 12445884717085209604836757)
            ·
              refine ⟨583400846113369200226723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12445884717085209604836757 583400846113369200226723)
              ·
                refine ⟨875101269170053800340085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583400846113369200226723 875101269170053800340085)
                ·
                  refine ⟨82040743984692543781883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 875101269170053800340085 82040743984692543781883)
                  ·
                    rfl

theorem cell21_359491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_359491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359491 prefixEnd_359491 := by exact prefixLift 359491
  have htrace : WordTrace (prefixWord ++ tailWord_359491) baseStart_359491 baseEnd_359491 := by
    simpa [prefixWord, tailWord_359491, baseEnd_359491] using wordTrace_append hprefix tailTrace_359491
  have hstable : (prefixWord ++ tailWord_359491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359491).length < 2 ^ (prefixWord ++ tailWord_359491).sum := by decide
  have hdescent : baseEnd_359491 < baseStart_359491 := by decide
  rcases family_descends (prefixWord ++ tailWord_359491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359542 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_359542 : Nat := 118140960795 + 359542 * 2 ^ 59
def prefixEnd_359542 : Nat := 4983230072969 + 3 ^ 40 * 359542 * 2
def baseEnd_359542 : Nat := 82052382879527788431779

theorem tailTrace_359542 : CollatzResearch.WordTrace tailWord_359542 prefixEnd_359542 82052382879527788431779 := by
  unfold tailWord_359542
  simp only [CollatzResearch.WordTrace]
  refine ⟨819598378965513358126055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8742382708965475820011253 819598378965513358126055)
  ·
    refine ⟨1229397568448270037189083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 819598378965513358126055 1229397568448270037189083)
    ·
      refine ⟨1844096352672405055783625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229397568448270037189083 1844096352672405055783625)
      ·
        refine ⟨1383072264504303791837719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1844096352672405055783625 1383072264504303791837719)
        ·
          refine ⟨2074608396756455687756579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383072264504303791837719 2074608396756455687756579)
          ·
            refine ⟨3111912595134683531634869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074608396756455687756579 3111912595134683531634869)
            ·
              refine ⟨291741805793876581090769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3111912595134683531634869 291741805793876581090769)
              ·
                refine ⟨218806354345407435818077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291741805793876581090769 218806354345407435818077)
                ·
                  refine ⟨82052382879527788431779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218806354345407435818077 82052382879527788431779)
                  ·
                    rfl

theorem cell21_359542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_359542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359542 prefixEnd_359542 := by exact prefixLift 359542
  have htrace : WordTrace (prefixWord ++ tailWord_359542) baseStart_359542 baseEnd_359542 := by
    simpa [prefixWord, tailWord_359542, baseEnd_359542] using wordTrace_append hprefix tailTrace_359542
  have hstable : (prefixWord ++ tailWord_359542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359542).length < 2 ^ (prefixWord ++ tailWord_359542).sum := by decide
  have hdescent : baseEnd_359542 < baseStart_359542 := by decide
  rcases family_descends (prefixWord ++ tailWord_359542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359553 : List Nat := [1, 2, 4, 2, 2, 2, 2, 6]
def baseStart_359553 : Nat := 118140960795 + 359553 * 2 ^ 59
def prefixEnd_359553 : Nat := 4983230072969 + 3 ^ 40 * 359553 * 2
def baseEnd_359553 : Nat := 27351631076464737916141

theorem tailTrace_359553 : CollatzResearch.WordTrace tailWord_359553 prefixEnd_359553 27351631076464737916141 := by
  unfold tailWord_359553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113975266408362608667313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8742650177605575072444875 13113975266408362608667313)
  ·
    refine ⟨9835481449806271956500485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13113975266408362608667313 9835481449806271956500485)
    ·
      refine ⟨1844152771838675991843841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9835481449806271956500485 1844152771838675991843841)
      ·
        refine ⟨1383114578879006993882881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1844152771838675991843841 1383114578879006993882881)
        ·
          refine ⟨1037335934159255245412161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383114578879006993882881 1037335934159255245412161)
          ·
            refine ⟨778001950619441434059121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037335934159255245412161 778001950619441434059121)
            ·
              refine ⟨583501462964581075544341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778001950619441434059121 583501462964581075544341)
              ·
                refine ⟨27351631076464737916141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 583501462964581075544341 27351631076464737916141)
                ·
                  rfl

theorem cell21_359553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 6].length) (baseStart_359553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359553 prefixEnd_359553 := by exact prefixLift 359553
  have htrace : WordTrace (prefixWord ++ tailWord_359553) baseStart_359553 baseEnd_359553 := by
    simpa [prefixWord, tailWord_359553, baseEnd_359553] using wordTrace_append hprefix tailTrace_359553
  have hstable : (prefixWord ++ tailWord_359553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359553).length < 2 ^ (prefixWord ++ tailWord_359553).sum := by decide
  have hdescent : baseEnd_359553 < baseStart_359553 := by decide
  rcases family_descends (prefixWord ++ tailWord_359553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359556 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_359556 : Nat := 118140960795 + 359556 * 2 ^ 59
def prefixEnd_359556 : Nat := 4983230072969 + 3 ^ 40 * 359556 * 2
def baseEnd_359556 : Nat := 82055577870266875198417

theorem tailTrace_359556 : CollatzResearch.WordTrace tailWord_359556 prefixEnd_359556 82055577870266875198417 := by
  unfold tailWord_359556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557042342698747060513261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8742723123598329414017681 6557042342698747060513261)
  ·
    refine ⟨2458890878512030147692473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6557042342698747060513261 2458890878512030147692473)
    ·
      refine ⟨1844168158884022610769355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2458890878512030147692473 1844168158884022610769355)
      ·
        refine ⟨2766252238326033916154033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844168158884022610769355 2766252238326033916154033)
        ·
          refine ⟨2074689178744525437115525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2766252238326033916154033 2074689178744525437115525)
          ·
            refine ⟨389004221014598519459161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2074689178744525437115525 389004221014598519459161)
            ·
              refine ⟨291753165760948889594371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389004221014598519459161 291753165760948889594371)
              ·
                refine ⟨437629748641423334391557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291753165760948889594371 437629748641423334391557)
                ·
                  refine ⟨82055577870266875198417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437629748641423334391557 82055577870266875198417)
                  ·
                    rfl

theorem cell21_359556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_359556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359556 prefixEnd_359556 := by exact prefixLift 359556
  have htrace : WordTrace (prefixWord ++ tailWord_359556) baseStart_359556 baseEnd_359556 := by
    simpa [prefixWord, tailWord_359556, baseEnd_359556] using wordTrace_append hprefix tailTrace_359556
  have hstable : (prefixWord ++ tailWord_359556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359556).length < 2 ^ (prefixWord ++ tailWord_359556).sum := by decide
  have hdescent : baseEnd_359556 < baseStart_359556 := by decide
  rcases family_descends (prefixWord ++ tailWord_359556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359584 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_359584 : Nat := 118140960795 + 359584 * 2 ^ 59
def prefixEnd_359584 : Nat := 4983230072969 + 3 ^ 40 * 359584 * 2
def baseEnd_359584 : Nat := 82061967851745048731693

theorem tailTrace_359584 : CollatzResearch.WordTrace tailWord_359584 prefixEnd_359584 82061967851745048731693 := by
  unfold tailWord_359584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557552964648027451522903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8743403952864036602030537 6557552964648027451522903)
  ·
    refine ⟨9836329446972041177284355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6557552964648027451522903 9836329446972041177284355)
    ·
      refine ⟨14754494170458061765926533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9836329446972041177284355 14754494170458061765926533)
      ·
        refine ⟨2766467656960886581111225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14754494170458061765926533 2766467656960886581111225)
        ·
          refine ⟨2074850742720664935833419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2766467656960886581111225 2074850742720664935833419)
          ·
            refine ⟨3112276114080997403750129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074850742720664935833419 3112276114080997403750129)
            ·
              refine ⟨2334207085560748052812597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3112276114080997403750129 2334207085560748052812597)
              ·
                refine ⟨218831914271320129951181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2334207085560748052812597 218831914271320129951181)
                ·
                  refine ⟨82061967851745048731693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218831914271320129951181 82061967851745048731693)
                  ·
                    rfl

theorem cell21_359584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_359584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359584 prefixEnd_359584 := by exact prefixLift 359584
  have htrace : WordTrace (prefixWord ++ tailWord_359584) baseStart_359584 baseEnd_359584 := by
    simpa [prefixWord, tailWord_359584, baseEnd_359584] using wordTrace_append hprefix tailTrace_359584
  have hstable : (prefixWord ++ tailWord_359584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359584).length < 2 ^ (prefixWord ++ tailWord_359584).sum := by decide
  have hdescent : baseEnd_359584 < baseStart_359584 := by decide
  rcases family_descends (prefixWord ++ tailWord_359584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359601 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 3]
def baseStart_359601 : Nat := 118140960795 + 359601 * 2 ^ 59
def prefixEnd_359601 : Nat := 4983230072969 + 3 ^ 40 * 359601 * 2
def baseEnd_359601 : Nat := 82065847483356796948325

theorem tailTrace_359601 : CollatzResearch.WordTrace tailWord_359601 prefixEnd_359601 82065847483356796948325 := by
  unfold tailWord_359601
  simp only [CollatzResearch.WordTrace]
  refine ⟨13115725970234466806414657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8743817313489644537609771 13115725970234466806414657)
  ·
    refine ⟨9836794477675850104810993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13115725970234466806414657 9836794477675850104810993)
    ·
      refine ⟨7377595858256887578608245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9836794477675850104810993 7377595858256887578608245)
      ·
        refine ⟨691649611711583210494523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7377595858256887578608245 691649611711583210494523)
        ·
          refine ⟨1037474417567374815741785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691649611711583210494523 1037474417567374815741785)
          ·
            refine ⟨778105813175531111806339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037474417567374815741785 778105813175531111806339)
            ·
              refine ⟨1167158719763296667709509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778105813175531111806339 1167158719763296667709509)
              ·
                refine ⟨218842259955618125195533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1167158719763296667709509 218842259955618125195533)
                ·
                  refine ⟨82065847483356796948325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218842259955618125195533 82065847483356796948325)
                  ·
                    rfl

theorem cell21_359601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 3].length) (baseStart_359601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359601 prefixEnd_359601 := by exact prefixLift 359601
  have htrace : WordTrace (prefixWord ++ tailWord_359601) baseStart_359601 baseEnd_359601 := by
    simpa [prefixWord, tailWord_359601, baseEnd_359601] using wordTrace_append hprefix tailTrace_359601
  have hstable : (prefixWord ++ tailWord_359601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359601).length < 2 ^ (prefixWord ++ tailWord_359601).sum := by decide
  have hdescent : baseEnd_359601 < baseStart_359601 := by decide
  rcases family_descends (prefixWord ++ tailWord_359601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359618 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_359618 : Nat := 118140960795 + 359618 * 2 ^ 59
def prefixEnd_359618 : Nat := 4983230072969 + 3 ^ 40 * 359618 * 2
def baseEnd_359618 : Nat := 82069727114968545164957

theorem tailTrace_359618 : CollatzResearch.WordTrace tailWord_359618 prefixEnd_359618 82069727114968545164957 := by
  unfold tailWord_359618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279086502793219677445877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8744230674115252473189005 3279086502793219677445877)
  ·
    refine ⟨307414359636864344760551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3279086502793219677445877 307414359636864344760551)
    ·
      refine ⟨461121539455296517140827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307414359636864344760551 461121539455296517140827)
      ·
        refine ⟨691682309182944775711241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461121539455296517140827 691682309182944775711241)
        ·
          refine ⟨518761731887208581783431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691682309182944775711241 518761731887208581783431)
          ·
            refine ⟨778142597830812872675147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518761731887208581783431 778142597830812872675147)
            ·
              refine ⟨1167213896746219309012721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778142597830812872675147 1167213896746219309012721)
              ·
                refine ⟨875410422559664481759541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167213896746219309012721 875410422559664481759541)
                ·
                  refine ⟨82069727114968545164957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 875410422559664481759541 82069727114968545164957)
                  ·
                    rfl

theorem cell21_359618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_359618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359618 prefixEnd_359618 := by exact prefixLift 359618
  have htrace : WordTrace (prefixWord ++ tailWord_359618) baseStart_359618 baseEnd_359618 := by
    simpa [prefixWord, tailWord_359618, baseEnd_359618] using wordTrace_append hprefix tailTrace_359618
  have hstable : (prefixWord ++ tailWord_359618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359618).length < 2 ^ (prefixWord ++ tailWord_359618).sum := by decide
  have hdescent : baseEnd_359618 < baseStart_359618 := by decide
  rcases family_descends (prefixWord ++ tailWord_359618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359660 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_359660 : Nat := 118140960795 + 359660 * 2 ^ 59
def prefixEnd_359660 : Nat := 4983230072969 + 3 ^ 40 * 359660 * 2
def baseEnd_359660 : Nat := 82079312087185805464871

theorem tailTrace_359660 : CollatzResearch.WordTrace tailWord_359660 prefixEnd_359660 82079312087185805464871 := by
  unfold tailWord_359660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6558938938510359941406217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8745251918013813255208289 6558938938510359941406217)
  ·
    refine ⟨4919204203882769956054663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6558938938510359941406217 4919204203882769956054663)
    ·
      refine ⟨7378806305824154934081995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919204203882769956054663 7378806305824154934081995)
      ·
        refine ⟨11068209458736232401122993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378806305824154934081995 11068209458736232401122993)
        ·
          refine ⟨8301157094052174300842245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11068209458736232401122993 8301157094052174300842245)
          ·
            refine ⟨1556466955134782681407921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8301157094052174300842245 1556466955134782681407921)
            ·
              refine ⟨1167350216351087011055941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556466955134782681407921 1167350216351087011055941)
              ·
                refine ⟨218878165565828814572989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1167350216351087011055941 218878165565828814572989)
                ·
                  refine ⟨82079312087185805464871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218878165565828814572989 82079312087185805464871)
                  ·
                    rfl

theorem cell21_359660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_359660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359660 prefixEnd_359660 := by exact prefixLift 359660
  have htrace : WordTrace (prefixWord ++ tailWord_359660) baseStart_359660 baseEnd_359660 := by
    simpa [prefixWord, tailWord_359660, baseEnd_359660] using wordTrace_append hprefix tailTrace_359660
  have hstable : (prefixWord ++ tailWord_359660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359660).length < 2 ^ (prefixWord ++ tailWord_359660).sum := by decide
  have hdescent : baseEnd_359660 < baseStart_359660 := by decide
  rcases family_descends (prefixWord ++ tailWord_359660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359725 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 4]
def baseStart_359725 : Nat := 118140960795 + 359725 * 2 ^ 59
def prefixEnd_359725 : Nat := 4983230072969 + 3 ^ 40 * 359725 * 2
def baseEnd_359725 : Nat := 82094145972760136881405

theorem tailTrace_359725 : CollatzResearch.WordTrace tailWord_359725 prefixEnd_359725 82094145972760136881405 := by
  unfold tailWord_359725
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120248621785235983928629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8746832414523490655952419 13120248621785235983928629)
  ·
    refine ⟨1230023308292365873493309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13120248621785235983928629 1230023308292365873493309)
    ·
      refine ⟨461258740609637202559991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1230023308292365873493309 461258740609637202559991)
      ·
        refine ⟨691888110914455803839987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461258740609637202559991 691888110914455803839987)
        ·
          refine ⟨1037832166371683705759981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691888110914455803839987 1037832166371683705759981)
          ·
            refine ⟨389187062389381389659993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037832166371683705759981 389187062389381389659993)
            ·
              refine ⟨291890296792036042244995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389187062389381389659993 291890296792036042244995)
              ·
                refine ⟨437835445188054063367493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291890296792036042244995 437835445188054063367493)
                ·
                  refine ⟨82094145972760136881405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437835445188054063367493 82094145972760136881405)
                  ·
                    rfl

theorem cell21_359725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_359725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359725 prefixEnd_359725 := by exact prefixLift 359725
  have htrace : WordTrace (prefixWord ++ tailWord_359725) baseStart_359725 baseEnd_359725 := by
    simpa [prefixWord, tailWord_359725, baseEnd_359725] using wordTrace_append hprefix tailTrace_359725
  have hstable : (prefixWord ++ tailWord_359725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359725).length < 2 ^ (prefixWord ++ tailWord_359725).sum := by decide
  have hdescent : baseEnd_359725 < baseStart_359725 := by decide
  rcases family_descends (prefixWord ++ tailWord_359725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359812 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_359812 : Nat := 118140960795 + 359812 * 2 ^ 59
def prefixEnd_359812 : Nat := 4983230072969 + 3 ^ 40 * 359812 * 2
def baseEnd_359812 : Nat := 82114000558067318931227

theorem tailTrace_359812 : CollatzResearch.WordTrace tailWord_359812 prefixEnd_359812 82114000558067318931227 := by
  unfold tailWord_359812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6561710886235024921172845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8748947848313366561563793 6561710886235024921172845)
  ·
    refine ⟨2460641582338134345439817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6561710886235024921172845 2460641582338134345439817)
    ·
      refine ⟨1845481186753600759079863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2460641582338134345439817 1845481186753600759079863)
      ·
        refine ⟨2768221780130401138619795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845481186753600759079863 2768221780130401138619795)
        ·
          refine ⟨4152332670195601707929693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768221780130401138619795 4152332670195601707929693)
          ·
            refine ⟨1557124751323350640473635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4152332670195601707929693 1557124751323350640473635)
            ·
              refine ⟨2335687126985025960710453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557124751323350640473635 2335687126985025960710453)
              ·
                refine ⟨218970668154846183816605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2335687126985025960710453 218970668154846183816605)
                ·
                  refine ⟨82114000558067318931227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218970668154846183816605 82114000558067318931227)
                  ·
                    rfl

theorem cell21_359812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_359812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359812 prefixEnd_359812 := by exact prefixLift 359812
  have htrace : WordTrace (prefixWord ++ tailWord_359812) baseStart_359812 baseEnd_359812 := by
    simpa [prefixWord, tailWord_359812, baseEnd_359812] using wordTrace_append hprefix tailTrace_359812
  have hstable : (prefixWord ++ tailWord_359812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359812).length < 2 ^ (prefixWord ++ tailWord_359812).sum := by decide
  have hdescent : baseEnd_359812 < baseStart_359812 := by decide
  rcases family_descends (prefixWord ++ tailWord_359812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359950 : List Nat := [4, 1, 1, 2, 5, 1, 1, 6]
def baseStart_359950 : Nat := 118140960795 + 359950 * 2 ^ 59
def prefixEnd_359950 : Nat := 4983230072969 + 3 ^ 40 * 359950 * 2
def baseEnd_359950 : Nat := 27381831346069915210315

theorem tailTrace_359950 : CollatzResearch.WordTrace tailWord_359950 prefixEnd_359950 27381831346069915210315 := by
  unfold tailWord_359950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641056880746262426358663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8752303363980066273912869 1641056880746262426358663)
  ·
    refine ⟨2461585321119393639537995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1641056880746262426358663 2461585321119393639537995)
    ·
      refine ⟨3692377981679090459306993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461585321119393639537995 3692377981679090459306993)
      ·
        refine ⟨2769283486259317844480245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3692377981679090459306993 2769283486259317844480245)
        ·
          refine ⟨259620326836811047920023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2769283486259317844480245 259620326836811047920023)
          ·
            refine ⟨389430490255216571880035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259620326836811047920023 389430490255216571880035)
            ·
              refine ⟨584145735382824857820053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389430490255216571880035 584145735382824857820053)
              ·
                refine ⟨27381831346069915210315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 584145735382824857820053 27381831346069915210315)
                ·
                  rfl

theorem cell21_359950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_359950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_359950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_359950 prefixEnd_359950 := by exact prefixLift 359950
  have htrace : WordTrace (prefixWord ++ tailWord_359950) baseStart_359950 baseEnd_359950 := by
    simpa [prefixWord, tailWord_359950, baseEnd_359950] using wordTrace_append hprefix tailTrace_359950
  have hstable : (prefixWord ++ tailWord_359950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359950).length < 2 ^ (prefixWord ++ tailWord_359950).sum := by decide
  have hdescent : baseEnd_359950 < baseStart_359950 := by decide
  rcases family_descends (prefixWord ++ tailWord_359950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360037 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_360037 : Nat := 118140960795 + 360037 * 2 ^ 59
def prefixEnd_360037 : Nat := 4983230072969 + 3 ^ 40 * 360037 * 2
def baseEnd_360037 : Nat := 82165348623516927680767

theorem tailTrace_360037 : CollatzResearch.WordTrace tailWord_360037 prefixEnd_360037 82165348623516927680767 := by
  unfold tailWord_360037
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131628196654913269286365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8754418797769942179524243 13131628196654913269286365)
  ·
    refine ⟨4924360573745592475982387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13131628196654913269286365 4924360573745592475982387)
    ·
      refine ⟨7386540860618388713973581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924360573745592475982387 7386540860618388713973581)
      ·
        refine ⟨2769952822731895767740093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7386540860618388713973581 2769952822731895767740093)
        ·
          refine ⟨1038732308524460912902535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2769952822731895767740093 1038732308524460912902535)
          ·
            refine ⟨1558098462786691369353803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038732308524460912902535 1558098462786691369353803)
            ·
              refine ⟨2337147694180037054030705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558098462786691369353803 2337147694180037054030705)
              ·
                refine ⟨1752860770635027790523029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337147694180037054030705 1752860770635027790523029)
                ·
                  refine ⟨82165348623516927680767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1752860770635027790523029 82165348623516927680767)
                  ·
                    rfl

theorem cell21_360037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_360037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360037 prefixEnd_360037 := by exact prefixLift 360037
  have htrace : WordTrace (prefixWord ++ tailWord_360037) baseStart_360037 baseEnd_360037 := by
    simpa [prefixWord, tailWord_360037, baseEnd_360037] using wordTrace_append hprefix tailTrace_360037
  have hstable : (prefixWord ++ tailWord_360037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360037).length < 2 ^ (prefixWord ++ tailWord_360037).sum := by decide
  have hdescent : baseEnd_360037 < baseStart_360037 := by decide
  rcases family_descends (prefixWord ++ tailWord_360037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360054 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_360054 : Nat := 118140960795 + 360054 * 2 ^ 59
def prefixEnd_360054 : Nat := 4983230072969 + 3 ^ 40 * 360054 * 2
def baseEnd_360054 : Nat := 82169228255128675897399

theorem tailTrace_360054 : CollatzResearch.WordTrace tailWord_360054 prefixEnd_360054 82169228255128675897399 := by
  unfold tailWord_360054
  simp only [CollatzResearch.WordTrace]
  refine ⟨820765514849582823290951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8754832158395550115103477 820765514849582823290951)
  ·
    refine ⟨1231148272274374234936427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820765514849582823290951 1231148272274374234936427)
    ·
      refine ⟨1846722408411561352404641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231148272274374234936427 1846722408411561352404641)
      ·
        refine ⟨1385041806308671014303481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846722408411561352404641 1385041806308671014303481)
        ·
          refine ⟨1038781354731503260727611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1385041806308671014303481 1038781354731503260727611)
          ·
            refine ⟨1558172032097254891091417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038781354731503260727611 1558172032097254891091417)
            ·
              refine ⟨1168629024072941168318563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558172032097254891091417 1168629024072941168318563)
              ·
                refine ⟨1752943536109411752477845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168629024072941168318563 1752943536109411752477845)
                ·
                  refine ⟨82169228255128675897399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1752943536109411752477845 82169228255128675897399)
                  ·
                    rfl

theorem cell21_360054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_360054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360054 prefixEnd_360054 := by exact prefixLift 360054
  have htrace : WordTrace (prefixWord ++ tailWord_360054) baseStart_360054 baseEnd_360054 := by
    simpa [prefixWord, tailWord_360054, baseEnd_360054] using wordTrace_append hprefix tailTrace_360054
  have hstable : (prefixWord ++ tailWord_360054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360054).length < 2 ^ (prefixWord ++ tailWord_360054).sum := by decide
  have hdescent : baseEnd_360054 < baseStart_360054 := by decide
  rcases family_descends (prefixWord ++ tailWord_360054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360071 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 4]
def baseStart_360071 : Nat := 118140960795 + 360071 * 2 ^ 59
def prefixEnd_360071 : Nat := 4983230072969 + 3 ^ 40 * 360071 * 2
def baseEnd_360071 : Nat := 82173107886740424114031

theorem tailTrace_360071 : CollatzResearch.WordTrace tailWord_360071 prefixEnd_360071 82173107886740424114031 := by
  unfold tailWord_360071
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132868278531737076024067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8755245519021158050682711 13132868278531737076024067)
  ·
    refine ⟨19699302417797605614036101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13132868278531737076024067 19699302417797605614036101)
    ·
      refine ⟨3693619203337051052631769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19699302417797605614036101 3693619203337051052631769)
      ·
        refine ⟨2770214402502788289473827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3693619203337051052631769 2770214402502788289473827)
        ·
          refine ⟨4155321603754182434210741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770214402502788289473827 4155321603754182434210741)
          ·
            refine ⟨389561400351954603207257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4155321603754182434210741 389561400351954603207257)
            ·
              refine ⟨292171050263965952405443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389561400351954603207257 292171050263965952405443)
              ·
                refine ⟨438256575395948928608165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292171050263965952405443 438256575395948928608165)
                ·
                  refine ⟨82173107886740424114031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438256575395948928608165 82173107886740424114031)
                  ·
                    rfl

theorem cell21_360071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 4].length) (baseStart_360071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360071 prefixEnd_360071 := by exact prefixLift 360071
  have htrace : WordTrace (prefixWord ++ tailWord_360071) baseStart_360071 baseEnd_360071 := by
    simpa [prefixWord, tailWord_360071, baseEnd_360071] using wordTrace_append hprefix tailTrace_360071
  have hstable : (prefixWord ++ tailWord_360071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360071).length < 2 ^ (prefixWord ++ tailWord_360071).sum := by decide
  have hdescent : baseEnd_360071 < baseStart_360071 := by decide
  rcases family_descends (prefixWord ++ tailWord_360071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360099 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 3]
def baseStart_360099 : Nat := 118140960795 + 360099 * 2 ^ 59
def prefixEnd_360099 : Nat := 4983230072969 + 3 ^ 40 * 360099 * 2
def baseEnd_360099 : Nat := 82179497868218597647307

theorem tailTrace_360099 : CollatzResearch.WordTrace tailWord_360099 prefixEnd_360099 82179497868218597647307 := by
  unfold tailWord_360099
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133889522430297858043351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8755926348286865238695567 13133889522430297858043351)
  ·
    refine ⟨19700834283645446787065027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13133889522430297858043351 19700834283645446787065027)
    ·
      refine ⟨29551251425468170180597541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19700834283645446787065027 29551251425468170180597541)
      ·
        refine ⟨5540859642275281908862039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29551251425468170180597541 5540859642275281908862039)
        ·
          refine ⟨8311289463412922863293059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540859642275281908862039 8311289463412922863293059)
          ·
            refine ⟨12466934195119384294939589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8311289463412922863293059 12466934195119384294939589)
            ·
              refine ⟨2337550161584884555301173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12466934195119384294939589 2337550161584884555301173)
              ·
                refine ⟨219145327648582927059485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2337550161584884555301173 219145327648582927059485)
                ·
                  refine ⟨82179497868218597647307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219145327648582927059485 82179497868218597647307)
                  ·
                    rfl

theorem cell21_360099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 3].length) (baseStart_360099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360099 prefixEnd_360099 := by exact prefixLift 360099
  have htrace : WordTrace (prefixWord ++ tailWord_360099) baseStart_360099 baseEnd_360099 := by
    simpa [prefixWord, tailWord_360099, baseEnd_360099] using wordTrace_append hprefix tailTrace_360099
  have hstable : (prefixWord ++ tailWord_360099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360099).length < 2 ^ (prefixWord ++ tailWord_360099).sum := by decide
  have hdescent : baseEnd_360099 < baseStart_360099 := by decide
  rcases family_descends (prefixWord ++ tailWord_360099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360175 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 3]
def baseStart_360175 : Nat := 118140960795 + 360175 * 2 ^ 59
def prefixEnd_360175 : Nat := 4983230072969 + 3 ^ 40 * 360175 * 2
def baseEnd_360175 : Nat := 82196842103659354380485

theorem tailTrace_360175 : CollatzResearch.WordTrace tailWord_360175 prefixEnd_360175 82196842103659354380485 := by
  unfold tailWord_360175
  simp only [CollatzResearch.WordTrace]
  refine ⟨13136661470154962837809979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8757774313436641891873319 13136661470154962837809979)
  ·
    refine ⟨19704992205232444256714969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13136661470154962837809979 19704992205232444256714969)
    ·
      refine ⟨14778744153924333192536227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19704992205232444256714969 14778744153924333192536227)
      ·
        refine ⟨22168116230886499788804341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14778744153924333192536227 22168116230886499788804341)
        ·
          refine ⟨2078260896645609355200407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22168116230886499788804341 2078260896645609355200407)
          ·
            refine ⟨3117391344968414032800611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078260896645609355200407 3117391344968414032800611)
            ·
              refine ⟨4676087017452621049200917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117391344968414032800611 4676087017452621049200917)
              ·
                refine ⟨219191578943091611681293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4676087017452621049200917 219191578943091611681293)
                ·
                  refine ⟨82196842103659354380485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219191578943091611681293 82196842103659354380485)
                  ·
                    rfl

theorem cell21_360175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 3].length) (baseStart_360175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360175 prefixEnd_360175 := by exact prefixLift 360175
  have htrace : WordTrace (prefixWord ++ tailWord_360175) baseStart_360175 baseEnd_360175 := by
    simpa [prefixWord, tailWord_360175, baseEnd_360175] using wordTrace_append hprefix tailTrace_360175
  have hstable : (prefixWord ++ tailWord_360175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360175).length < 2 ^ (prefixWord ++ tailWord_360175).sum := by decide
  have hdescent : baseEnd_360175 < baseStart_360175 := by decide
  rcases family_descends (prefixWord ++ tailWord_360175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360279 : List Nat := [1, 1, 3, 2, 5, 9]
def baseStart_360279 : Nat := 118140960795 + 360279 * 2 ^ 59
def prefixEnd_360279 : Nat := 4983230072969 + 3 ^ 40 * 360279 * 2
def baseEnd_360279 : Nat := 3045206530391788320257

theorem tailTrace_360279 : CollatzResearch.WordTrace tailWord_360279 prefixEnd_360279 3045206530391788320257 := by
  unfold tailWord_360279
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140454661778188599595891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8760303107852125733063927 13140454661778188599595891)
  ·
    refine ⟨19710681992667282899393837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13140454661778188599595891 19710681992667282899393837)
    ·
      refine ⟨7391505747250231087272689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19710681992667282899393837 7391505747250231087272689)
      ·
        refine ⟨5543629310437673315454517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7391505747250231087272689 5543629310437673315454517)
        ·
          refine ⟨519715247853531873323861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5543629310437673315454517 519715247853531873323861)
          ·
            refine ⟨3045206530391788320257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 519715247853531873323861 3045206530391788320257)
            ·
              rfl

theorem cell21_360279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 9].length) (baseStart_360279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360279 prefixEnd_360279 := by exact prefixLift 360279
  have htrace : WordTrace (prefixWord ++ tailWord_360279) baseStart_360279 baseEnd_360279 := by
    simpa [prefixWord, tailWord_360279, baseEnd_360279] using wordTrace_append hprefix tailTrace_360279
  have hstable : (prefixWord ++ tailWord_360279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360279).length < 2 ^ (prefixWord ++ tailWord_360279).sum := by decide
  have hdescent : baseEnd_360279 < baseStart_360279 := by decide
  rcases family_descends (prefixWord ++ tailWord_360279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360344 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_360344 : Nat := 118140960795 + 360344 * 2 ^ 59
def prefixEnd_360344 : Nat := 4983230072969 + 3 ^ 40 * 360344 * 2
def baseEnd_360344 : Nat := 82235410206152616063473

theorem tailTrace_360344 : CollatzResearch.WordTrace tailWord_360344 prefixEnd_360344 82235410206152616063473 := by
  unfold tailWord_360344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571412703271352350356043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8761883604361803133808057 6571412703271352350356043)
  ·
    refine ⟨9857119054907028525534065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571412703271352350356043 9857119054907028525534065)
    ·
      refine ⟨7392839291180271394150549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9857119054907028525534065 7392839291180271394150549)
      ·
        refine ⟨346539341774075221600807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7392839291180271394150549 346539341774075221600807)
        ·
          refine ⟨519809012661112832401211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346539341774075221600807 519809012661112832401211)
          ·
            refine ⟨779713518991669248601817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519809012661112832401211 779713518991669248601817)
            ·
              refine ⟨584785139243751936451363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779713518991669248601817 584785139243751936451363)
              ·
                refine ⟨877177708865627904677045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584785139243751936451363 877177708865627904677045)
                ·
                  refine ⟨82235410206152616063473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 877177708865627904677045 82235410206152616063473)
                  ·
                    rfl

theorem cell21_360344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_360344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360344 prefixEnd_360344 := by exact prefixLift 360344
  have htrace : WordTrace (prefixWord ++ tailWord_360344) baseStart_360344 baseEnd_360344 := by
    simpa [prefixWord, tailWord_360344, baseEnd_360344] using wordTrace_append hprefix tailTrace_360344
  have hstable : (prefixWord ++ tailWord_360344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360344).length < 2 ^ (prefixWord ++ tailWord_360344).sum := by decide
  have hdescent : baseEnd_360344 < baseStart_360344 := by decide
  rcases family_descends (prefixWord ++ tailWord_360344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360400 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_360400 : Nat := 118140960795 + 360400 * 2 ^ 59
def prefixEnd_360400 : Nat := 4983230072969 + 3 ^ 40 * 360400 * 2
def baseEnd_360400 : Nat := 82248190169108963130025

theorem tailTrace_360400 : CollatzResearch.WordTrace tailWord_360400 prefixEnd_360400 82248190169108963130025 := by
  unfold tailWord_360400
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572433947169913132375327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8763245262893217509833769 6572433947169913132375327)
  ·
    refine ⟨9858650920754869698562991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572433947169913132375327 9858650920754869698562991)
    ·
      refine ⟨14787976381132304547844487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9858650920754869698562991 14787976381132304547844487)
      ·
        refine ⟨22181964571698456821766731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14787976381132304547844487 22181964571698456821766731)
        ·
          refine ⟨33272946857547685232650097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22181964571698456821766731 33272946857547685232650097)
          ·
            refine ⟨24954710143160763924487573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33272946857547685232650097 24954710143160763924487573)
            ·
              refine ⟨1169752037960660808960355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24954710143160763924487573 1169752037960660808960355)
              ·
                refine ⟨1754628056940991213440533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169752037960660808960355 1754628056940991213440533)
                ·
                  refine ⟨82248190169108963130025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1754628056940991213440533 82248190169108963130025)
                  ·
                    rfl

theorem cell21_360400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_360400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360400 prefixEnd_360400 := by exact prefixLift 360400
  have htrace : WordTrace (prefixWord ++ tailWord_360400) baseStart_360400 baseEnd_360400 := by
    simpa [prefixWord, tailWord_360400, baseEnd_360400] using wordTrace_append hprefix tailTrace_360400
  have hstable : (prefixWord ++ tailWord_360400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360400).length < 2 ^ (prefixWord ++ tailWord_360400).sum := by decide
  have hdescent : baseEnd_360400 < baseStart_360400 := by decide
  rcases family_descends (prefixWord ++ tailWord_360400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360462 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_360462 : Nat := 118140960795 + 360462 * 2 ^ 59
def prefixEnd_360462 : Nat := 4983230072969 + 3 ^ 40 * 360462 * 2
def baseEnd_360462 : Nat := 82262339413810633096565

theorem tailTrace_360462 : CollatzResearch.WordTrace tailWord_360462 prefixEnd_360462 82262339413810633096565 := by
  unfold tailWord_360462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643391152514401356688455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8764752813410140569005093 1643391152514401356688455)
  ·
    refine ⟨2465086728771602035032683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643391152514401356688455 2465086728771602035032683)
    ·
      refine ⟨3697630093157403052549025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465086728771602035032683 3697630093157403052549025)
      ·
        refine ⟨2773222569868052289411769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3697630093157403052549025 2773222569868052289411769)
        ·
          refine ⟨2079916927401039217058827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773222569868052289411769 2079916927401039217058827)
          ·
            refine ⟨3119875391101558825588241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079916927401039217058827 3119875391101558825588241)
            ·
              refine ⟨2339906543326169119191181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119875391101558825588241 2339906543326169119191181)
              ·
                refine ⟨877464953747313419696693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2339906543326169119191181 877464953747313419696693)
                ·
                  refine ⟨82262339413810633096565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 877464953747313419696693 82262339413810633096565)
                  ·
                    rfl

theorem cell21_360462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_360462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360462 prefixEnd_360462 := by exact prefixLift 360462
  have htrace : WordTrace (prefixWord ++ tailWord_360462) baseStart_360462 baseEnd_360462 := by
    simpa [prefixWord, tailWord_360462, baseEnd_360462] using wordTrace_append hprefix tailTrace_360462
  have hstable : (prefixWord ++ tailWord_360462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360462).length < 2 ^ (prefixWord ++ tailWord_360462).sum := by decide
  have hdescent : baseEnd_360462 < baseStart_360462 := by decide
  rcases family_descends (prefixWord ++ tailWord_360462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360510 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 6]
def baseStart_360510 : Nat := 118140960795 + 360510 * 2 ^ 59
def prefixEnd_360510 : Nat := 4983230072969 + 3 ^ 40 * 360510 * 2
def baseEnd_360510 : Nat := 82273293667773216296467

theorem tailTrace_360510 : CollatzResearch.WordTrace tailWord_360510 prefixEnd_360510 82273293667773216296467 := by
  unfold tailWord_360510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643609990492664381406873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8765919949294210034169989 1643609990492664381406873)
  ·
    refine ⟨1232707492869498286055155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1643609990492664381406873 1232707492869498286055155)
    ·
      refine ⟨1849061239304247429082733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232707492869498286055155 1849061239304247429082733)
      ·
        refine ⟨693397964739092785906025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1849061239304247429082733 693397964739092785906025)
        ·
          refine ⟨520048473554319589429519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693397964739092785906025 520048473554319589429519)
          ·
            refine ⟨780072710331479384144279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520048473554319589429519 780072710331479384144279)
            ·
              refine ⟨1170109065497219076216419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780072710331479384144279 1170109065497219076216419)
              ·
                refine ⟨1755163598245828614324629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170109065497219076216419 1755163598245828614324629)
                ·
                  refine ⟨82273293667773216296467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1755163598245828614324629 82273293667773216296467)
                  ·
                    rfl

theorem cell21_360510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_360510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360510 prefixEnd_360510 := by exact prefixLift 360510
  have htrace : WordTrace (prefixWord ++ tailWord_360510) baseStart_360510 baseEnd_360510 := by
    simpa [prefixWord, tailWord_360510, baseEnd_360510] using wordTrace_append hprefix tailTrace_360510
  have hstable : (prefixWord ++ tailWord_360510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360510).length < 2 ^ (prefixWord ++ tailWord_360510).sum := by decide
  have hdescent : baseEnd_360510 < baseStart_360510 := by decide
  rcases family_descends (prefixWord ++ tailWord_360510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360541 : List Nat := [1, 4, 4, 1, 1, 1, 4, 5]
def baseStart_360541 : Nat := 118140960795 + 360541 * 2 ^ 59
def prefixEnd_360541 : Nat := 4983230072969 + 3 ^ 40 * 360541 * 2
def baseEnd_360541 : Nat := 27426789430041350426579

theorem tailTrace_360541 : CollatzResearch.WordTrace tailWord_360541 prefixEnd_360541 27426789430041350426579 := by
  unfold tailWord_360541
  simp only [CollatzResearch.WordTrace]
  refine ⟨13150010586829007345633477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8766673724552671563755651 13150010586829007345633477)
  ·
    refine ⟨2465626985030438877306277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13150010586829007345633477 2465626985030438877306277)
    ·
      refine ⟨462305059693207289494927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2465626985030438877306277 462305059693207289494927)
      ·
        refine ⟨693457589539810934242391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462305059693207289494927 693457589539810934242391)
        ·
          refine ⟨1040186384309716401363587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693457589539810934242391 1040186384309716401363587)
          ·
            refine ⟨1560279576464574602045381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040186384309716401363587 1560279576464574602045381)
            ·
              refine ⟨292552420587107737883509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1560279576464574602045381 292552420587107737883509)
              ·
                refine ⟨27426789430041350426579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292552420587107737883509 27426789430041350426579)
                ·
                  rfl

theorem cell21_360541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 5].length) (baseStart_360541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360541 prefixEnd_360541 := by exact prefixLift 360541
  have htrace : WordTrace (prefixWord ++ tailWord_360541) baseStart_360541 baseEnd_360541 := by
    simpa [prefixWord, tailWord_360541, baseEnd_360541] using wordTrace_append hprefix tailTrace_360541
  have hstable : (prefixWord ++ tailWord_360541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360541).length < 2 ^ (prefixWord ++ tailWord_360541).sum := by decide
  have hdescent : baseEnd_360541 < baseStart_360541 := by decide
  rcases family_descends (prefixWord ++ tailWord_360541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360572 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_360572 : Nat := 118140960795 + 360572 * 2 ^ 59
def prefixEnd_360572 : Nat := 4983230072969 + 3 ^ 40 * 360572 * 2
def baseEnd_360572 : Nat := 82287442912474886263007

theorem tailTrace_360572 : CollatzResearch.WordTrace tailWord_360572 prefixEnd_360572 82287442912474886263007 := by
  unfold tailWord_360572
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575570624858349820005985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8767427499811133093341313 6575570624858349820005985)
  ·
    refine ⟨4931677968643762365004489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6575570624858349820005985 4931677968643762365004489)
    ·
      refine ⟨3698758476482821773753367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4931677968643762365004489 3698758476482821773753367)
      ·
        refine ⟨5548137714724232660630051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3698758476482821773753367 5548137714724232660630051)
        ·
          refine ⟨8322206572086348990945077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548137714724232660630051 8322206572086348990945077)
          ·
            refine ⟨780206866133095217901101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8322206572086348990945077 780206866133095217901101)
            ·
              refine ⟨292577574799910706712913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780206866133095217901101 292577574799910706712913)
              ·
                refine ⟨219433181099933030034685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292577574799910706712913 219433181099933030034685)
                ·
                  refine ⟨82287442912474886263007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219433181099933030034685 82287442912474886263007)
                  ·
                    rfl

theorem cell21_360572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_360572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360572 prefixEnd_360572 := by exact prefixLift 360572
  have htrace : WordTrace (prefixWord ++ tailWord_360572) baseStart_360572 baseEnd_360572 := by
    simpa [prefixWord, tailWord_360572, baseEnd_360572] using wordTrace_append hprefix tailTrace_360572
  have hstable : (prefixWord ++ tailWord_360572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360572).length < 2 ^ (prefixWord ++ tailWord_360572).sum := by decide
  have hdescent : baseEnd_360572 < baseStart_360572 := by decide
  rcases family_descends (prefixWord ++ tailWord_360572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360586 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_360586 : Nat := 118140960795 + 360586 * 2 ^ 59
def prefixEnd_360586 : Nat := 4983230072969 + 3 ^ 40 * 360586 * 2
def baseEnd_360586 : Nat := 82290637903213973029645

theorem tailTrace_360586 : CollatzResearch.WordTrace tailWord_360586 prefixEnd_360586 82290637903213973029645 := by
  unfold tailWord_360586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287912967916495007755403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8767767914443986687347741 3287912967916495007755403)
  ·
    refine ⟨4931869451874742511633105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3287912967916495007755403 4931869451874742511633105)
    ·
      refine ⟨3698902088906056883724829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4931869451874742511633105 3698902088906056883724829)
      ·
        refine ⟨1387088283339771331396811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3698902088906056883724829 1387088283339771331396811)
        ·
          refine ⟨2080632425009656997095217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1387088283339771331396811 2080632425009656997095217)
          ·
            refine ⟨1560474318757242747821413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2080632425009656997095217 1560474318757242747821413)
            ·
              refine ⟨292588934766983015216515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1560474318757242747821413 292588934766983015216515)
              ·
                refine ⟨438883402150474522824773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292588934766983015216515 438883402150474522824773)
                ·
                  refine ⟨82290637903213973029645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438883402150474522824773 82290637903213973029645)
                  ·
                    rfl

theorem cell21_360586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_360586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360586 prefixEnd_360586 := by exact prefixLift 360586
  have htrace : WordTrace (prefixWord ++ tailWord_360586) baseStart_360586 baseEnd_360586 := by
    simpa [prefixWord, tailWord_360586, baseEnd_360586] using wordTrace_append hprefix tailTrace_360586
  have hstable : (prefixWord ++ tailWord_360586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360586).length < 2 ^ (prefixWord ++ tailWord_360586).sum := by decide
  have hdescent : baseEnd_360586 < baseStart_360586 := by decide
  rcases family_descends (prefixWord ++ tailWord_360586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360597 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_360597 : Nat := 118140960795 + 360597 * 2 ^ 59
def prefixEnd_360597 : Nat := 4983230072969 + 3 ^ 40 * 360597 * 2
def baseEnd_360597 : Nat := 82293148253080398346289

theorem tailTrace_360597 : CollatzResearch.WordTrace tailWord_360597 prefixEnd_360597 82293148253080398346289 := by
  unfold tailWord_360597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152053074626128909672045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8768035383084085939781363 13152053074626128909672045)
  ·
    refine ⟨4932019902984798341127017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13152053074626128909672045 4932019902984798341127017)
    ·
      refine ⟨3699014927238598755845263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4932019902984798341127017 3699014927238598755845263)
      ·
        refine ⟨5548522390857898133767895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699014927238598755845263 5548522390857898133767895)
        ·
          refine ⟨8322783586286847200651843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548522390857898133767895 8322783586286847200651843)
          ·
            refine ⟨12484175379430270800977765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8322783586286847200651843 12484175379430270800977765)
            ·
              refine ⟨2340782883643175775183331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12484175379430270800977765 2340782883643175775183331)
              ·
                refine ⟨3511174325464763662774997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340782883643175775183331 3511174325464763662774997)
                ·
                  refine ⟨82293148253080398346289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3511174325464763662774997 82293148253080398346289)
                  ·
                    rfl

theorem cell21_360597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_360597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360597 prefixEnd_360597 := by exact prefixLift 360597
  have htrace : WordTrace (prefixWord ++ tailWord_360597) baseStart_360597 baseEnd_360597 := by
    simpa [prefixWord, tailWord_360597, baseEnd_360597] using wordTrace_append hprefix tailTrace_360597
  have hstable : (prefixWord ++ tailWord_360597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360597).length < 2 ^ (prefixWord ++ tailWord_360597).sum := by decide
  have hdescent : baseEnd_360597 < baseStart_360597 := by decide
  rcases family_descends (prefixWord ++ tailWord_360597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360631 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 3]
def baseStart_360631 : Nat := 118140960795 + 360631 * 2 ^ 59
def prefixEnd_360631 : Nat := 4983230072969 + 3 ^ 40 * 360631 * 2
def baseEnd_360631 : Nat := 82300907516303894779553

theorem tailTrace_360631 : CollatzResearch.WordTrace tailWord_360631 prefixEnd_360631 82300907516303894779553 := by
  unfold tailWord_360631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13153293156502952716409747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8768862104335301810939831 13153293156502952716409747)
  ·
    refine ⟨19729939734754429074614621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13153293156502952716409747 19729939734754429074614621)
    ·
      refine ⟨7398727400532910902980483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19729939734754429074614621 7398727400532910902980483)
      ·
        refine ⟨11098091100799366354470725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7398727400532910902980483 11098091100799366354470725)
        ·
          refine ⟨2080892081399881191463261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11098091100799366354470725 2080892081399881191463261)
          ·
            refine ⟨780334530524955446798723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2080892081399881191463261 780334530524955446798723)
            ·
              refine ⟨1170501795787433170198085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 780334530524955446798723 1170501795787433170198085)
              ·
                refine ⟨219469086710143719412141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1170501795787433170198085 219469086710143719412141)
                ·
                  refine ⟨82300907516303894779553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219469086710143719412141 82300907516303894779553)
                  ·
                    rfl

theorem cell21_360631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 3].length) (baseStart_360631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360631 prefixEnd_360631 := by exact prefixLift 360631
  have htrace : WordTrace (prefixWord ++ tailWord_360631) baseStart_360631 baseEnd_360631 := by
    simpa [prefixWord, tailWord_360631, baseEnd_360631] using wordTrace_append hprefix tailTrace_360631
  have hstable : (prefixWord ++ tailWord_360631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360631).length < 2 ^ (prefixWord ++ tailWord_360631).sum := by decide
  have hdescent : baseEnd_360631 < baseStart_360631 := by decide
  rcases family_descends (prefixWord ++ tailWord_360631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360673 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_360673 : Nat := 118140960795 + 360673 * 2 ^ 59
def prefixEnd_360673 : Nat := 4983230072969 + 3 ^ 40 * 360673 * 2
def baseEnd_360673 : Nat := 82310492488521155079467

theorem tailTrace_360673 : CollatzResearch.WordTrace tailWord_360673 prefixEnd_360673 82310492488521155079467 := by
  unfold tailWord_360673
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154825022350793889438673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8769883348233862592959115 13154825022350793889438673)
  ·
    refine ⟨9866118766763095417079005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13154825022350793889438673 9866118766763095417079005)
    ·
      refine ⟨3699794537536160781404627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9866118766763095417079005 3699794537536160781404627)
      ·
        refine ⟨5549691806304241172106941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699794537536160781404627 5549691806304241172106941)
        ·
          refine ⟨2081134427364090439540103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5549691806304241172106941 2081134427364090439540103)
          ·
            refine ⟨3121701641046135659310155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081134427364090439540103 3121701641046135659310155)
            ·
              refine ⟨4682552461569203488965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3121701641046135659310155 4682552461569203488965233)
              ·
                refine ⟨3511914346176902616723925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4682552461569203488965233 3511914346176902616723925)
                ·
                  refine ⟨82310492488521155079467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3511914346176902616723925 82310492488521155079467)
                  ·
                    rfl

theorem cell21_360673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_360673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360673 prefixEnd_360673 := by exact prefixLift 360673
  have htrace : WordTrace (prefixWord ++ tailWord_360673) baseStart_360673 baseEnd_360673 := by
    simpa [prefixWord, tailWord_360673, baseEnd_360673] using wordTrace_append hprefix tailTrace_360673
  have hstable : (prefixWord ++ tailWord_360673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360673).length < 2 ^ (prefixWord ++ tailWord_360673).sum := by decide
  have hdescent : baseEnd_360673 < baseStart_360673 := by decide
  rcases family_descends (prefixWord ++ tailWord_360673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360690 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_360690 : Nat := 118140960795 + 360690 * 2 ^ 59
def prefixEnd_360690 : Nat := 4983230072969 + 3 ^ 40 * 360690 * 2
def baseEnd_360690 : Nat := 82314372120132903296099

theorem tailTrace_360690 : CollatzResearch.WordTrace tailWord_360690 prefixEnd_360690 82314372120132903296099 := by
  unfold tailWord_360690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288861265822301448201881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8770296708859470528538349 3288861265822301448201881)
  ·
    refine ⟨2466645949366726086151411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3288861265822301448201881 2466645949366726086151411)
    ·
      refine ⟨3699968924050089129227117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2466645949366726086151411 3699968924050089129227117)
      ·
        refine ⟨1387488346518783423460169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3699968924050089129227117 1387488346518783423460169)
        ·
          refine ⟨1040616259889087567595127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1387488346518783423460169 1040616259889087567595127)
          ·
            refine ⟨1560924389833631351392691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040616259889087567595127 1560924389833631351392691)
            ·
              refine ⟨2341386584750447027089037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560924389833631351392691 2341386584750447027089037)
              ·
                refine ⟨878019969281417635158389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2341386584750447027089037 878019969281417635158389)
                ·
                  refine ⟨82314372120132903296099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 878019969281417635158389 82314372120132903296099)
                  ·
                    rfl

theorem cell21_360690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_360690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360690 prefixEnd_360690 := by exact prefixLift 360690
  have htrace : WordTrace (prefixWord ++ tailWord_360690) baseStart_360690 baseEnd_360690 := by
    simpa [prefixWord, tailWord_360690, baseEnd_360690] using wordTrace_append hprefix tailTrace_360690
  have hstable : (prefixWord ++ tailWord_360690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360690).length < 2 ^ (prefixWord ++ tailWord_360690).sum := by decide
  have hdescent : baseEnd_360690 < baseStart_360690 := by decide
  rcases family_descends (prefixWord ++ tailWord_360690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360704 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_360704 : Nat := 118140960795 + 360704 * 2 ^ 59
def prefixEnd_360704 : Nat := 4983230072969 + 3 ^ 40 * 360704 * 2
def baseEnd_360704 : Nat := 82317567110871990062737

theorem tailTrace_360704 : CollatzResearch.WordTrace tailWord_360704 prefixEnd_360704 82317567110871990062737 := by
  unfold tailWord_360704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577977842619243091908583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8770637123492324122544777 6577977842619243091908583)
  ·
    refine ⟨9866966763928864637862875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6577977842619243091908583 9866966763928864637862875)
    ·
      refine ⟨14800450145893296956794313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9866966763928864637862875 14800450145893296956794313)
      ·
        refine ⟨11100337609419972717595735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14800450145893296956794313 11100337609419972717595735)
        ·
          refine ⟨16650506414129959076393603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11100337609419972717595735 16650506414129959076393603)
          ·
            refine ⟨24975759621194938614590405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16650506414129959076393603 24975759621194938614590405)
            ·
              refine ⟨4682954928974050990235701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24975759621194938614590405 4682954928974050990235701)
              ·
                refine ⟨439027024591317280334597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4682954928974050990235701 439027024591317280334597)
                ·
                  refine ⟨82317567110871990062737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439027024591317280334597 82317567110871990062737)
                  ·
                    rfl

theorem cell21_360704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_360704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360704 prefixEnd_360704 := by exact prefixLift 360704
  have htrace : WordTrace (prefixWord ++ tailWord_360704) baseStart_360704 baseEnd_360704 := by
    simpa [prefixWord, tailWord_360704, baseEnd_360704] using wordTrace_append hprefix tailTrace_360704
  have hstable : (prefixWord ++ tailWord_360704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360704).length < 2 ^ (prefixWord ++ tailWord_360704).sum := by decide
  have hdescent : baseEnd_360704 < baseStart_360704 := by decide
  rcases family_descends (prefixWord ++ tailWord_360704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360735 : List Nat := [1, 1, 2, 4, 3, 3, 7]
def baseStart_360735 : Nat := 118140960795 + 360735 * 2 ^ 59
def prefixEnd_360735 : Nat := 4983230072969 + 3 ^ 40 * 360735 * 2
def baseEnd_360735 : Nat := 9147182414802536116223

theorem tailTrace_360735 : CollatzResearch.WordTrace tailWord_360735 prefixEnd_360735 9147182414802536116223 := by
  unfold tailWord_360735
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157086348126178478195659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8771390898750785652130439 13157086348126178478195659)
  ·
    refine ⟨19735629522189267717293489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13157086348126178478195659 19735629522189267717293489)
    ·
      refine ⟨14801722141641950787970117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19735629522189267717293489 14801722141641950787970117)
      ·
        refine ⟨2775322901557865772744397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14801722141641950787970117 2775322901557865772744397)
        ·
          refine ⟨1040746088084199664779149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2775322901557865772744397 1040746088084199664779149)
          ·
            refine ⟨390279783031574874292181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1040746088084199664779149 390279783031574874292181)
            ·
              refine ⟨9147182414802536116223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 390279783031574874292181 9147182414802536116223)
              ·
                rfl

theorem cell21_360735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 7].length) (baseStart_360735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360735 prefixEnd_360735 := by exact prefixLift 360735
  have htrace : WordTrace (prefixWord ++ tailWord_360735) baseStart_360735 baseEnd_360735 := by
    simpa [prefixWord, tailWord_360735, baseEnd_360735] using wordTrace_append hprefix tailTrace_360735
  have hstable : (prefixWord ++ tailWord_360735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360735).length < 2 ^ (prefixWord ++ tailWord_360735).sum := by decide
  have hdescent : baseEnd_360735 < baseStart_360735 := by decide
  rcases family_descends (prefixWord ++ tailWord_360735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360887 : List Nat := [1, 1, 3, 1, 3, 3, 4, 5]
def baseStart_360887 : Nat := 118140960795 + 360887 * 2 ^ 59
def prefixEnd_360887 : Nat := 4983230072969 + 3 ^ 40 * 360887 * 2
def baseEnd_360887 : Nat := 27453110068034779504121

theorem tailTrace_360887 : CollatzResearch.WordTrace tailWord_360887 prefixEnd_360887 27453110068034779504121 := by
  unfold tailWord_360887
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162630243575508437728915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8775086829050338958485943 13162630243575508437728915)
  ·
    refine ⟨19743945365363262656593373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13162630243575508437728915 19743945365363262656593373)
    ·
      refine ⟨7403979512011223496222515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19743945365363262656593373 7403979512011223496222515)
      ·
        refine ⟨11105969268016835244333773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403979512011223496222515 11105969268016835244333773)
        ·
          refine ⟨4164738475506313216625165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11105969268016835244333773 4164738475506313216625165)
          ·
            refine ⟨1561776928314867456234437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4164738475506313216625165 1561776928314867456234437)
            ·
              refine ⟨292833174059037648043957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1561776928314867456234437 292833174059037648043957)
              ·
                refine ⟨27453110068034779504121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292833174059037648043957 27453110068034779504121)
                ·
                  rfl

theorem cell21_360887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 5].length) (baseStart_360887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360887 prefixEnd_360887 := by exact prefixLift 360887
  have htrace : WordTrace (prefixWord ++ tailWord_360887) baseStart_360887 baseEnd_360887 := by
    simpa [prefixWord, tailWord_360887, baseEnd_360887] using wordTrace_append hprefix tailTrace_360887
  have hstable : (prefixWord ++ tailWord_360887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360887).length < 2 ^ (prefixWord ++ tailWord_360887).sum := by decide
  have hdescent : baseEnd_360887 < baseStart_360887 := by decide
  rcases family_descends (prefixWord ++ tailWord_360887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360980 : List Nat := [2, 4, 3, 1, 1, 1, 3, 6]
def baseStart_360980 : Nat := 118140960795 + 360980 * 2 ^ 59
def prefixEnd_360980 : Nat := 4983230072969 + 3 ^ 40 * 360980 * 2
def baseEnd_360980 : Nat := 27460184690385614487391

theorem tailTrace_360980 : CollatzResearch.WordTrace tailWord_360980 prefixEnd_360980 27460184690385614487391 := by
  unfold tailWord_360980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583011116119292660432197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8777348154825723547242929 6583011116119292660432197)
  ·
    refine ⟨1234314584272367373831037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6583011116119292660432197 1234314584272367373831037)
    ·
      refine ⟨462867969102137765186639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1234314584272367373831037 462867969102137765186639)
      ·
        refine ⟨694301953653206647779959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462867969102137765186639 694301953653206647779959)
        ·
          refine ⟨1041452930479809971669939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694301953653206647779959 1041452930479809971669939)
          ·
            refine ⟨1562179395719714957504909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041452930479809971669939 1562179395719714957504909)
            ·
              refine ⟨585817273394893109064341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1562179395719714957504909 585817273394893109064341)
              ·
                refine ⟨27460184690385614487391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 585817273394893109064341 27460184690385614487391)
                ·
                  rfl

theorem cell21_360980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_360980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360980 prefixEnd_360980 := by exact prefixLift 360980
  have htrace : WordTrace (prefixWord ++ tailWord_360980) baseStart_360980 baseEnd_360980 := by
    simpa [prefixWord, tailWord_360980, baseEnd_360980] using wordTrace_append hprefix tailTrace_360980
  have hstable : (prefixWord ++ tailWord_360980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360980).length < 2 ^ (prefixWord ++ tailWord_360980).sum := by decide
  have hdescent : baseEnd_360980 < baseStart_360980 := by decide
  rcases family_descends (prefixWord ++ tailWord_360980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360991 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_360991 : Nat := 118140960795 + 360991 * 2 ^ 59
def prefixEnd_360991 : Nat := 4983230072969 + 3 ^ 40 * 360991 * 2
def baseEnd_360991 : Nat := 82383064421023268778817

theorem tailTrace_360991 : CollatzResearch.WordTrace tailWord_360991 prefixEnd_360991 82383064421023268778817 := by
  unfold tailWord_360991
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166423435198734199514827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8777615623465822799676551 13166423435198734199514827)
  ·
    refine ⟨19749635152798101299272241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13166423435198734199514827 19749635152798101299272241)
    ·
      refine ⟨14812226364598575974454181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19749635152798101299272241 14812226364598575974454181)
      ·
        refine ⟨2777292443362232995210159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14812226364598575974454181 2777292443362232995210159)
        ·
          refine ⟨4165938665043349492815239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2777292443362232995210159 4165938665043349492815239)
          ·
            refine ⟨6248907997565024239222859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165938665043349492815239 6248907997565024239222859)
            ·
              refine ⟨9373361996347536358834289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248907997565024239222859 9373361996347536358834289)
              ·
                refine ⟨7030021497260652269125717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9373361996347536358834289 7030021497260652269125717)
                ·
                  refine ⟨82383064421023268778817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7030021497260652269125717 82383064421023268778817)
                  ·
                    rfl

theorem cell21_360991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_360991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_360991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_360991 prefixEnd_360991 := by exact prefixLift 360991
  have htrace : WordTrace (prefixWord ++ tailWord_360991) baseStart_360991 baseEnd_360991 := by
    simpa [prefixWord, tailWord_360991, baseEnd_360991] using wordTrace_append hprefix tailTrace_360991
  have hstable : (prefixWord ++ tailWord_360991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360991).length < 2 ^ (prefixWord ++ tailWord_360991).sum := by decide
  have hdescent : baseEnd_360991 < baseStart_360991 := by decide
  rcases family_descends (prefixWord ++ tailWord_360991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361025 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 4]
def baseStart_361025 : Nat := 118140960795 + 361025 * 2 ^ 59
def prefixEnd_361025 : Nat := 4983230072969 + 3 ^ 40 * 361025 * 2
def baseEnd_361025 : Nat := 82390823684246765212081

theorem tailTrace_361025 : CollatzResearch.WordTrace tailWord_361025 prefixEnd_361025 82390823684246765212081 := by
  unfold tailWord_361025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167663517075558006252529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8778442344717038670835019 13167663517075558006252529)
  ·
    refine ⟨9875747637806668504689397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13167663517075558006252529 9875747637806668504689397)
    ·
      refine ⟨925851341044375172314631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9875747637806668504689397 925851341044375172314631)
      ·
        refine ⟨1388777011566562758471947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925851341044375172314631 1388777011566562758471947)
        ·
          refine ⟨2083165517349844137707921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388777011566562758471947 2083165517349844137707921)
          ·
            refine ⟨1562374138012383103280941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2083165517349844137707921 1562374138012383103280941)
            ·
              refine ⟨585890301754643663730353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1562374138012383103280941 585890301754643663730353)
              ·
                refine ⟨439417726315982747797765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585890301754643663730353 439417726315982747797765)
                ·
                  refine ⟨82390823684246765212081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439417726315982747797765 82390823684246765212081)
                  ·
                    rfl

theorem cell21_361025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_361025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361025 prefixEnd_361025 := by exact prefixLift 361025
  have htrace : WordTrace (prefixWord ++ tailWord_361025) baseStart_361025 baseEnd_361025 := by
    simpa [prefixWord, tailWord_361025, baseEnd_361025] using wordTrace_append hprefix tailTrace_361025
  have hstable : (prefixWord ++ tailWord_361025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361025).length < 2 ^ (prefixWord ++ tailWord_361025).sum := by decide
  have hdescent : baseEnd_361025 < baseStart_361025 := by decide
  rcases family_descends (prefixWord ++ tailWord_361025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361090 : List Nat := [3, 4, 3, 1, 1, 1, 2, 6]
def baseStart_361090 : Nat := 118140960795 + 361090 * 2 ^ 59
def prefixEnd_361090 : Nat := 4983230072969 + 3 ^ 40 * 361090 * 2
def baseEnd_361090 : Nat := 27468552523273698876205

theorem tailTrace_361090 : CollatzResearch.WordTrace tailWord_361090 prefixEnd_361090 27468552523273698876205 := by
  unfold tailWord_361090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292508565460018526842181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8780022841226716071579149 3292508565460018526842181)
  ·
    refine ⟨617345356023753473782909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3292508565460018526842181 617345356023753473782909)
    ·
      refine ⟨231504508508907552668591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 617345356023753473782909 231504508508907552668591)
      ·
        refine ⟨347256762763361329002887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231504508508907552668591 347256762763361329002887)
        ·
          refine ⟨520885144145041993504331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347256762763361329002887 520885144145041993504331)
          ·
            refine ⟨781327716217562990256497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520885144145041993504331 781327716217562990256497)
            ·
              refine ⟨585995787163172242692373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781327716217562990256497 585995787163172242692373)
              ·
                refine ⟨27468552523273698876205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 585995787163172242692373 27468552523273698876205)
                ·
                  rfl

theorem cell21_361090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_361090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361090 prefixEnd_361090 := by exact prefixLift 361090
  have htrace : WordTrace (prefixWord ++ tailWord_361090) baseStart_361090 baseEnd_361090 := by
    simpa [prefixWord, tailWord_361090, baseEnd_361090] using wordTrace_append hprefix tailTrace_361090
  have hstable : (prefixWord ++ tailWord_361090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361090).length < 2 ^ (prefixWord ++ tailWord_361090).sum := by decide
  have hdescent : baseEnd_361090 < baseStart_361090 := by decide
  rcases family_descends (prefixWord ++ tailWord_361090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361146 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_361146 : Nat := 118140960795 + 361146 * 2 ^ 59
def prefixEnd_361146 : Nat := 4983230072969 + 3 ^ 40 * 361146 * 2
def baseEnd_361146 : Nat := 82418437532777443695167

theorem tailTrace_361146 : CollatzResearch.WordTrace tailWord_361146 prefixEnd_361146 82418437532777443695167 := by
  unfold tailWord_361146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293019187409298917851823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8781384499758130447604861 3293019187409298917851823)
  ·
    refine ⟨4939528781113948376777735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3293019187409298917851823 4939528781113948376777735)
    ·
      refine ⟨7409293171670922565166603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4939528781113948376777735 7409293171670922565166603)
      ·
        refine ⟨11113939757506383847749905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409293171670922565166603 11113939757506383847749905)
        ·
          refine ⟨8335454818129787885812429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11113939757506383847749905 8335454818129787885812429)
          ·
            refine ⟨3125795556798670457179661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8335454818129787885812429 3125795556798670457179661)
            ·
              refine ⟨1172173333799501421442373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3125795556798670457179661 1172173333799501421442373)
              ·
                refine ⟨219782500087406516520445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1172173333799501421442373 219782500087406516520445)
                ·
                  refine ⟨82418437532777443695167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219782500087406516520445 82418437532777443695167)
                  ·
                    rfl

theorem cell21_361146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_361146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361146 prefixEnd_361146 := by exact prefixLift 361146
  have htrace : WordTrace (prefixWord ++ tailWord_361146) baseStart_361146 baseEnd_361146 := by
    simpa [prefixWord, tailWord_361146, baseEnd_361146] using wordTrace_append hprefix tailTrace_361146
  have hstable : (prefixWord ++ tailWord_361146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361146).length < 2 ^ (prefixWord ++ tailWord_361146).sum := by decide
  have hdescent : baseEnd_361146 < baseStart_361146 := by decide
  rcases family_descends (prefixWord ++ tailWord_361146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361160 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_361160 : Nat := 118140960795 + 361160 * 2 ^ 59
def prefixEnd_361160 : Nat := 4983230072969 + 3 ^ 40 * 361160 * 2
def baseEnd_361160 : Nat := 82421632523516530461805

theorem tailTrace_361160 : CollatzResearch.WordTrace tailWord_361160 prefixEnd_361160 82421632523516530461805 := by
  unfold tailWord_361160
  simp only [CollatzResearch.WordTrace]
  refine ⟨6586293685793238031208467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8781724914390984041611289 6586293685793238031208467)
  ·
    refine ⟨9879440528689857046812701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6586293685793238031208467 9879440528689857046812701)
    ·
      refine ⟨3704790198258696392554763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9879440528689857046812701 3704790198258696392554763)
      ·
        refine ⟨5557185297388044588832145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704790198258696392554763 5557185297388044588832145)
        ·
          refine ⟨4167888973041033441624109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5557185297388044588832145 4167888973041033441624109)
          ·
            refine ⟨1562958364890387540609041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4167888973041033441624109 1562958364890387540609041)
            ·
              refine ⟨1172218773667790655456781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562958364890387540609041 1172218773667790655456781)
              ·
                refine ⟨439582040125421495796293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172218773667790655456781 439582040125421495796293)
                ·
                  refine ⟨82421632523516530461805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439582040125421495796293 82421632523516530461805)
                  ·
                    rfl

theorem cell21_361160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_361160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361160 prefixEnd_361160 := by exact prefixLift 361160
  have htrace : WordTrace (prefixWord ++ tailWord_361160) baseStart_361160 baseEnd_361160 := by
    simpa [prefixWord, tailWord_361160, baseEnd_361160] using wordTrace_append hprefix tailTrace_361160
  have hstable : (prefixWord ++ tailWord_361160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361160).length < 2 ^ (prefixWord ++ tailWord_361160).sum := by decide
  have hdescent : baseEnd_361160 < baseStart_361160 := by decide
  rcases family_descends (prefixWord ++ tailWord_361160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361180 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_361180 : Nat := 118140960795 + 361180 * 2 ^ 59
def prefixEnd_361180 : Nat := 4983230072969 + 3 ^ 40 * 361180 * 2
def baseEnd_361180 : Nat := 82426196796000940128431

theorem tailTrace_361180 : CollatzResearch.WordTrace tailWord_361180 prefixEnd_361180 82426196796000940128431 := by
  unfold tailWord_361180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6586658415757009739072497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8782211221009346318763329 6586658415757009739072497)
  ·
    refine ⟨4939993811817757304304373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6586658415757009739072497 4939993811817757304304373)
    ·
      refine ⟨463124419857914747278535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4939993811817757304304373 463124419857914747278535)
      ·
        refine ⟨694686629786872120917803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463124419857914747278535 694686629786872120917803)
        ·
          refine ⟨1042029944680308181376705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694686629786872120917803 1042029944680308181376705)
          ·
            refine ⟨781522458510231136032529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042029944680308181376705 781522458510231136032529)
            ·
              refine ⟨586141843882673352024397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781522458510231136032529 586141843882673352024397)
              ·
                refine ⟨219803191456002507009149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586141843882673352024397 219803191456002507009149)
                ·
                  refine ⟨82426196796000940128431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219803191456002507009149 82426196796000940128431)
                  ·
                    rfl

theorem cell21_361180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_361180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361180 prefixEnd_361180 := by exact prefixLift 361180
  have htrace : WordTrace (prefixWord ++ tailWord_361180) baseStart_361180 baseEnd_361180 := by
    simpa [prefixWord, tailWord_361180, baseEnd_361180] using wordTrace_append hprefix tailTrace_361180
  have hstable : (prefixWord ++ tailWord_361180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361180).length < 2 ^ (prefixWord ++ tailWord_361180).sum := by decide
  have hdescent : baseEnd_361180 < baseStart_361180 := by decide
  rcases family_descends (prefixWord ++ tailWord_361180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361250 : List Nat := [3, 3, 1, 1, 2, 2, 9]
def baseStart_361250 : Nat := 118140960795 + 361250 * 2 ^ 59
def prefixEnd_361250 : Nat := 4983230072969 + 3 ^ 40 * 361250 * 2
def baseEnd_361250 : Nat := 9160241305521819329069

theorem tailTrace_361250 : CollatzResearch.WordTrace tailWord_361250 prefixEnd_361250 9160241305521819329069 := by
  unfold tailWord_361250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293967485315105358298301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8783913294173614288795469 3293967485315105358298301)
  ·
    refine ⟨1235237806993164509361863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3293967485315105358298301 1235237806993164509361863)
    ·
      refine ⟨1852856710489746764042795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235237806993164509361863 1852856710489746764042795)
      ·
        refine ⟨2779285065734620146064193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852856710489746764042795 2779285065734620146064193)
        ·
          refine ⟨2084463799300965109548145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2779285065734620146064193 2084463799300965109548145)
          ·
            refine ⟨1563347849475723832161109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084463799300965109548145 1563347849475723832161109)
            ·
              refine ⟨9160241305521819329069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1563347849475723832161109 9160241305521819329069)
              ·
                rfl

theorem cell21_361250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 9].length) (baseStart_361250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361250 prefixEnd_361250 := by exact prefixLift 361250
  have htrace : WordTrace (prefixWord ++ tailWord_361250) baseStart_361250 baseEnd_361250 := by
    simpa [prefixWord, tailWord_361250, baseEnd_361250] using wordTrace_append hprefix tailTrace_361250
  have hstable : (prefixWord ++ tailWord_361250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361250).length < 2 ^ (prefixWord ++ tailWord_361250).sum := by decide
  have hdescent : baseEnd_361250 < baseStart_361250 := by decide
  rcases family_descends (prefixWord ++ tailWord_361250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361270 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_361270 : Nat := 118140960795 + 361270 * 2 ^ 59
def prefixEnd_361270 : Nat := 4983230072969 + 3 ^ 40 * 361270 * 2
def baseEnd_361270 : Nat := 82446736022180783628247

theorem tailTrace_361270 : CollatzResearch.WordTrace tailWord_361270 prefixEnd_361270 82446736022180783628247 := by
  unfold tailWord_361270
  simp only [CollatzResearch.WordTrace]
  refine ⟨823537462574247803057579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8784399600791976565947509 823537462574247803057579)
  ·
    refine ⟨1235306193861371704586369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 823537462574247803057579 1235306193861371704586369)
    ·
      refine ⟨926479645396028778439777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235306193861371704586369 926479645396028778439777)
      ·
        refine ⟨694859734047021583829833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 926479645396028778439777 694859734047021583829833)
        ·
          refine ⟨521144800535266187872375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694859734047021583829833 521144800535266187872375)
          ·
            refine ⟨781717200802899281808563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521144800535266187872375 781717200802899281808563)
            ·
              refine ⟨1172575801204348922712845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781717200802899281808563 1172575801204348922712845)
              ·
                refine ⟨439715925451630846017317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172575801204348922712845 439715925451630846017317)
                ·
                  refine ⟨82446736022180783628247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439715925451630846017317 82446736022180783628247)
                  ·
                    rfl

theorem cell21_361270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_361270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361270 prefixEnd_361270 := by exact prefixLift 361270
  have htrace : WordTrace (prefixWord ++ tailWord_361270) baseStart_361270 baseEnd_361270 := by
    simpa [prefixWord, tailWord_361270, baseEnd_361270] using wordTrace_append hprefix tailTrace_361270
  have hstable : (prefixWord ++ tailWord_361270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361270).length < 2 ^ (prefixWord ++ tailWord_361270).sum := by decide
  have hdescent : baseEnd_361270 < baseStart_361270 := by decide
  rcases family_descends (prefixWord ++ tailWord_361270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361298 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_361298 : Nat := 118140960795 + 361298 * 2 ^ 59
def prefixEnd_361298 : Nat := 4983230072969 + 3 ^ 40 * 361298 * 2
def baseEnd_361298 : Nat := 82453126003658957161523

theorem tailTrace_361298 : CollatzResearch.WordTrace tailWord_361298 prefixEnd_361298 82453126003658957161523 := by
  unfold tailWord_361298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294405161271631407735137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8785080430057683753960365 3294405161271631407735137)
  ·
    refine ⟨2470803870953723555801353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3294405161271631407735137 2470803870953723555801353)
    ·
      refine ⟨1853102903215292666851015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470803870953723555801353 1853102903215292666851015)
      ·
        refine ⟨2779654354822939000276523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853102903215292666851015 2779654354822939000276523)
        ·
          refine ⟨4169481532234408500414785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779654354822939000276523 4169481532234408500414785)
          ·
            refine ⟨3127111149175806375311089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169481532234408500414785 3127111149175806375311089)
            ·
              refine ⟨2345333361881854781483317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3127111149175806375311089 2345333361881854781483317)
              ·
                refine ⟨219875002676423885764061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2345333361881854781483317 219875002676423885764061)
                ·
                  refine ⟨82453126003658957161523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219875002676423885764061 82453126003658957161523)
                  ·
                    rfl

theorem cell21_361298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_361298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361298 prefixEnd_361298 := by exact prefixLift 361298
  have htrace : WordTrace (prefixWord ++ tailWord_361298) baseStart_361298 baseEnd_361298 := by
    simpa [prefixWord, tailWord_361298, baseEnd_361298] using wordTrace_append hprefix tailTrace_361298
  have hstable : (prefixWord ++ tailWord_361298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361298).length < 2 ^ (prefixWord ++ tailWord_361298).sum := by decide
  have hdescent : baseEnd_361298 < baseStart_361298 := by decide
  rcases family_descends (prefixWord ++ tailWord_361298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361309 : List Nat := [1, 4, 16]
def baseStart_361309 : Nat := 118140960795 + 361309 * 2 ^ 59
def prefixEnd_361309 : Nat := 4983230072969 + 3 ^ 40 * 361309 * 2
def baseEnd_361309 : Nat := 113107868797702856623

theorem tailTrace_361309 : CollatzResearch.WordTrace tailWord_361309 prefixEnd_361309 113107868797702856623 := by
  unfold tailWord_361309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13178021848046674509590981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8785347898697783006393987 13178021848046674509590981)
  ·
    refine ⟨2470879096508751470548309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13178021848046674509590981 2470879096508751470548309)
    ·
      refine ⟨113107868797702856623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 2470879096508751470548309 113107868797702856623)
      ·
        rfl

theorem cell21_361309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 16].length) (baseStart_361309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361309 prefixEnd_361309 := by exact prefixLift 361309
  have htrace : WordTrace (prefixWord ++ tailWord_361309) baseStart_361309 baseEnd_361309 := by
    simpa [prefixWord, tailWord_361309, baseEnd_361309] using wordTrace_append hprefix tailTrace_361309
  have hstable : (prefixWord ++ tailWord_361309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361309).length < 2 ^ (prefixWord ++ tailWord_361309).sum := by decide
  have hdescent : baseEnd_361309 < baseStart_361309 := by decide
  rcases family_descends (prefixWord ++ tailWord_361309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361312 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_361312 : Nat := 118140960795 + 361312 * 2 ^ 59
def prefixEnd_361312 : Nat := 4983230072969 + 3 ^ 40 * 361312 * 2
def baseEnd_361312 : Nat := 82456320994398043928161

theorem tailTrace_361312 : CollatzResearch.WordTrace tailWord_361312 prefixEnd_361312 82456320994398043928161 := by
  unfold tailWord_361312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589065633517903010975095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8785420844690537347966793 6589065633517903010975095)
  ·
    refine ⟨9883598450276854516462643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6589065633517903010975095 9883598450276854516462643)
    ·
      refine ⟨14825397675415281774693965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9883598450276854516462643 14825397675415281774693965)
      ·
        refine ⟨5559524128280730665510237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14825397675415281774693965 5559524128280730665510237)
        ·
          refine ⟨2084821548105273999566339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5559524128280730665510237 2084821548105273999566339)
          ·
            refine ⟨3127232322157910999349509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084821548105273999566339 3127232322157910999349509)
            ·
              refine ⟨586356060404608312378033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3127232322157910999349509 586356060404608312378033)
              ·
                refine ⟨439767045303456234283525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586356060404608312378033 439767045303456234283525)
                ·
                  refine ⟨82456320994398043928161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439767045303456234283525 82456320994398043928161)
                  ·
                    rfl

theorem cell21_361312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_361312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361312 prefixEnd_361312 := by exact prefixLift 361312
  have htrace : WordTrace (prefixWord ++ tailWord_361312) baseStart_361312 baseEnd_361312 := by
    simpa [prefixWord, tailWord_361312, baseEnd_361312] using wordTrace_append hprefix tailTrace_361312
  have hstable : (prefixWord ++ tailWord_361312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361312).length < 2 ^ (prefixWord ++ tailWord_361312).sum := by decide
  have hdescent : baseEnd_361312 < baseStart_361312 := by decide
  rcases family_descends (prefixWord ++ tailWord_361312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361315 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 3]
def baseStart_361315 : Nat := 118140960795 + 361315 * 2 ^ 59
def prefixEnd_361315 : Nat := 4983230072969 + 3 ^ 40 * 361315 * 2
def baseEnd_361315 : Nat := 82457005635270705378155

theorem tailTrace_361315 : CollatzResearch.WordTrace tailWord_361315 prefixEnd_361315 82457005635270705378155 := by
  unfold tailWord_361315
  simp only [CollatzResearch.WordTrace]
  refine ⟨13178240686024937534309399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8785493790683291689539599 13178240686024937534309399)
  ·
    refine ⟨19767361029037406301464099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13178240686024937534309399 19767361029037406301464099)
    ·
      refine ⟨29651041543556109452196149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19767361029037406301464099 29651041543556109452196149)
      ·
        refine ⟨2779785144708385261143389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29651041543556109452196149 2779785144708385261143389)
        ·
          refine ⟨1042419429265644472928771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2779785144708385261143389 1042419429265644472928771)
          ·
            refine ⟨1563629143898466709393157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042419429265644472928771 1563629143898466709393157)
            ·
              refine ⟨293180464480962508011217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1563629143898466709393157 293180464480962508011217)
              ·
                refine ⟨219885348360721881008413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293180464480962508011217 219885348360721881008413)
                ·
                  refine ⟨82457005635270705378155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219885348360721881008413 82457005635270705378155)
                  ·
                    rfl

theorem cell21_361315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 3].length) (baseStart_361315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361315 prefixEnd_361315 := by exact prefixLift 361315
  have htrace : WordTrace (prefixWord ++ tailWord_361315) baseStart_361315 baseEnd_361315 := by
    simpa [prefixWord, tailWord_361315, baseEnd_361315] using wordTrace_append hprefix tailTrace_361315
  have hstable : (prefixWord ++ tailWord_361315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361315).length < 2 ^ (prefixWord ++ tailWord_361315).sum := by decide
  have hdescent : baseEnd_361315 < baseStart_361315 := by decide
  rcases family_descends (prefixWord ++ tailWord_361315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361385 : List Nat := [1, 2, 1, 1, 1, 1, 6, 8]
def baseStart_361385 : Nat := 118140960795 + 361385 * 2 ^ 59
def prefixEnd_361385 : Nat := 4983230072969 + 3 ^ 40 * 361385 * 2
def baseEnd_361385 : Nat := 27490993529655379737115

theorem tailTrace_361385 : CollatzResearch.WordTrace tailWord_361385 prefixEnd_361385 27490993529655379737115 := by
  unfold tailWord_361385
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180793795771339489357609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8787195863847559659571739 13180793795771339489357609)
  ·
    refine ⟨9885595346828504617018207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13180793795771339489357609 9885595346828504617018207)
    ·
      refine ⟨14828393020242756925527311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9885595346828504617018207 14828393020242756925527311)
      ·
        refine ⟨22242589530364135388290967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14828393020242756925527311 22242589530364135388290967)
        ·
          refine ⟨33363884295546203082436451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22242589530364135388290967 33363884295546203082436451)
          ·
            refine ⟨50045826443319304623654677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33363884295546203082436451 50045826443319304623654677)
            ·
              refine ⟨2345898114530592404233813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50045826443319304623654677 2345898114530592404233813)
              ·
                refine ⟨27490993529655379737115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2345898114530592404233813 27490993529655379737115)
                ·
                  rfl

theorem cell21_361385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 8].length) (baseStart_361385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361385 prefixEnd_361385 := by exact prefixLift 361385
  have htrace : WordTrace (prefixWord ++ tailWord_361385) baseStart_361385 baseEnd_361385 := by
    simpa [prefixWord, tailWord_361385, baseEnd_361385] using wordTrace_append hprefix tailTrace_361385
  have hstable : (prefixWord ++ tailWord_361385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361385).length < 2 ^ (prefixWord ++ tailWord_361385).sum := by decide
  have hdescent : baseEnd_361385 < baseStart_361385 := by decide
  rcases family_descends (prefixWord ++ tailWord_361385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361433 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 5]
def baseStart_361433 : Nat := 118140960795 + 361433 * 2 ^ 59
def prefixEnd_361433 : Nat := 4983230072969 + 3 ^ 40 * 361433 * 2
def baseEnd_361433 : Nat := 82483934842928722411247

theorem tailTrace_361433 : CollatzResearch.WordTrace tailWord_361433 prefixEnd_361433 82483934842928722411247 := by
  unfold tailWord_361433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182544499597443687104953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8788362999731629124736635 13182544499597443687104953)
  ·
    refine ⟨9886908374698082765328715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13182544499597443687104953 9886908374698082765328715)
    ·
      refine ⟨14830362562047124147993073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9886908374698082765328715 14830362562047124147993073)
      ·
        refine ⟨11122771921535343110994805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14830362562047124147993073 11122771921535343110994805)
        ·
          refine ⟨1042759867643938416655763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11122771921535343110994805 1042759867643938416655763)
          ·
            refine ⟨1564139801465907624983645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042759867643938416655763 1564139801465907624983645)
            ·
              refine ⟨586552425549715359368867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1564139801465907624983645 586552425549715359368867)
              ·
                refine ⟨879828638324573039053301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586552425549715359368867 879828638324573039053301)
                ·
                  refine ⟨82483934842928722411247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 879828638324573039053301 82483934842928722411247)
                  ·
                    rfl

theorem cell21_361433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_361433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361433 prefixEnd_361433 := by exact prefixLift 361433
  have htrace : WordTrace (prefixWord ++ tailWord_361433) baseStart_361433 baseEnd_361433 := by
    simpa [prefixWord, tailWord_361433, baseEnd_361433] using wordTrace_append hprefix tailTrace_361433
  have hstable : (prefixWord ++ tailWord_361433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361433).length < 2 ^ (prefixWord ++ tailWord_361433).sum := by decide
  have hdescent : baseEnd_361433 < baseStart_361433 := by decide
  rcases family_descends (prefixWord ++ tailWord_361433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361495 : List Nat := [1, 1, 3, 5, 1, 3, 1, 6]
def baseStart_361495 : Nat := 118140960795 + 361495 * 2 ^ 59
def prefixEnd_361495 : Nat := 4983230072969 + 3 ^ 40 * 361495 * 2
def baseEnd_361495 : Nat := 27499361362543464125929

theorem tailTrace_361495 : CollatzResearch.WordTrace tailWord_361495 prefixEnd_361495 27499361362543464125929 := by
  unfold tailWord_361495
  simp only [CollatzResearch.WordTrace]
  refine ⟨13184805825372828275861939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8789870550248552183907959 13184805825372828275861939)
  ·
    refine ⟨19777208738059242413792909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13184805825372828275861939 19777208738059242413792909)
    ·
      refine ⟨7416453276772215905172341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19777208738059242413792909 7416453276772215905172341)
      ·
        refine ⟨695292494697395241109907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7416453276772215905172341 695292494697395241109907)
        ·
          refine ⟨1042938742046092861664861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695292494697395241109907 1042938742046092861664861)
          ·
            refine ⟨391102028267284823124323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1042938742046092861664861 391102028267284823124323)
            ·
              refine ⟨586653042400927234686485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391102028267284823124323 586653042400927234686485)
              ·
                refine ⟨27499361362543464125929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 586653042400927234686485 27499361362543464125929)
                ·
                  rfl

theorem cell21_361495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 6].length) (baseStart_361495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361495 prefixEnd_361495 := by exact prefixLift 361495
  have htrace : WordTrace (prefixWord ++ tailWord_361495) baseStart_361495 baseEnd_361495 := by
    simpa [prefixWord, tailWord_361495, baseEnd_361495] using wordTrace_append hprefix tailTrace_361495
  have hstable : (prefixWord ++ tailWord_361495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361495).length < 2 ^ (prefixWord ++ tailWord_361495).sum := by decide
  have hdescent : baseEnd_361495 < baseStart_361495 := by decide
  rcases family_descends (prefixWord ++ tailWord_361495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361568 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_361568 : Nat := 118140960795 + 361568 * 2 ^ 59
def prefixEnd_361568 : Nat := 4983230072969 + 3 ^ 40 * 361568 * 2
def baseEnd_361568 : Nat := 82514743682198487660971

theorem tailTrace_361568 : CollatzResearch.WordTrace tailWord_361568 prefixEnd_361568 82514743682198487660971 := by
  unfold tailWord_361568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6593734177054180871634679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8791645569405574495512905 6593734177054180871634679)
  ·
    refine ⟨9890601265581271307452019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6593734177054180871634679 9890601265581271307452019)
    ·
      refine ⟨14835901898371906961178029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9890601265581271307452019 14835901898371906961178029)
      ·
        refine ⟨5563463211889465110441761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14835901898371906961178029 5563463211889465110441761)
        ·
          refine ⟨4172597408917098832831321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5563463211889465110441761 4172597408917098832831321)
          ·
            refine ⟨3129448056687824124623491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4172597408917098832831321 3129448056687824124623491)
            ·
              refine ⟨4694172085031736186935237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129448056687824124623491 4694172085031736186935237)
              ·
                refine ⟨880157265943450535050357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4694172085031736186935237 880157265943450535050357)
                ·
                  refine ⟨82514743682198487660971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 880157265943450535050357 82514743682198487660971)
                  ·
                    rfl

theorem cell21_361568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_361568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361568 prefixEnd_361568 := by exact prefixLift 361568
  have htrace : WordTrace (prefixWord ++ tailWord_361568) baseStart_361568 baseEnd_361568 := by
    simpa [prefixWord, tailWord_361568, baseEnd_361568] using wordTrace_append hprefix tailTrace_361568
  have hstable : (prefixWord ++ tailWord_361568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361568).length < 2 ^ (prefixWord ++ tailWord_361568).sum := by decide
  have hdescent : baseEnd_361568 < baseStart_361568 := by decide
  rcases family_descends (prefixWord ++ tailWord_361568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361585 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 3]
def baseStart_361585 : Nat := 118140960795 + 361585 * 2 ^ 59
def prefixEnd_361585 : Nat := 4983230072969 + 3 ^ 40 * 361585 * 2
def baseEnd_361585 : Nat := 82518623313810235877603

theorem tailTrace_361585 : CollatzResearch.WordTrace tailWord_361585 prefixEnd_361585 82518623313810235877603 := by
  unfold tailWord_361585
  simp only [CollatzResearch.WordTrace]
  refine ⟨13188088395046773646638209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8792058930031182431092139 13188088395046773646638209)
  ·
    refine ⟨9891066296285080234978657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13188088395046773646638209 9891066296285080234978657)
    ·
      refine ⟨7418299722213810176233993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9891066296285080234978657 7418299722213810176233993)
      ·
        refine ⟨5563724791660357632175495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7418299722213810176233993 5563724791660357632175495)
        ·
          refine ⟨8345587187490536448263243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563724791660357632175495 8345587187490536448263243)
          ·
            refine ⟨12518380781235804672394865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8345587187490536448263243 12518380781235804672394865)
            ·
              refine ⟨9388785585926853504296149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12518380781235804672394865 9388785585926853504296149)
              ·
                refine ⟨220049662170160629006941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9388785585926853504296149 220049662170160629006941)
                ·
                  refine ⟨82518623313810235877603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220049662170160629006941 82518623313810235877603)
                  ·
                    rfl

theorem cell21_361585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_361585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361585 prefixEnd_361585 := by exact prefixLift 361585
  have htrace : WordTrace (prefixWord ++ tailWord_361585) baseStart_361585 baseEnd_361585 := by
    simpa [prefixWord, tailWord_361585, baseEnd_361585] using wordTrace_append hprefix tailTrace_361585
  have hstable : (prefixWord ++ tailWord_361585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361585).length < 2 ^ (prefixWord ++ tailWord_361585).sum := by decide
  have hdescent : baseEnd_361585 < baseStart_361585 := by decide
  rcases family_descends (prefixWord ++ tailWord_361585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361709 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 4]
def baseStart_361709 : Nat := 118140960795 + 361709 * 2 ^ 59
def prefixEnd_361709 : Nat := 4983230072969 + 3 ^ 40 * 361709 * 2
def baseEnd_361709 : Nat := 82546921803213575810683

theorem tailTrace_361709 : CollatzResearch.WordTrace tailWord_361709 prefixEnd_361709 82546921803213575810683 := by
  unfold tailWord_361709
  simp only [CollatzResearch.WordTrace]
  refine ⟨13192611046597542824152181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8795074031065028549434787 13192611046597542824152181)
  ·
    refine ⟨1236807285618519639764267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13192611046597542824152181 1236807285618519639764267)
    ·
      refine ⟨1855210928427779459646401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236807285618519639764267 1855210928427779459646401)
      ·
        refine ⟨1391408196320834594734801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1855210928427779459646401 1391408196320834594734801)
        ·
          refine ⟨1043556147240625946051101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391408196320834594734801 1043556147240625946051101)
          ·
            refine ⟨391333555215234729769163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1043556147240625946051101 391333555215234729769163)
            ·
              refine ⟨587000332822852094653745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391333555215234729769163 587000332822852094653745)
              ·
                refine ⟨440250249617139070990309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587000332822852094653745 440250249617139070990309)
                ·
                  refine ⟨82546921803213575810683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440250249617139070990309 82546921803213575810683)
                  ·
                    rfl

theorem cell21_361709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_361709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361709 prefixEnd_361709 := by exact prefixLift 361709
  have htrace : WordTrace (prefixWord ++ tailWord_361709) baseStart_361709 baseEnd_361709 := by
    simpa [prefixWord, tailWord_361709, baseEnd_361709] using wordTrace_append hprefix tailTrace_361709
  have hstable : (prefixWord ++ tailWord_361709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361709).length < 2 ^ (prefixWord ++ tailWord_361709).sum := by decide
  have hdescent : baseEnd_361709 < baseStart_361709 := by decide
  rcases family_descends (prefixWord ++ tailWord_361709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361754 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_361754 : Nat := 118140960795 + 361754 * 2 ^ 59
def prefixEnd_361754 : Nat := 4983230072969 + 3 ^ 40 * 361754 * 2
def baseEnd_361754 : Nat := 82557191416303497560591

theorem tailTrace_361754 : CollatzResearch.WordTrace tailWord_361754 prefixEnd_361754 82557191416303497560591 := by
  unfold tailWord_361754
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298563082858628877385079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8796168220956343673026877 3298563082858628877385079)
  ·
    refine ⟨4947844624287943316077619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3298563082858628877385079 4947844624287943316077619)
    ·
      refine ⟨7421766936431914974116429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947844624287943316077619 7421766936431914974116429)
      ·
        refine ⟨2783162601161968115293661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7421766936431914974116429 2783162601161968115293661)
        ·
          refine ⟨1043685975435738043235123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2783162601161968115293661 1043685975435738043235123)
          ·
            refine ⟨1565528963153607064852685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043685975435738043235123 1565528963153607064852685)
            ·
              refine ⟨587073361182602649319757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1565528963153607064852685 587073361182602649319757)
              ·
                refine ⟨220152510443475993494909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587073361182602649319757 220152510443475993494909)
                ·
                  refine ⟨82557191416303497560591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220152510443475993494909 82557191416303497560591)
                  ·
                    rfl

theorem cell21_361754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_361754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361754 prefixEnd_361754 := by exact prefixLift 361754
  have htrace : WordTrace (prefixWord ++ tailWord_361754) baseStart_361754 baseEnd_361754 := by
    simpa [prefixWord, tailWord_361754, baseEnd_361754] using wordTrace_append hprefix tailTrace_361754
  have hstable : (prefixWord ++ tailWord_361754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361754).length < 2 ^ (prefixWord ++ tailWord_361754).sum := by decide
  have hdescent : baseEnd_361754 < baseStart_361754 := by decide
  rcases family_descends (prefixWord ++ tailWord_361754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361765 : List Nat := [1, 3, 1, 2, 4, 1, 9]
def baseStart_361765 : Nat := 118140960795 + 361765 * 2 ^ 59
def prefixEnd_361765 : Nat := 4983230072969 + 3 ^ 40 * 361765 * 2
def baseEnd_361765 : Nat := 9173300196241102541915

theorem tailTrace_361765 : CollatzResearch.WordTrace tailWord_361765 prefixEnd_361765 9173300196241102541915 := by
  unfold tailWord_361765
  simp only [CollatzResearch.WordTrace]
  refine ⟨13194653534394664388190749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8796435689596442925460499 13194653534394664388190749)
  ·
    refine ⟨4947995075397999145571531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13194653534394664388190749 4947995075397999145571531)
    ·
      refine ⟨7421992613096998718357297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947995075397999145571531 7421992613096998718357297)
      ·
        refine ⟨5566494459822749038767973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7421992613096998718357297 5566494459822749038767973)
        ·
          refine ⟨1043717711216765444768995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5566494459822749038767973 1043717711216765444768995)
          ·
            refine ⟨1565576566825148167153493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043717711216765444768995 1565576566825148167153493)
            ·
              refine ⟨9173300196241102541915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1565576566825148167153493 9173300196241102541915)
              ·
                rfl

theorem cell21_361765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 9].length) (baseStart_361765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361765 prefixEnd_361765 := by exact prefixLift 361765
  have htrace : WordTrace (prefixWord ++ tailWord_361765) baseStart_361765 baseEnd_361765 := by
    simpa [prefixWord, tailWord_361765, baseEnd_361765] using wordTrace_append hprefix tailTrace_361765
  have hstable : (prefixWord ++ tailWord_361765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361765).length < 2 ^ (prefixWord ++ tailWord_361765).sum := by decide
  have hdescent : baseEnd_361765 < baseStart_361765 := by decide
  rcases family_descends (prefixWord ++ tailWord_361765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361827 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 4]
def baseStart_361827 : Nat := 118140960795 + 361827 * 2 ^ 59
def prefixEnd_361827 : Nat := 4983230072969 + 3 ^ 40 * 361827 * 2
def baseEnd_361827 : Nat := 82573851010871592843775

theorem tailTrace_361827 : CollatzResearch.WordTrace tailWord_361827 prefixEnd_361827 82573851010871592843775 := by
  unfold tailWord_361827
  simp only [CollatzResearch.WordTrace]
  refine ⟨13196914860170048976947735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8797943240113365984631823 13196914860170048976947735)
  ·
    refine ⟨19795372290255073465421603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13196914860170048976947735 19795372290255073465421603)
    ·
      refine ⟨29693058435382610198132405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19795372290255073465421603 29693058435382610198132405)
      ·
        refine ⟨2783724228317119706074913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29693058435382610198132405 2783724228317119706074913)
        ·
          refine ⟨2087793171237839779556185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2783724228317119706074913 2087793171237839779556185)
          ·
            refine ⟨1565844878428379834667139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087793171237839779556185 1565844878428379834667139)
            ·
              refine ⟨2348767317642569752000709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565844878428379834667139 2348767317642569752000709)
              ·
                refine ⟨440393872057981828500133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2348767317642569752000709 440393872057981828500133)
                ·
                  refine ⟨82573851010871592843775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440393872057981828500133 82573851010871592843775)
                  ·
                    rfl

theorem cell21_361827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_361827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361827 prefixEnd_361827 := by exact prefixLift 361827
  have htrace : WordTrace (prefixWord ++ tailWord_361827) baseStart_361827 baseEnd_361827 := by
    simpa [prefixWord, tailWord_361827, baseEnd_361827] using wordTrace_append hprefix tailTrace_361827
  have hstable : (prefixWord ++ tailWord_361827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361827).length < 2 ^ (prefixWord ++ tailWord_361827).sum := by decide
  have hdescent : baseEnd_361827 < baseStart_361827 := by decide
  rcases family_descends (prefixWord ++ tailWord_361827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361841 : List Nat := [1, 2, 2, 2, 1, 2, 5, 6]
def baseStart_361841 : Nat := 118140960795 + 361841 * 2 ^ 59
def prefixEnd_361841 : Nat := 4983230072969 + 3 ^ 40 * 361841 * 2
def baseEnd_361841 : Nat := 27525682000536893203471

theorem tailTrace_361841 : CollatzResearch.WordTrace tailWord_361841 prefixEnd_361841 27525682000536893203471 := by
  unfold tailWord_361841
  simp only [CollatzResearch.WordTrace]
  refine ⟨13197425482119329367957377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8798283654746219578638251 13197425482119329367957377)
  ·
    refine ⟨9898069111589497025968033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13197425482119329367957377 9898069111589497025968033)
    ·
      refine ⟨7423551833692122769476025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9898069111589497025968033 7423551833692122769476025)
      ·
        refine ⟨5567663875269092077107019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7423551833692122769476025 5567663875269092077107019)
        ·
          refine ⟨8351495812903638115660529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567663875269092077107019 8351495812903638115660529)
          ·
            refine ⟨6263621859677728586745397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8351495812903638115660529 6263621859677728586745397)
            ·
              refine ⟨587214549344787055007381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6263621859677728586745397 587214549344787055007381)
              ·
                refine ⟨27525682000536893203471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 587214549344787055007381 27525682000536893203471)
                ·
                  rfl

theorem cell21_361841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 6].length) (baseStart_361841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361841 prefixEnd_361841 := by exact prefixLift 361841
  have htrace : WordTrace (prefixWord ++ tailWord_361841) baseStart_361841 baseEnd_361841 := by
    simpa [prefixWord, tailWord_361841, baseEnd_361841] using wordTrace_append hprefix tailTrace_361841
  have hstable : (prefixWord ++ tailWord_361841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361841).length < 2 ^ (prefixWord ++ tailWord_361841).sum := by decide
  have hdescent : baseEnd_361841 < baseStart_361841 := by decide
  rcases family_descends (prefixWord ++ tailWord_361841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361917 : List Nat := [1, 4, 1, 2, 2, 1, 3, 7]
def baseStart_361917 : Nat := 118140960795 + 361917 * 2 ^ 59
def prefixEnd_361917 : Nat := 4983230072969 + 3 ^ 40 * 361917 * 2
def baseEnd_361917 : Nat := 27531463412350478781197

theorem tailTrace_361917 : CollatzResearch.WordTrace tailWord_361917 prefixEnd_361917 27531463412350478781197 := by
  unfold tailWord_361917
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200197429843994347724005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8800131619895996231816003 13200197429843994347724005)
  ·
    refine ⟨2475037018095748940198251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13200197429843994347724005 2475037018095748940198251)
    ·
      refine ⟨3712555527143623410297377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475037018095748940198251 3712555527143623410297377)
      ·
        refine ⟨2784416645357717557723033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3712555527143623410297377 2784416645357717557723033)
        ·
          refine ⟨2088312484018288168292275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2784416645357717557723033 2088312484018288168292275)
          ·
            refine ⟨3132468726027432252438413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088312484018288168292275 3132468726027432252438413)
            ·
              refine ⟨1174675772260287094664405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3132468726027432252438413 1174675772260287094664405)
              ·
                refine ⟨27531463412350478781197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1174675772260287094664405 27531463412350478781197)
                ·
                  rfl

theorem cell21_361917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 7].length) (baseStart_361917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361917 prefixEnd_361917 := by exact prefixLift 361917
  have htrace : WordTrace (prefixWord ++ tailWord_361917) baseStart_361917 baseEnd_361917 := by
    simpa [prefixWord, tailWord_361917, baseEnd_361917] using wordTrace_append hprefix tailTrace_361917
  have hstable : (prefixWord ++ tailWord_361917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361917).length < 2 ^ (prefixWord ++ tailWord_361917).sum := by decide
  have hdescent : baseEnd_361917 < baseStart_361917 := by decide
  rcases family_descends (prefixWord ++ tailWord_361917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361931 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 7]
def baseStart_361931 : Nat := 118140960795 + 361931 * 2 ^ 59
def prefixEnd_361931 : Nat := 4983230072969 + 3 ^ 40 * 361931 * 2
def baseEnd_361931 : Nat := 82597585227790523110229

theorem tailTrace_361931 : CollatzResearch.WordTrace tailWord_361931 prefixEnd_361931 82597585227790523110229 := by
  unfold tailWord_361931
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200708051793274738733647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8800472034528849825822431 13200708051793274738733647)
  ·
    refine ⟨19801062077689912108100471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13200708051793274738733647 19801062077689912108100471)
    ·
      refine ⟨29701593116534868162150707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19801062077689912108100471 29701593116534868162150707)
      ·
        refine ⟨44552389674802302243226061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29701593116534868162150707 44552389674802302243226061)
        ·
          refine ⟨16707146128050863341209773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44552389674802302243226061 16707146128050863341209773)
          ·
            refine ⟨6265179798019073752953665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16707146128050863341209773 6265179798019073752953665)
            ·
              refine ⟨4698884848514305314715249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6265179798019073752953665 4698884848514305314715249)
              ·
                refine ⟨3524163636385728986036437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698884848514305314715249 3524163636385728986036437)
                ·
                  refine ⟨82597585227790523110229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3524163636385728986036437 82597585227790523110229)
                  ·
                    rfl

theorem cell21_361931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 7].length) (baseStart_361931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361931 prefixEnd_361931 := by exact prefixLift 361931
  have htrace : WordTrace (prefixWord ++ tailWord_361931) baseStart_361931 baseEnd_361931 := by
    simpa [prefixWord, tailWord_361931, baseEnd_361931] using wordTrace_append hprefix tailTrace_361931
  have hstable : (prefixWord ++ tailWord_361931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361931).length < 2 ^ (prefixWord ++ tailWord_361931).sum := by decide
  have hdescent : baseEnd_361931 < baseStart_361931 := by decide
  rcases family_descends (prefixWord ++ tailWord_361931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361996 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_361996 : Nat := 118140960795 + 361996 * 2 ^ 59
def prefixEnd_361996 : Nat := 4983230072969 + 3 ^ 40 * 361996 * 2
def baseEnd_361996 : Nat := 82612419113364854526763

theorem tailTrace_361996 : CollatzResearch.WordTrace tailWord_361996 prefixEnd_361996 82612419113364854526763 := by
  unfold tailWord_361996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6601539398278895419924921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8802052531038527226566561 6601539398278895419924921)
  ·
    refine ⟨4951154548709171564943691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6601539398278895419924921 4951154548709171564943691)
    ·
      refine ⟨7426731823063757347415537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951154548709171564943691 7426731823063757347415537)
      ·
        refine ⟨5570048867297818010561653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7426731823063757347415537 5570048867297818010561653)
        ·
          refine ⟨522192081309170438490155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5570048867297818010561653 522192081309170438490155)
          ·
            refine ⟨783288121963755657735233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522192081309170438490155 783288121963755657735233)
            ·
              refine ⟨587466091472816743301425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783288121963755657735233 587466091472816743301425)
              ·
                refine ⟨440599568604612557476069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 587466091472816743301425 440599568604612557476069)
                ·
                  refine ⟨82612419113364854526763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440599568604612557476069 82612419113364854526763)
                  ·
                    rfl

theorem cell21_361996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_361996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_361996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_361996 prefixEnd_361996 := by exact prefixLift 361996
  have htrace : WordTrace (prefixWord ++ tailWord_361996) baseStart_361996 baseEnd_361996 := by
    simpa [prefixWord, tailWord_361996, baseEnd_361996] using wordTrace_append hprefix tailTrace_361996
  have hstable : (prefixWord ++ tailWord_361996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361996).length < 2 ^ (prefixWord ++ tailWord_361996).sum := by decide
  have hdescent : baseEnd_361996 < baseStart_361996 := by decide
  rcases family_descends (prefixWord ++ tailWord_361996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362041 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 3]
def baseStart_362041 : Nat := 118140960795 + 362041 * 2 ^ 59
def prefixEnd_362041 : Nat := 4983230072969 + 3 ^ 40 * 362041 * 2
def baseEnd_362041 : Nat := 82622688726454776276671

theorem tailTrace_362041 : CollatzResearch.WordTrace tailWord_362041 prefixEnd_362041 82622688726454776276671 := by
  unfold tailWord_362041
  simp only [CollatzResearch.WordTrace]
  refine ⟨13204720081394763525237977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8803146720929842350158651 13204720081394763525237977)
  ·
    refine ⟨9903540061046072643928483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13204720081394763525237977 9903540061046072643928483)
    ·
      refine ⟨14855310091569108965892725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9903540061046072643928483 14855310091569108965892725)
      ·
        refine ⟨1392685321084603965552443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14855310091569108965892725 1392685321084603965552443)
        ·
          refine ⟨2089027981626905948328665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392685321084603965552443 2089027981626905948328665)
          ·
            refine ⟨1566770986220179461246499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2089027981626905948328665 1566770986220179461246499)
            ·
              refine ⟨2350156479330269191869749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566770986220179461246499 2350156479330269191869749)
              ·
                refine ⟨220327169937212736737789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2350156479330269191869749 220327169937212736737789)
                ·
                  refine ⟨82622688726454776276671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220327169937212736737789 82622688726454776276671)
                  ·
                    rfl

theorem cell21_362041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_362041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362041 prefixEnd_362041 := by exact prefixLift 362041
  have htrace : WordTrace (prefixWord ++ tailWord_362041) baseStart_362041 baseEnd_362041 := by
    simpa [prefixWord, tailWord_362041, baseEnd_362041] using wordTrace_append hprefix tailTrace_362041
  have hstable : (prefixWord ++ tailWord_362041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362041).length < 2 ^ (prefixWord ++ tailWord_362041).sum := by decide
  have hdescent : baseEnd_362041 < baseStart_362041 := by decide
  rcases family_descends (prefixWord ++ tailWord_362041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362055 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 6]
def baseStart_362055 : Nat := 118140960795 + 362055 * 2 ^ 59
def prefixEnd_362055 : Nat := 4983230072969 + 3 ^ 40 * 362055 * 2
def baseEnd_362055 : Nat := 82625883717193863043309

theorem tailTrace_362055 : CollatzResearch.WordTrace tailWord_362055 prefixEnd_362055 82625883717193863043309 := by
  unfold tailWord_362055
  simp only [CollatzResearch.WordTrace]
  refine ⟨13205230703344043916247619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8803487135562695944165079 13205230703344043916247619)
  ·
    refine ⟨19807846055016065874371429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13205230703344043916247619 19807846055016065874371429)
    ·
      refine ⟨3713971135315512351444643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19807846055016065874371429 3713971135315512351444643)
      ·
        refine ⟨5570956702973268527166965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3713971135315512351444643 5570956702973268527166965)
        ·
          refine ⟨522277190903743924421903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5570956702973268527166965 522277190903743924421903)
          ·
            refine ⟨783415786355615886632855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522277190903743924421903 783415786355615886632855)
            ·
              refine ⟨1175123679533423829949283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783415786355615886632855 1175123679533423829949283)
              ·
                refine ⟨1762685519300135744923925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175123679533423829949283 1762685519300135744923925)
                ·
                  refine ⟨82625883717193863043309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1762685519300135744923925 82625883717193863043309)
                  ·
                    rfl

theorem cell21_362055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_362055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362055 prefixEnd_362055 := by exact prefixLift 362055
  have htrace : WordTrace (prefixWord ++ tailWord_362055) baseStart_362055 baseEnd_362055 := by
    simpa [prefixWord, tailWord_362055, baseEnd_362055] using wordTrace_append hprefix tailTrace_362055
  have hstable : (prefixWord ++ tailWord_362055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362055).length < 2 ^ (prefixWord ++ tailWord_362055).sum := by decide
  have hdescent : baseEnd_362055 < baseStart_362055 := by decide
  rcases family_descends (prefixWord ++ tailWord_362055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362145 : List Nat := [1, 2, 3, 3, 2, 1, 2, 7]
def baseStart_362145 : Nat := 118140960795 + 362145 * 2 ^ 59
def prefixEnd_362145 : Nat := 4983230072969 + 3 ^ 40 * 362145 * 2
def baseEnd_362145 : Nat := 27548807647791235514375

theorem tailTrace_362145 : CollatzResearch.WordTrace tailWord_362145 prefixEnd_362145 27548807647791235514375 := by
  unfold tailWord_362145
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208513273017989287023889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8805675515345326191349259 13208513273017989287023889)
  ·
    refine ⟨9906384954763491965267917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13208513273017989287023889 9906384954763491965267917)
    ·
      refine ⟨3714894358036309486975469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9906384954763491965267917 3714894358036309486975469)
      ·
        refine ⟨1393085384263616057615801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3714894358036309486975469 1393085384263616057615801)
        ·
          refine ⟨1044814038197712043211851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393085384263616057615801 1044814038197712043211851)
          ·
            refine ⟨1567221057296568064817777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044814038197712043211851 1567221057296568064817777)
            ·
              refine ⟨1175415792972426048613333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567221057296568064817777 1175415792972426048613333)
              ·
                refine ⟨27548807647791235514375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1175415792972426048613333 27548807647791235514375)
                ·
                  rfl

theorem cell21_362145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_362145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362145 prefixEnd_362145 := by exact prefixLift 362145
  have htrace : WordTrace (prefixWord ++ tailWord_362145) baseStart_362145 baseEnd_362145 := by
    simpa [prefixWord, tailWord_362145, baseEnd_362145] using wordTrace_append hprefix tailTrace_362145
  have hstable : (prefixWord ++ tailWord_362145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362145).length < 2 ^ (prefixWord ++ tailWord_362145).sum := by decide
  have hdescent : baseEnd_362145 < baseStart_362145 := by decide
  rcases family_descends (prefixWord ++ tailWord_362145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362221 : List Nat := [1, 5, 1, 2, 1, 3, 8]
def baseStart_362221 : Nat := 118140960795 + 362221 * 2 ^ 59
def prefixEnd_362221 : Nat := 4983230072969 + 3 ^ 40 * 362221 * 2
def baseEnd_362221 : Nat := 9184863019868273697367

theorem tailTrace_362221 : CollatzResearch.WordTrace tailWord_362221 prefixEnd_362221 9184863019868273697367 := by
  unfold tailWord_362221
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211285220742654266790517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8807523480495102844527011 13211285220742654266790517)
  ·
    refine ⟨1238557989444623837511611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13211285220742654266790517 1238557989444623837511611)
    ·
      refine ⟨1857836984166935756267417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238557989444623837511611 1857836984166935756267417)
      ·
        refine ⟨1393377738125201817200563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857836984166935756267417 1393377738125201817200563)
        ·
          refine ⟨2090066607187802725800845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393377738125201817200563 2090066607187802725800845)
          ·
            refine ⟨783774977695426022175317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2090066607187802725800845 783774977695426022175317)
            ·
              refine ⟨9184863019868273697367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 783774977695426022175317 9184863019868273697367)
              ·
                rfl

theorem cell21_362221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 8].length) (baseStart_362221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362221 prefixEnd_362221 := by exact prefixLift 362221
  have htrace : WordTrace (prefixWord ++ tailWord_362221) baseStart_362221 baseEnd_362221 := by
    simpa [prefixWord, tailWord_362221, baseEnd_362221] using wordTrace_append hprefix tailTrace_362221
  have hstable : (prefixWord ++ tailWord_362221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362221).length < 2 ^ (prefixWord ++ tailWord_362221).sum := by decide
  have hdescent : baseEnd_362221 < baseStart_362221 := by decide
  rcases family_descends (prefixWord ++ tailWord_362221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362266 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_362266 : Nat := 118140960795 + 362266 * 2 ^ 59
def prefixEnd_362266 : Nat := 4983230072969 + 3 ^ 40 * 362266 * 2
def baseEnd_362266 : Nat := 82674036791904385026211

theorem tailTrace_362266 : CollatzResearch.WordTrace tailWord_362266 prefixEnd_362266 82674036791904385026211 := by
  unfold tailWord_362266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303231626394906738044663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8808617670386417968119101 3303231626394906738044663)
  ·
    refine ⟨4954847439592360107066995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3303231626394906738044663 4954847439592360107066995)
    ·
      refine ⟨7432271159388540160600493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4954847439592360107066995 7432271159388540160600493)
      ·
        refine ⟨2787101684770702560225185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7432271159388540160600493 2787101684770702560225185)
        ·
          refine ⟨2090326263578026920168889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2787101684770702560225185 2090326263578026920168889)
          ·
            refine ⟨1567744697683520190126667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2090326263578026920168889 1567744697683520190126667)
            ·
              refine ⟨2351617046525280285190001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567744697683520190126667 2351617046525280285190001)
              ·
                refine ⟨1763712784893960213892501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2351617046525280285190001 1763712784893960213892501)
                ·
                  refine ⟨82674036791904385026211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1763712784893960213892501 82674036791904385026211)
                  ·
                    rfl

theorem cell21_362266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_362266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362266 prefixEnd_362266 := by exact prefixLift 362266
  have htrace : WordTrace (prefixWord ++ tailWord_362266) baseStart_362266 baseEnd_362266 := by
    simpa [prefixWord, tailWord_362266, baseEnd_362266] using wordTrace_append hprefix tailTrace_362266
  have hstable : (prefixWord ++ tailWord_362266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362266).length < 2 ^ (prefixWord ++ tailWord_362266).sum := by decide
  have hdescent : baseEnd_362266 < baseStart_362266 := by decide
  rcases family_descends (prefixWord ++ tailWord_362266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362286 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_362286 : Nat := 118140960795 + 362286 * 2 ^ 59
def prefixEnd_362286 : Nat := 4983230072969 + 3 ^ 40 * 362286 * 2
def baseEnd_362286 : Nat := 82678601064388794692837

theorem tailTrace_362286 : CollatzResearch.WordTrace tailWord_362286 prefixEnd_362286 82678601064388794692837 := by
  unfold tailWord_362286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651706995688396295988339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8809103977004780245271141 1651706995688396295988339)
  ·
    refine ⟨2477560493532594443982509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1651706995688396295988339 2477560493532594443982509)
    ·
      refine ⟨929085185074722916493441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2477560493532594443982509 929085185074722916493441)
      ·
        refine ⟨696813888806042187370081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 929085185074722916493441 696813888806042187370081)
        ·
          refine ⟨522610416604531640527561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 696813888806042187370081 522610416604531640527561)
          ·
            refine ⟨391957812453398730395671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522610416604531640527561 391957812453398730395671)
            ·
              refine ⟨587936718680098095593507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391957812453398730395671 587936718680098095593507)
              ·
                refine ⟨881905078020147143390261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587936718680098095593507 881905078020147143390261)
                ·
                  refine ⟨82678601064388794692837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 881905078020147143390261 82678601064388794692837)
                  ·
                    rfl

theorem cell21_362286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_362286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362286 prefixEnd_362286 := by exact prefixLift 362286
  have htrace : WordTrace (prefixWord ++ tailWord_362286) baseStart_362286 baseEnd_362286 := by
    simpa [prefixWord, tailWord_362286, baseEnd_362286] using wordTrace_append hprefix tailTrace_362286
  have hstable : (prefixWord ++ tailWord_362286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362286).length < 2 ^ (prefixWord ++ tailWord_362286).sum := by decide
  have hdescent : baseEnd_362286 < baseStart_362286 := by decide
  rcases family_descends (prefixWord ++ tailWord_362286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362311 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_362311 : Nat := 118140960795 + 362311 * 2 ^ 59
def prefixEnd_362311 : Nat := 4983230072969 + 3 ^ 40 * 362311 * 2
def baseEnd_362311 : Nat := 82684306404994306776119

theorem tailTrace_362311 : CollatzResearch.WordTrace tailWord_362311 prefixEnd_362311 82684306404994306776119 := by
  unfold tailWord_362311
  simp only [CollatzResearch.WordTrace]
  refine ⟨13214567790416599637566787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8809711860277733091711191 13214567790416599637566787)
  ·
    refine ⟨19821851685624899456350181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13214567790416599637566787 19821851685624899456350181)
    ·
      refine ⟨3716597191054668648065659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19821851685624899456350181 3716597191054668648065659)
      ·
        refine ⟨5574895786582002972098489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3716597191054668648065659 5574895786582002972098489)
        ·
          refine ⟨4181171839936502229073867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5574895786582002972098489 4181171839936502229073867)
          ·
            refine ⟨6271757759904753343610801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181171839936502229073867 6271757759904753343610801)
            ·
              refine ⟨4703818319928565007708101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6271757759904753343610801 4703818319928565007708101)
              ·
                refine ⟨881965934986605938945269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4703818319928565007708101 881965934986605938945269)
                ·
                  refine ⟨82684306404994306776119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 881965934986605938945269 82684306404994306776119)
                  ·
                    rfl

theorem cell21_362311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_362311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362311 prefixEnd_362311 := by exact prefixLift 362311
  have htrace : WordTrace (prefixWord ++ tailWord_362311) baseStart_362311 baseEnd_362311 := by
    simpa [prefixWord, tailWord_362311, baseEnd_362311] using wordTrace_append hprefix tailTrace_362311
  have hstable : (prefixWord ++ tailWord_362311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362311).length < 2 ^ (prefixWord ++ tailWord_362311).sum := by decide
  have hdescent : baseEnd_362311 < baseStart_362311 := by decide
  rcases family_descends (prefixWord ++ tailWord_362311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362373 : List Nat := [1, 3, 1, 1, 3, 2, 5, 5]
def baseStart_362373 : Nat := 118140960795 + 362373 * 2 ^ 59
def prefixEnd_362373 : Nat := 4983230072969 + 3 ^ 40 * 362373 * 2
def baseEnd_362373 : Nat := 27566151883231992247553

theorem tailTrace_362373 : CollatzResearch.WordTrace tailWord_362373 prefixEnd_362373 27566151883231992247553 := by
  unfold tailWord_362373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216829116191984226323773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8811219410794656150882515 13216829116191984226323773)
  ·
    refine ⟨4956310918571994084871415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13216829116191984226323773 4956310918571994084871415)
    ·
      refine ⟨7434466377857991127307123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4956310918571994084871415 7434466377857991127307123)
      ·
        refine ⟨11151699566786986690960685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434466377857991127307123 11151699566786986690960685)
        ·
          refine ⟨4181887337545120009110257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11151699566786986690960685 4181887337545120009110257)
          ·
            refine ⟨3136415503158840006832693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4181887337545120009110257 3136415503158840006832693)
            ·
              refine ⟨294038953421141250640565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3136415503158840006832693 294038953421141250640565)
              ·
                refine ⟨27566151883231992247553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294038953421141250640565 27566151883231992247553)
                ·
                  rfl

theorem cell21_362373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 5].length) (baseStart_362373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362373 prefixEnd_362373 := by exact prefixLift 362373
  have htrace : WordTrace (prefixWord ++ tailWord_362373) baseStart_362373 baseEnd_362373 := by
    simpa [prefixWord, tailWord_362373, baseEnd_362373] using wordTrace_append hprefix tailTrace_362373
  have hstable : (prefixWord ++ tailWord_362373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362373).length < 2 ^ (prefixWord ++ tailWord_362373).sum := by decide
  have hdescent : baseEnd_362373 < baseStart_362373 := by decide
  rcases family_descends (prefixWord ++ tailWord_362373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362404 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_362404 : Nat := 118140960795 + 362404 * 2 ^ 59
def prefixEnd_362404 : Nat := 4983230072969 + 3 ^ 40 * 362404 * 2
def baseEnd_362404 : Nat := 82705530272046811725929

theorem tailTrace_362404 : CollatzResearch.WordTrace tailWord_362404 prefixEnd_362404 82705530272046811725929 := by
  unfold tailWord_362404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6608979889539838260351133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8811973186053117680468177 6608979889539838260351133)
  ·
    refine ⟨2478367458577439347631675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6608979889539838260351133 2478367458577439347631675)
    ·
      refine ⟨3717551187866159021447513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478367458577439347631675 3717551187866159021447513)
      ·
        refine ⟨2788163390899619266085635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3717551187866159021447513 2788163390899619266085635)
        ·
          refine ⟨4182245086349428899128453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788163390899619266085635 4182245086349428899128453)
          ·
            refine ⟨784170953690517918586585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4182245086349428899128453 784170953690517918586585)
            ·
              refine ⟨588128215267888438939939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784170953690517918586585 588128215267888438939939)
              ·
                refine ⟨882192322901832658409909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588128215267888438939939 882192322901832658409909)
                ·
                  refine ⟨82705530272046811725929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 882192322901832658409909 82705530272046811725929)
                  ·
                    rfl

theorem cell21_362404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_362404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362404 prefixEnd_362404 := by exact prefixLift 362404
  have htrace : WordTrace (prefixWord ++ tailWord_362404) baseStart_362404 baseEnd_362404 := by
    simpa [prefixWord, tailWord_362404, baseEnd_362404] using wordTrace_append hprefix tailTrace_362404
  have hstable : (prefixWord ++ tailWord_362404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362404).length < 2 ^ (prefixWord ++ tailWord_362404).sum := by decide
  have hdescent : baseEnd_362404 < baseStart_362404 := by decide
  rcases family_descends (prefixWord ++ tailWord_362404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362418 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_362418 : Nat := 118140960795 + 362418 * 2 ^ 59
def prefixEnd_362418 : Nat := 4983230072969 + 3 ^ 40 * 362418 * 2
def baseEnd_362418 : Nat := 82708725262785898492567

theorem tailTrace_362418 : CollatzResearch.WordTrace tailWord_362418 prefixEnd_362418 82708725262785898492567 := by
  unfold tailWord_362418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3304617600257239227927977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8812313600685971274474605 3304617600257239227927977)
  ·
    refine ⟨2478463200192929420945983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3304617600257239227927977 2478463200192929420945983)
    ·
      refine ⟨3717694800289394131418975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478463200192929420945983 3717694800289394131418975)
      ·
        refine ⟨5576542200434091197128463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717694800289394131418975 5576542200434091197128463)
        ·
          refine ⟨8364813300651136795692695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576542200434091197128463 8364813300651136795692695)
          ·
            refine ⟨12547219950976705193539043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364813300651136795692695 12547219950976705193539043)
            ·
              refine ⟨18820829926465057790308565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12547219950976705193539043 18820829926465057790308565)
              ·
                refine ⟨441113201401524791960357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18820829926465057790308565 441113201401524791960357)
                ·
                  refine ⟨82708725262785898492567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441113201401524791960357 82708725262785898492567)
                  ·
                    rfl

theorem cell21_362418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_362418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362418 prefixEnd_362418 := by exact prefixLift 362418
  have htrace : WordTrace (prefixWord ++ tailWord_362418) baseStart_362418 baseEnd_362418 := by
    simpa [prefixWord, tailWord_362418, baseEnd_362418] using wordTrace_append hprefix tailTrace_362418
  have hstable : (prefixWord ++ tailWord_362418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362418).length < 2 ^ (prefixWord ++ tailWord_362418).sum := by decide
  have hdescent : baseEnd_362418 < baseStart_362418 := by decide
  rcases family_descends (prefixWord ++ tailWord_362418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362432 : List Nat := [2, 1, 1, 2, 3, 2, 3, 7]
def baseStart_362432 : Nat := 118140960795 + 362432 * 2 ^ 59
def prefixEnd_362432 : Nat := 4983230072969 + 3 ^ 40 * 362432 * 2
def baseEnd_362432 : Nat := 27570640084508328419735

theorem tailTrace_362432 : CollatzResearch.WordTrace tailWord_362432 prefixEnd_362432 27570640084508328419735 := by
  unfold tailWord_362432
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609490511489118651360775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8812654015318824868481033 6609490511489118651360775)
  ·
    refine ⟨9914235767233677977041163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6609490511489118651360775 9914235767233677977041163)
    ·
      refine ⟨14871353650850516965561745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9914235767233677977041163 14871353650850516965561745)
      ·
        refine ⟨11153515238137887724171309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14871353650850516965561745 11153515238137887724171309)
        ·
          refine ⟨4182568214301707896564241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11153515238137887724171309 4182568214301707896564241)
          ·
            refine ⟨3136926160726280922423181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4182568214301707896564241 3136926160726280922423181)
            ·
              refine ⟨1176347310272355345908693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3136926160726280922423181 1176347310272355345908693)
              ·
                refine ⟨27570640084508328419735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1176347310272355345908693 27570640084508328419735)
                ·
                  rfl

theorem cell21_362432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_362432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362432 prefixEnd_362432 := by exact prefixLift 362432
  have htrace : WordTrace (prefixWord ++ tailWord_362432) baseStart_362432 baseEnd_362432 := by
    simpa [prefixWord, tailWord_362432, baseEnd_362432] using wordTrace_append hprefix tailTrace_362432
  have hstable : (prefixWord ++ tailWord_362432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362432).length < 2 ^ (prefixWord ++ tailWord_362432).sum := by decide
  have hdescent : baseEnd_362432 < baseStart_362432 := by decide
  rcases family_descends (prefixWord ++ tailWord_362432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362525 : List Nat := [1, 4, 2, 2, 2, 1, 3, 6]
def baseStart_362525 : Nat := 118140960795 + 362525 * 2 ^ 59
def prefixEnd_362525 : Nat := 4983230072969 + 3 ^ 40 * 362525 * 2
def baseEnd_362525 : Nat := 27577714706859163403005

theorem tailTrace_362525 : CollatzResearch.WordTrace tailWord_362525 prefixEnd_362525 27577714706859163403005 := by
  unfold tailWord_362525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13222373011641314185857029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8814915341094209457238019 13222373011641314185857029)
  ·
    refine ⟨2479194939682746409848193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13222373011641314185857029 2479194939682746409848193)
    ·
      refine ⟨1859396204762059807386145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2479194939682746409848193 1859396204762059807386145)
      ·
        refine ⟨1394547153571544855539609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1859396204762059807386145 1394547153571544855539609)
        ·
          refine ⟨1045910365178658641654707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394547153571544855539609 1045910365178658641654707)
          ·
            refine ⟨1568865547767987962482061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045910365178658641654707 1568865547767987962482061)
            ·
              refine ⟨588324580412995485930773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1568865547767987962482061 588324580412995485930773)
              ·
                refine ⟨27577714706859163403005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 588324580412995485930773 27577714706859163403005)
                ·
                  rfl

theorem cell21_362525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 6].length) (baseStart_362525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362525 prefixEnd_362525 := by exact prefixLift 362525
  have htrace : WordTrace (prefixWord ++ tailWord_362525) baseStart_362525 baseEnd_362525 := by
    simpa [prefixWord, tailWord_362525, baseEnd_362525] using wordTrace_append hprefix tailTrace_362525
  have hstable : (prefixWord ++ tailWord_362525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362525).length < 2 ^ (prefixWord ++ tailWord_362525).sum := by decide
  have hdescent : baseEnd_362525 < baseStart_362525 := by decide
  rcases family_descends (prefixWord ++ tailWord_362525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362542 : List Nat := [4, 1, 3, 1, 1, 3, 3, 5]
def baseStart_362542 : Nat := 118140960795 + 362542 * 2 ^ 59
def prefixEnd_362542 : Nat := 4983230072969 + 3 ^ 40 * 362542 * 2
def baseEnd_362542 : Nat := 27579007917396412808549

theorem tailTrace_362542 : CollatzResearch.WordTrace tailWord_362542 prefixEnd_362542 27579007917396412808549 := by
  unfold tailWord_362542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652874131572465761153235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8815328701719817392817253 1652874131572465761153235)
  ·
    refine ⟨2479311197358698641729853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652874131572465761153235 2479311197358698641729853)
    ·
      refine ⟨929741699009511990648695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2479311197358698641729853 929741699009511990648695)
      ·
        refine ⟨1394612548514267985973043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929741699009511990648695 1394612548514267985973043)
        ·
          refine ⟨2091918822771401978959565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394612548514267985973043 2091918822771401978959565)
          ·
            refine ⟨784469558539275742109837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2091918822771401978959565 784469558539275742109837)
            ·
              refine ⟨294176084452228403291189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784469558539275742109837 294176084452228403291189)
              ·
                refine ⟨27579007917396412808549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294176084452228403291189 27579007917396412808549)
                ·
                  rfl

theorem cell21_362542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_362542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362542 prefixEnd_362542 := by exact prefixLift 362542
  have htrace : WordTrace (prefixWord ++ tailWord_362542) baseStart_362542 baseEnd_362542 := by
    simpa [prefixWord, tailWord_362542, baseEnd_362542] using wordTrace_append hprefix tailTrace_362542
  have hstable : (prefixWord ++ tailWord_362542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362542).length < 2 ^ (prefixWord ++ tailWord_362542).sum := by decide
  have hdescent : baseEnd_362542 < baseStart_362542 := by decide
  rcases family_descends (prefixWord ++ tailWord_362542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362573 : List Nat := [1, 6, 1, 1, 1, 1, 1, 6, 3]
def baseStart_362573 : Nat := 118140960795 + 362573 * 2 ^ 59
def prefixEnd_362573 : Nat := 4983230072969 + 3 ^ 40 * 362573 * 2
def baseEnd_362573 : Nat := 82744098374540073408917

theorem tailTrace_362573 : CollatzResearch.WordTrace tailWord_362573 prefixEnd_362573 82744098374540073408917 := by
  unfold tailWord_362573
  simp only [CollatzResearch.WordTrace]
  refine ⟨13224123715467418383604373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8816082476978278922402915 13224123715467418383604373)
  ·
    refine ⟨619880799162535236731455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13224123715467418383604373 619880799162535236731455)
    ·
      refine ⟨929821198743802855097183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619880799162535236731455 929821198743802855097183)
      ·
        refine ⟨1394731798115704282645775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929821198743802855097183 1394731798115704282645775)
        ·
          refine ⟨2092097697173556423968663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394731798115704282645775 2092097697173556423968663)
          ·
            refine ⟨3138146545760334635952995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092097697173556423968663 3138146545760334635952995)
            ·
              refine ⟨4707219818640501953929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138146545760334635952995 4707219818640501953929493)
              ·
                refine ⟨220650928998773529090445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4707219818640501953929493 220650928998773529090445)
                ·
                  refine ⟨82744098374540073408917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220650928998773529090445 82744098374540073408917)
                  ·
                    rfl

theorem cell21_362573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_362573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362573 prefixEnd_362573 := by exact prefixLift 362573
  have htrace : WordTrace (prefixWord ++ tailWord_362573) baseStart_362573 baseEnd_362573 := by
    simpa [prefixWord, tailWord_362573, baseEnd_362573] using wordTrace_append hprefix tailTrace_362573
  have hstable : (prefixWord ++ tailWord_362573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362573).length < 2 ^ (prefixWord ++ tailWord_362573).sum := by decide
  have hdescent : baseEnd_362573 < baseStart_362573 := by decide
  rcases family_descends (prefixWord ++ tailWord_362573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362632 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_362632 : Nat := 118140960795 + 362632 * 2 ^ 59
def prefixEnd_362632 : Nat := 4983230072969 + 3 ^ 40 * 362632 * 2
def baseEnd_362632 : Nat := 82757562978369081925463

theorem tailTrace_362632 : CollatzResearch.WordTrace tailWord_362632 prefixEnd_362632 82757562978369081925463 := by
  unfold tailWord_362632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613137811126835730001075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8817517081502447640001433 6613137811126835730001075)
  ·
    refine ⟨9919706716690253595001613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6613137811126835730001075 9919706716690253595001613)
    ·
      refine ⟨3719890018758845098125605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9919706716690253595001613 3719890018758845098125605)
      ·
        refine ⟨697479378517283455898551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3719890018758845098125605 697479378517283455898551)
        ·
          refine ⟨1046219067775925183847827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697479378517283455898551 1046219067775925183847827)
          ·
            refine ⟨1569328601663887775771741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046219067775925183847827 1569328601663887775771741)
            ·
              refine ⟨588498225623957915914403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569328601663887775771741 588498225623957915914403)
              ·
                refine ⟨882747338435936873871605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588498225623957915914403 882747338435936873871605)
                ·
                  refine ⟨82757562978369081925463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 882747338435936873871605 82757562978369081925463)
                  ·
                    rfl

theorem cell21_362632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_362632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362632 prefixEnd_362632 := by exact prefixLift 362632
  have htrace : WordTrace (prefixWord ++ tailWord_362632) baseStart_362632 baseEnd_362632 := by
    simpa [prefixWord, tailWord_362632, baseEnd_362632] using wordTrace_append hprefix tailTrace_362632
  have hstable : (prefixWord ++ tailWord_362632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362632).length < 2 ^ (prefixWord ++ tailWord_362632).sum := by decide
  have hdescent : baseEnd_362632 < baseStart_362632 := by decide
  rcases family_descends (prefixWord ++ tailWord_362632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362677 : List Nat := [1, 3, 3, 4, 1, 9]
def baseStart_362677 : Nat := 118140960795 + 362677 * 2 ^ 59
def prefixEnd_362677 : Nat := 4983230072969 + 3 ^ 40 * 362677 * 2
def baseEnd_362677 : Nat := 3065475281165148284273

theorem tailTrace_362677 : CollatzResearch.WordTrace tailWord_362677 prefixEnd_362677 3065475281165148284273 := by
  unfold tailWord_362677
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227916907090644145390285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8818611271393762763593523 13227916907090644145390285)
  ·
    refine ⟨4960468840158991554521357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13227916907090644145390285 4960468840158991554521357)
    ·
      refine ⟨1860175815059621832945509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4960468840158991554521357 1860175815059621832945509)
      ·
        refine ⟨348782965323679093677283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1860175815059621832945509 348782965323679093677283)
        ·
          refine ⟨523174447985518640515925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348782965323679093677283 523174447985518640515925)
          ·
            refine ⟨3065475281165148284273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 523174447985518640515925 3065475281165148284273)
            ·
              rfl

theorem cell21_362677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 9].length) (baseStart_362677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362677 prefixEnd_362677 := by exact prefixLift 362677
  have htrace : WordTrace (prefixWord ++ tailWord_362677) baseStart_362677 baseEnd_362677 := by
    simpa [prefixWord, tailWord_362677, baseEnd_362677] using wordTrace_append hprefix tailTrace_362677
  have hstable : (prefixWord ++ tailWord_362677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362677).length < 2 ^ (prefixWord ++ tailWord_362677).sum := by decide
  have hdescent : baseEnd_362677 < baseStart_362677 := by decide
  rcases family_descends (prefixWord ++ tailWord_362677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362725 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 3]
def baseStart_362725 : Nat := 118140960795 + 362725 * 2 ^ 59
def prefixEnd_362725 : Nat := 4983230072969 + 3 ^ 40 * 362725 * 2
def baseEnd_362725 : Nat := 82778786845421586875273

theorem tailTrace_362725 : CollatzResearch.WordTrace tailWord_362725 prefixEnd_362725 82778786845421586875273 := by
  unfold tailWord_362725
  simp only [CollatzResearch.WordTrace]
  refine ⟨13229667610916748343137629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8819778407277832228758419 13229667610916748343137629)
  ·
    refine ⟨4961125354093780628676611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13229667610916748343137629 4961125354093780628676611)
    ·
      refine ⟨7441688031140670943014917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961125354093780628676611 7441688031140670943014917)
      ·
        refine ⟨1395316505838875801815297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7441688031140670943014917 1395316505838875801815297)
        ·
          refine ⟨1046487379379156851361473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395316505838875801815297 1046487379379156851361473)
          ·
            refine ⟨784865534534367638521105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046487379379156851361473 784865534534367638521105)
            ·
              refine ⟨588649150900775728890829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784865534534367638521105 588649150900775728890829)
              ·
                refine ⟨220743431587790898334061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588649150900775728890829 220743431587790898334061)
                ·
                  refine ⟨82778786845421586875273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220743431587790898334061 82778786845421586875273)
                  ·
                    rfl

theorem cell21_362725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_362725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362725 prefixEnd_362725 := by exact prefixLift 362725
  have htrace : WordTrace (prefixWord ++ tailWord_362725) baseStart_362725 baseEnd_362725 := by
    simpa [prefixWord, tailWord_362725, baseEnd_362725] using wordTrace_append hprefix tailTrace_362725
  have hstable : (prefixWord ++ tailWord_362725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362725).length < 2 ^ (prefixWord ++ tailWord_362725).sum := by decide
  have hdescent : baseEnd_362725 < baseStart_362725 := by decide
  rcases family_descends (prefixWord ++ tailWord_362725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362756 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_362756 : Nat := 118140960795 + 362756 * 2 ^ 59
def prefixEnd_362756 : Nat := 4983230072969 + 3 ^ 40 * 362756 * 2
def baseEnd_362756 : Nat := 82785861467772421858543

theorem tailTrace_362756 : CollatzResearch.WordTrace tailWord_362756 prefixEnd_362756 82785861467772421858543 := by
  unfold tailWord_362756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6615399136902220318758061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8820532182536293758344081 6615399136902220318758061)
  ·
    refine ⟨2480774676338332619534273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6615399136902220318758061 2480774676338332619534273)
    ·
      refine ⟨1860581007253749464650705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2480774676338332619534273 1860581007253749464650705)
      ·
        refine ⟨1395435755440312098488029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860581007253749464650705 1395435755440312098488029)
        ·
          refine ⟨523288408290117036933011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1395435755440312098488029 523288408290117036933011)
          ·
            refine ⟨784932612435175555399517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523288408290117036933011 784932612435175555399517)
            ·
              refine ⟨294349729663190833274819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784932612435175555399517 294349729663190833274819)
              ·
                refine ⟨441524594494786249912229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294349729663190833274819 441524594494786249912229)
                ·
                  refine ⟨82785861467772421858543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441524594494786249912229 82785861467772421858543)
                  ·
                    rfl

theorem cell21_362756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_362756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362756 prefixEnd_362756 := by exact prefixLift 362756
  have htrace : WordTrace (prefixWord ++ tailWord_362756) baseStart_362756 baseEnd_362756 := by
    simpa [prefixWord, tailWord_362756, baseEnd_362756] using wordTrace_append hprefix tailTrace_362756
  have hstable : (prefixWord ++ tailWord_362756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362756).length < 2 ^ (prefixWord ++ tailWord_362756).sum := by decide
  have hdescent : baseEnd_362756 < baseStart_362756 := by decide
  rcases family_descends (prefixWord ++ tailWord_362756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362801 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 5]
def baseStart_362801 : Nat := 118140960795 + 362801 * 2 ^ 59
def prefixEnd_362801 : Nat := 4983230072969 + 3 ^ 40 * 362801 * 2
def baseEnd_362801 : Nat := 82796131080862343608451

theorem tailTrace_362801 : CollatzResearch.WordTrace tailWord_362801 prefixEnd_362801 82796131080862343608451 := by
  unfold tailWord_362801
  simp only [CollatzResearch.WordTrace]
  refine ⟨13232439558641413322904257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8821626372427608881936171 13232439558641413322904257)
  ·
    refine ⟨9924329668981059992178193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13232439558641413322904257 9924329668981059992178193)
    ·
      refine ⟨7443247251735794994133645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9924329668981059992178193 7443247251735794994133645)
      ·
        refine ⟨2791217719400923122800117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7443247251735794994133645 2791217719400923122800117)
        ·
          refine ⟨261676661193836542762511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2791217719400923122800117 261676661193836542762511)
          ·
            refine ⟨392514991790754814143767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261676661193836542762511 392514991790754814143767)
            ·
              refine ⟨588772487686132221215651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392514991790754814143767 588772487686132221215651)
              ·
                refine ⟨883158731529198331823477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588772487686132221215651 883158731529198331823477)
                ·
                  refine ⟨82796131080862343608451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 883158731529198331823477 82796131080862343608451)
                  ·
                    rfl

theorem cell21_362801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 5].length) (baseStart_362801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362801 prefixEnd_362801 := by exact prefixLift 362801
  have htrace : WordTrace (prefixWord ++ tailWord_362801) baseStart_362801 baseEnd_362801 := by
    simpa [prefixWord, tailWord_362801, baseEnd_362801] using wordTrace_append hprefix tailTrace_362801
  have hstable : (prefixWord ++ tailWord_362801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362801).length < 2 ^ (prefixWord ++ tailWord_362801).sum := by decide
  have hdescent : baseEnd_362801 < baseStart_362801 := by decide
  rcases family_descends (prefixWord ++ tailWord_362801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362812 : List Nat := [2, 2, 2, 2, 1, 2, 4, 6]
def baseStart_362812 : Nat := 118140960795 + 362812 * 2 ^ 59
def prefixEnd_362812 : Nat := 4983230072969 + 3 ^ 40 * 362812 * 2
def baseEnd_362812 : Nat := 27599547143576256308365

theorem tailTrace_362812 : CollatzResearch.WordTrace tailWord_362812 prefixEnd_362812 27599547143576256308365 := by
  unfold tailWord_362812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616420380800781100777345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8821893841067708134369793 6616420380800781100777345)
  ·
    refine ⟨4962315285600585825583009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6616420380800781100777345 4962315285600585825583009)
    ·
      refine ⟨3721736464200439369187257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4962315285600585825583009 3721736464200439369187257)
      ·
        refine ⟨2791302348150329526890443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3721736464200439369187257 2791302348150329526890443)
        ·
          refine ⟨4186953522225494290335665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791302348150329526890443 4186953522225494290335665)
          ·
            refine ⟨3140215141669120717751749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186953522225494290335665 3140215141669120717751749)
            ·
              refine ⟨588790339062960134578453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3140215141669120717751749 588790339062960134578453)
              ·
                refine ⟨27599547143576256308365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 588790339062960134578453 27599547143576256308365)
                ·
                  rfl

theorem cell21_362812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_362812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362812 prefixEnd_362812 := by exact prefixLift 362812
  have htrace : WordTrace (prefixWord ++ tailWord_362812) baseStart_362812 baseEnd_362812 := by
    simpa [prefixWord, tailWord_362812, baseEnd_362812] using wordTrace_append hprefix tailTrace_362812
  have hstable : (prefixWord ++ tailWord_362812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362812).length < 2 ^ (prefixWord ++ tailWord_362812).sum := by decide
  have hdescent : baseEnd_362812 < baseStart_362812 := by decide
  rcases family_descends (prefixWord ++ tailWord_362812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362871 : List Nat := [1, 1, 3, 1, 1, 2, 2, 10]
def baseStart_362871 : Nat := 118140960795 + 362871 * 2 ^ 59
def prefixEnd_362871 : Nat := 4983230072969 + 3 ^ 40 * 362871 * 2
def baseEnd_362871 : Nat := 27604035344852592480547

theorem tailTrace_362871 : CollatzResearch.WordTrace tailWord_362871 prefixEnd_362871 27604035344852592480547 := by
  unfold tailWord_362871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13234992668387815277952467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8823328445591876851968311 13234992668387815277952467)
  ·
    refine ⟨19852489002581722916928701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13234992668387815277952467 19852489002581722916928701)
    ·
      refine ⟨7444683375968146093848263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19852489002581722916928701 7444683375968146093848263)
      ·
        refine ⟨11167025063952219140772395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7444683375968146093848263 11167025063952219140772395)
        ·
          refine ⟨16750537595928328711158593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11167025063952219140772395 16750537595928328711158593)
          ·
            refine ⟨12562903196946246533368945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16750537595928328711158593 12562903196946246533368945)
            ·
              refine ⟨9422177397709684900026709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12562903196946246533368945 9422177397709684900026709)
              ·
                refine ⟨27604035344852592480547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9422177397709684900026709 27604035344852592480547)
                ·
                  rfl

theorem cell21_362871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 10].length) (baseStart_362871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362871 prefixEnd_362871 := by exact prefixLift 362871
  have htrace : WordTrace (prefixWord ++ tailWord_362871) baseStart_362871 baseEnd_362871 := by
    simpa [prefixWord, tailWord_362871, baseEnd_362871] using wordTrace_append hprefix tailTrace_362871
  have hstable : (prefixWord ++ tailWord_362871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362871).length < 2 ^ (prefixWord ++ tailWord_362871).sum := by decide
  have hdescent : baseEnd_362871 < baseStart_362871 := by decide
  rcases family_descends (prefixWord ++ tailWord_362871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362919 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_362919 : Nat := 118140960795 + 362919 * 2 ^ 59
def prefixEnd_362919 : Nat := 4983230072969 + 3 ^ 40 * 362919 * 2
def baseEnd_362919 : Nat := 82823060288520360641543

theorem tailTrace_362919 : CollatzResearch.WordTrace tailWord_362919 prefixEnd_362919 82823060288520360641543 := by
  unfold tailWord_362919
  simp only [CollatzResearch.WordTrace]
  refine ⟨13236743372213919475699811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8824495581475946317133207 13236743372213919475699811)
  ·
    refine ⟨19855115058320879213549717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13236743372213919475699811 19855115058320879213549717)
    ·
      refine ⟨930708518358791213135143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19855115058320879213549717 930708518358791213135143)
      ·
        refine ⟨1396062777538186819702715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930708518358791213135143 1396062777538186819702715)
        ·
          refine ⟨2094094166307280229554073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396062777538186819702715 2094094166307280229554073)
          ·
            refine ⟨1570570624730460172165555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094094166307280229554073 1570570624730460172165555)
            ·
              refine ⟨2355855937095690258248333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570570624730460172165555 2355855937095690258248333)
              ·
                refine ⟨883445976410883846843125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2355855937095690258248333 883445976410883846843125)
                ·
                  refine ⟨82823060288520360641543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 883445976410883846843125 82823060288520360641543)
                  ·
                    rfl

theorem cell21_362919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_362919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362919 prefixEnd_362919 := by exact prefixLift 362919
  have htrace : WordTrace (prefixWord ++ tailWord_362919) baseStart_362919 baseEnd_362919 := by
    simpa [prefixWord, tailWord_362919, baseEnd_362919] using wordTrace_append hprefix tailTrace_362919
  have hstable : (prefixWord ++ tailWord_362919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362919).length < 2 ^ (prefixWord ++ tailWord_362919).sum := by decide
  have hdescent : baseEnd_362919 < baseStart_362919 := by decide
  rcases family_descends (prefixWord ++ tailWord_362919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362964 : List Nat := [2, 4, 1, 2, 2, 1, 9]
def baseStart_362964 : Nat := 118140960795 + 362964 * 2 ^ 59
def prefixEnd_362964 : Nat := 4983230072969 + 3 ^ 40 * 362964 * 2
def baseEnd_362964 : Nat := 9203703322401142487939

theorem tailTrace_362964 : CollatzResearch.WordTrace tailWord_362964 prefixEnd_362964 9203703322401142487939 := by
  unfold tailWord_362964
  simp only [CollatzResearch.WordTrace]
  refine ⟨6619192328525446080543973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8825589771367261440725297 6619192328525446080543973)
  ·
    refine ⟨1241098561598521140101995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6619192328525446080543973 1241098561598521140101995)
    ·
      refine ⟨1861647842397781710152993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1241098561598521140101995 1861647842397781710152993)
      ·
        refine ⟨1396235881798336282614745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1861647842397781710152993 1396235881798336282614745)
        ·
          refine ⟨1047176911348752211961059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396235881798336282614745 1047176911348752211961059)
          ·
            refine ⟨1570765367023128317941589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047176911348752211961059 1570765367023128317941589)
            ·
              refine ⟨9203703322401142487939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1570765367023128317941589 9203703322401142487939)
              ·
                rfl

theorem cell21_362964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 9].length) (baseStart_362964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362964 prefixEnd_362964 := by exact prefixLift 362964
  have htrace : WordTrace (prefixWord ++ tailWord_362964) baseStart_362964 baseEnd_362964 := by
    simpa [prefixWord, tailWord_362964, baseEnd_362964] using wordTrace_append hprefix tailTrace_362964
  have hstable : (prefixWord ++ tailWord_362964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362964).length < 2 ^ (prefixWord ++ tailWord_362964).sum := by decide
  have hdescent : baseEnd_362964 < baseStart_362964 := by decide
  rcases family_descends (prefixWord ++ tailWord_362964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362981 : List Nat := [1, 3, 1, 5, 2, 1, 2, 6]
def baseStart_362981 : Nat := 118140960795 + 362981 * 2 ^ 59
def prefixEnd_362981 : Nat := 4983230072969 + 3 ^ 40 * 362981 * 2
def baseEnd_362981 : Nat := 27612403177740676869361

theorem tailTrace_362981 : CollatzResearch.WordTrace tailWord_362981 prefixEnd_362981 27612403177740676869361 := by
  unfold tailWord_362981
  simp only [CollatzResearch.WordTrace]
  refine ⟨13239004697989304064456797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8826003131992869376304531 13239004697989304064456797)
  ·
    refine ⟨4964626761745989024171299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13239004697989304064456797 4964626761745989024171299)
    ·
      refine ⟨7446940142618983536256949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964626761745989024171299 7446940142618983536256949)
      ·
        refine ⟨698150638370529706524089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7446940142618983536256949 698150638370529706524089)
        ·
          refine ⟨523612978777897279893067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698150638370529706524089 523612978777897279893067)
          ·
            refine ⟨785419468166845919839601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523612978777897279893067 785419468166845919839601)
            ·
              refine ⟨589064601125134439879701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785419468166845919839601 589064601125134439879701)
              ·
                refine ⟨27612403177740676869361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 589064601125134439879701 27612403177740676869361)
                ·
                  rfl

theorem cell21_362981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 6].length) (baseStart_362981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_362981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_362981 prefixEnd_362981 := by exact prefixLift 362981
  have htrace : WordTrace (prefixWord ++ tailWord_362981) baseStart_362981 baseEnd_362981 := by
    simpa [prefixWord, tailWord_362981, baseEnd_362981] using wordTrace_append hprefix tailTrace_362981
  have hstable : (prefixWord ++ tailWord_362981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362981).length < 2 ^ (prefixWord ++ tailWord_362981).sum := by decide
  have hdescent : baseEnd_362981 < baseStart_362981 := by decide
  rcases family_descends (prefixWord ++ tailWord_362981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363116 : List Nat := [2, 2, 1, 1, 3, 1, 6, 5]
def baseStart_363116 : Nat := 118140960795 + 363116 * 2 ^ 59
def prefixEnd_363116 : Nat := 4983230072969 + 3 ^ 40 * 363116 * 2
def baseEnd_363116 : Nat := 27622672790830598619269

theorem tailTrace_363116 : CollatzResearch.WordTrace tailWord_363116 prefixEnd_363116 27622672790830598619269 := by
  unfold tailWord_363116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621964276250111060310601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8829285701666814747080801 6621964276250111060310601)
  ·
    refine ⟨4966473207187583295232951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6621964276250111060310601 4966473207187583295232951)
    ·
      refine ⟨7449709810781374942849427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4966473207187583295232951 7449709810781374942849427)
      ·
        refine ⟨11174564716172062414274141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7449709810781374942849427 11174564716172062414274141)
        ·
          refine ⟨4190461768564523405352803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11174564716172062414274141 4190461768564523405352803)
          ·
            refine ⟨6285692652846785108029205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190461768564523405352803 6285692652846785108029205)
            ·
              refine ⟨294641843102193051938869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6285692652846785108029205 294641843102193051938869)
              ·
                refine ⟨27622672790830598619269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 294641843102193051938869 27622672790830598619269)
                ·
                  rfl

theorem cell21_363116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_363116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363116 prefixEnd_363116 := by exact prefixLift 363116
  have htrace : WordTrace (prefixWord ++ tailWord_363116) baseStart_363116 baseEnd_363116 := by
    simpa [prefixWord, tailWord_363116, baseEnd_363116] using wordTrace_append hprefix tailTrace_363116
  have hstable : (prefixWord ++ tailWord_363116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363116).length < 2 ^ (prefixWord ++ tailWord_363116).sum := by decide
  have hdescent : baseEnd_363116 < baseStart_363116 := by decide
  rcases family_descends (prefixWord ++ tailWord_363116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363122 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_363122 : Nat := 118140960795 + 363122 * 2 ^ 59
def prefixEnd_363122 : Nat := 4983230072969 + 3 ^ 40 * 363122 * 2
def baseEnd_363122 : Nat := 82869387654237118757795

theorem tailTrace_363122 : CollatzResearch.WordTrace tailWord_363122 prefixEnd_363122 82869387654237118757795 := by
  unfold tailWord_363122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311036847619621286334905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8829431593652323430226413 3311036847619621286334905)
  ·
    refine ⟨2483277635714715964751179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3311036847619621286334905 2483277635714715964751179)
    ·
      refine ⟨3724916453572073947126769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483277635714715964751179 3724916453572073947126769)
      ·
        refine ⟨2793687340179055460345077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3724916453572073947126769 2793687340179055460345077)
        ·
          refine ⟨261908188141786449407351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2793687340179055460345077 261908188141786449407351)
          ·
            refine ⟨392862282212679674111027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261908188141786449407351 392862282212679674111027)
            ·
              refine ⟨589293423319019511166541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392862282212679674111027 589293423319019511166541)
              ·
                refine ⟨220985033744632316687453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589293423319019511166541 220985033744632316687453)
                ·
                  refine ⟨82869387654237118757795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220985033744632316687453 82869387654237118757795)
                  ·
                    rfl

theorem cell21_363122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_363122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363122 prefixEnd_363122 := by exact prefixLift 363122
  have htrace : WordTrace (prefixWord ++ tailWord_363122) baseStart_363122 baseEnd_363122 := by
    simpa [prefixWord, tailWord_363122, baseEnd_363122] using wordTrace_append hprefix tailTrace_363122
  have hstable : (prefixWord ++ tailWord_363122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363122).length < 2 ^ (prefixWord ++ tailWord_363122).sum := by decide
  have hdescent : baseEnd_363122 < baseStart_363122 := by decide
  rcases family_descends (prefixWord ++ tailWord_363122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363133 : List Nat := [1, 4, 1, 1, 6, 1, 7]
def baseStart_363133 : Nat := 118140960795 + 363133 * 2 ^ 59
def prefixEnd_363133 : Nat := 4983230072969 + 3 ^ 40 * 363133 * 2
def baseEnd_363133 : Nat := 9207988667122616008271

theorem tailTrace_363133 : CollatzResearch.WordTrace tailWord_363133 prefixEnd_363133 9207988667122616008271 := by
  unfold tailWord_363133
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244548593438634023990053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8829699062292422682660035 13244548593438634023990053)
  ·
    refine ⟨2483352861269743879498135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13244548593438634023990053 2483352861269743879498135)
    ·
      refine ⟨3725029291904615819247203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483352861269743879498135 3725029291904615819247203)
      ·
        refine ⟨5587543937856923728870805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725029291904615819247203 5587543937856923728870805)
        ·
          refine ⟨261916122087043299790819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5587543937856923728870805 261916122087043299790819)
          ·
            refine ⟨392874183130564949686229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261916122087043299790819 392874183130564949686229)
            ·
              refine ⟨9207988667122616008271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 392874183130564949686229 9207988667122616008271)
              ·
                rfl

theorem cell21_363133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 7].length) (baseStart_363133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363133 prefixEnd_363133 := by exact prefixLift 363133
  have htrace : WordTrace (prefixWord ++ tailWord_363133) baseStart_363133 baseEnd_363133 := by
    simpa [prefixWord, tailWord_363133, baseEnd_363133] using wordTrace_append hprefix tailTrace_363133
  have hstable : (prefixWord ++ tailWord_363133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363133).length < 2 ^ (prefixWord ++ tailWord_363133).sum := by decide
  have hdescent : baseEnd_363133 < baseStart_363133 := by decide
  rcases family_descends (prefixWord ++ tailWord_363133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363161 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 4]
def baseStart_363161 : Nat := 118140960795 + 363161 * 2 ^ 59
def prefixEnd_363161 : Nat := 4983230072969 + 3 ^ 40 * 363161 * 2
def baseEnd_363161 : Nat := 82878287985581717607715

theorem tailTrace_363161 : CollatzResearch.WordTrace tailWord_363161 prefixEnd_363161 82878287985581717607715 := by
  unfold tailWord_363161
  simp only [CollatzResearch.WordTrace]
  refine ⟨13245569837337194806009337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8830379891558129870672891 13245569837337194806009337)
  ·
    refine ⟨9934177378002896104507003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13245569837337194806009337 9934177378002896104507003)
    ·
      refine ⟨14901266067004344156760505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9934177378002896104507003 14901266067004344156760505)
      ·
        refine ⟨11175949550253258117570379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14901266067004344156760505 11175949550253258117570379)
        ·
          refine ⟨16763924325379887176355569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11175949550253258117570379 16763924325379887176355569)
          ·
            refine ⟨12572943244034915382266677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16763924325379887176355569 12572943244034915382266677)
            ·
              refine ⟨1178713429128273317087501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12572943244034915382266677 1178713429128273317087501)
              ·
                refine ⟨442017535923102493907813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1178713429128273317087501 442017535923102493907813)
                ·
                  refine ⟨82878287985581717607715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442017535923102493907813 82878287985581717607715)
                  ·
                    rfl

theorem cell21_363161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_363161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363161 prefixEnd_363161 := by exact prefixLift 363161
  have htrace : WordTrace (prefixWord ++ tailWord_363161) baseStart_363161 baseEnd_363161 := by
    simpa [prefixWord, tailWord_363161, baseEnd_363161] using wordTrace_append hprefix tailTrace_363161
  have hstable : (prefixWord ++ tailWord_363161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363161).length < 2 ^ (prefixWord ++ tailWord_363161).sum := by decide
  have hdescent : baseEnd_363161 < baseStart_363161 := by decide
  rcases family_descends (prefixWord ++ tailWord_363161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363271 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 4]
def baseStart_363271 : Nat := 118140960795 + 363271 * 2 ^ 59
def prefixEnd_363271 : Nat := 4983230072969 + 3 ^ 40 * 363271 * 2
def baseEnd_363271 : Nat := 82903391484245970774157

theorem tailTrace_363271 : CollatzResearch.WordTrace tailWord_363271 prefixEnd_363271 82903391484245970774157 := by
  unfold tailWord_363271
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249581866938683592513667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8833054577959122395009111 13249581866938683592513667)
  ·
    refine ⟨19874372800408025388770501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13249581866938683592513667 19874372800408025388770501)
    ·
      refine ⟨3726444900076504760394469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19874372800408025388770501 3726444900076504760394469)
      ·
        refine ⟨698708418764344642573963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3726444900076504760394469 698708418764344642573963)
        ·
          refine ⟨1048062628146516963860945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698708418764344642573963 1048062628146516963860945)
          ·
            refine ⟨786046971109887722895709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048062628146516963860945 786046971109887722895709)
            ·
              refine ⟨294767614166207896085891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786046971109887722895709 294767614166207896085891)
              ·
                refine ⟨442151421249311844128837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294767614166207896085891 442151421249311844128837)
                ·
                  refine ⟨82903391484245970774157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442151421249311844128837 82903391484245970774157)
                  ·
                    rfl

theorem cell21_363271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 4].length) (baseStart_363271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363271 prefixEnd_363271 := by exact prefixLift 363271
  have htrace : WordTrace (prefixWord ++ tailWord_363271) baseStart_363271 baseEnd_363271 := by
    simpa [prefixWord, tailWord_363271, baseEnd_363271] using wordTrace_append hprefix tailTrace_363271
  have hstable : (prefixWord ++ tailWord_363271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363271).length < 2 ^ (prefixWord ++ tailWord_363271).sum := by decide
  have hdescent : baseEnd_363271 < baseStart_363271 := by decide
  rcases family_descends (prefixWord ++ tailWord_363271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363313 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 4]
def baseStart_363313 : Nat := 118140960795 + 363313 * 2 ^ 59
def prefixEnd_363313 : Nat := 4983230072969 + 3 ^ 40 * 363313 * 2
def baseEnd_363313 : Nat := 82912976456463231074071

theorem tailTrace_363313 : CollatzResearch.WordTrace tailWord_363313 prefixEnd_363313 82912976456463231074071 := by
  unfold tailWord_363313
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251113732786524765542593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8834075821857683177028395 13251113732786524765542593)
  ·
    refine ⟨9938335299589893574156945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13251113732786524765542593 9938335299589893574156945)
    ·
      refine ⟨7453751474692420180617709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9938335299589893574156945 7453751474692420180617709)
      ·
        refine ⟨2795156803009657567731641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7453751474692420180617709 2795156803009657567731641)
        ·
          refine ⟨2096367602257243175798731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2795156803009657567731641 2096367602257243175798731)
          ·
            refine ⟨3144551403385864763698097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096367602257243175798731 3144551403385864763698097)
            ·
              refine ⟨2358413552539398572773573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144551403385864763698097 2358413552539398572773573)
              ·
                refine ⟨442202541101137232395045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2358413552539398572773573 442202541101137232395045)
                ·
                  refine ⟨82912976456463231074071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442202541101137232395045 82912976456463231074071)
                  ·
                    rfl

theorem cell21_363313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_363313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363313 prefixEnd_363313 := by exact prefixLift 363313
  have htrace : WordTrace (prefixWord ++ tailWord_363313) baseStart_363313 baseEnd_363313 := by
    simpa [prefixWord, tailWord_363313, baseEnd_363313] using wordTrace_append hprefix tailTrace_363313
  have hstable : (prefixWord ++ tailWord_363313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363313).length < 2 ^ (prefixWord ++ tailWord_363313).sum := by decide
  have hdescent : baseEnd_363313 < baseStart_363313 := by decide
  rcases family_descends (prefixWord ++ tailWord_363313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363327 : List Nat := [1, 1, 2, 2, 5, 1, 1, 8]
def baseStart_363327 : Nat := 118140960795 + 363327 * 2 ^ 59
def prefixEnd_363327 : Nat := 4983230072969 + 3 ^ 40 * 363327 * 2
def baseEnd_363327 : Nat := 27638723815734105946903

theorem tailTrace_363327 : CollatzResearch.WordTrace tailWord_363327 prefixEnd_363327 27638723815734105946903 := by
  unfold tailWord_363327
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251624354735805156552235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8834416236490536771034823 13251624354735805156552235)
  ·
    refine ⟨19877436532103707734828353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13251624354735805156552235 19877436532103707734828353)
    ·
      refine ⟨14908077399077780801121265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19877436532103707734828353 14908077399077780801121265)
      ·
        refine ⟨11181058049308335600840949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14908077399077780801121265 11181058049308335600840949)
        ·
          refine ⟨1048224192122656462578839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11181058049308335600840949 1048224192122656462578839)
          ·
            refine ⟨1572336288183984693868259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048224192122656462578839 1572336288183984693868259)
            ·
              refine ⟨2358504432275977040802389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572336288183984693868259 2358504432275977040802389)
              ·
                refine ⟨27638723815734105946903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2358504432275977040802389 27638723815734105946903)
                ·
                  rfl

theorem cell21_363327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_363327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363327 prefixEnd_363327 := by exact prefixLift 363327
  have htrace : WordTrace (prefixWord ++ tailWord_363327) baseStart_363327 baseEnd_363327 := by
    simpa [prefixWord, tailWord_363327, baseEnd_363327] using wordTrace_append hprefix tailTrace_363327
  have hstable : (prefixWord ++ tailWord_363327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363327).length < 2 ^ (prefixWord ++ tailWord_363327).sum := by decide
  have hdescent : baseEnd_363327 < baseStart_363327 := by decide
  rcases family_descends (prefixWord ++ tailWord_363327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363389 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 4]
def baseStart_363389 : Nat := 118140960795 + 363389 * 2 ^ 59
def prefixEnd_363389 : Nat := 4983230072969 + 3 ^ 40 * 363389 * 2
def baseEnd_363389 : Nat := 82930320691903987807249

theorem tailTrace_363389 : CollatzResearch.WordTrace tailWord_363389 prefixEnd_363389 82930320691903987807249 := by
  unfold tailWord_363389
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253885680511189745309221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8835923787007459830206147 13253885680511189745309221)
  ·
    refine ⟨2485103565095848077245479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13253885680511189745309221 2485103565095848077245479)
    ·
      refine ⟨3727655347643772115868219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485103565095848077245479 3727655347643772115868219)
      ·
        refine ⟨5591483021465658173802329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3727655347643772115868219 5591483021465658173802329)
        ·
          refine ⟨4193612266099243630351747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5591483021465658173802329 4193612266099243630351747)
          ·
            refine ⟨6290418399148865445527621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193612266099243630351747 6290418399148865445527621)
            ·
              refine ⟨1179453449840412271036429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6290418399148865445527621 1179453449840412271036429)
              ·
                refine ⟨442295043690154601638661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1179453449840412271036429 442295043690154601638661)
                ·
                  refine ⟨82930320691903987807249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442295043690154601638661 82930320691903987807249)
                  ·
                    rfl

theorem cell21_363389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_363389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363389 prefixEnd_363389 := by exact prefixLift 363389
  have htrace : WordTrace (prefixWord ++ tailWord_363389) baseStart_363389 baseEnd_363389 := by
    simpa [prefixWord, tailWord_363389, baseEnd_363389] using wordTrace_append hprefix tailTrace_363389
  have hstable : (prefixWord ++ tailWord_363389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363389).length < 2 ^ (prefixWord ++ tailWord_363389).sum := by decide
  have hdescent : baseEnd_363389 < baseStart_363389 := by decide
  rcases family_descends (prefixWord ++ tailWord_363389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363417 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_363417 : Nat := 118140960795 + 363417 * 2 ^ 59
def prefixEnd_363417 : Nat := 4983230072969 + 3 ^ 40 * 363417 * 2
def baseEnd_363417 : Nat := 82936710673382161340525

theorem tailTrace_363417 : CollatzResearch.WordTrace tailWord_363417 prefixEnd_363417 82936710673382161340525 := by
  unfold tailWord_363417
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254906924409750527328505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8836604616273167018219003 13254906924409750527328505)
  ·
    refine ⟨9941180193307312895496379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13254906924409750527328505 9941180193307312895496379)
    ·
      refine ⟨14911770289960969343244569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9941180193307312895496379 14911770289960969343244569)
      ·
        refine ⟨11183827717470727007433427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14911770289960969343244569 11183827717470727007433427)
        ·
          refine ⟨16775741576206090511150141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11183827717470727007433427 16775741576206090511150141)
          ·
            refine ⟨6290903091077283941681303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16775741576206090511150141 6290903091077283941681303)
            ·
              refine ⟨9436354636615925912521955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6290903091077283941681303 9436354636615925912521955)
              ·
                refine ⟨14154531954923888868782933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9436354636615925912521955 14154531954923888868782933)
                ·
                  refine ⟨82936710673382161340525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14154531954923888868782933 82936710673382161340525)
                  ·
                    rfl

theorem cell21_363417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_363417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_363417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_363417 prefixEnd_363417 := by exact prefixLift 363417
  have htrace : WordTrace (prefixWord ++ tailWord_363417) baseStart_363417 baseEnd_363417 := by
    simpa [prefixWord, tailWord_363417, baseEnd_363417] using wordTrace_append hprefix tailTrace_363417
  have hstable : (prefixWord ++ tailWord_363417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363417).length < 2 ^ (prefixWord ++ tailWord_363417).sum := by decide
  have hdescent : baseEnd_363417 < baseStart_363417 := by decide
  rcases family_descends (prefixWord ++ tailWord_363417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
