import V185TrunkScan23Chunk0814

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4821702 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4821702 : Nat := 118140960795 + 4821702 * 2 ^ 59
def prefixEnd_4821702 : Nat := 4983230072969 + 3 ^ 40 * 4821702 * 2
def baseEnd_4821702 : Nat := 2475850698745199302450403

theorem tailTrace_4821702 : CollatzResearch.WordTrace tailWord_4821702 prefixEnd_4821702 2475850698745199302450403 := by
  unfold tailWord_4821702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495684986806394062063355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117241279718536406657351573 5495684986806394062063355)
  ·
    refine ⟨8243527480209591093095033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5495684986806394062063355 8243527480209591093095033)
    ·
      refine ⟨6182645610157193319821275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8243527480209591093095033 6182645610157193319821275)
      ·
        refine ⟨9273968415235789979731913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182645610157193319821275 9273968415235789979731913)
        ·
          refine ⟨6955476311426842484798935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9273968415235789979731913 6955476311426842484798935)
          ·
            refine ⟨10433214467140263727198403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955476311426842484798935 10433214467140263727198403)
            ·
              refine ⟨15649821700710395590797605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10433214467140263727198403 15649821700710395590797605)
              ·
                refine ⟨2934341568883199173274551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15649821700710395590797605 2934341568883199173274551)
                ·
                  refine ⟨4401512353324798759911827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934341568883199173274551 4401512353324798759911827)
                  ·
                    refine ⟨6602268529987198139867741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401512353324798759911827 6602268529987198139867741)
                    ·
                      refine ⟨2475850698745199302450403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6602268529987198139867741 2475850698745199302450403)
                      ·
                        rfl

theorem cell23_4821702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4821702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821702 prefixEnd_4821702 := by exact prefixLift 4821702
  have htrace : WordTrace (prefixWord ++ tailWord_4821702) baseStart_4821702 baseEnd_4821702 := by
    simpa [prefixWord, tailWord_4821702, baseEnd_4821702] using wordTrace_append hprefix tailTrace_4821702
  have hstable : (prefixWord ++ tailWord_4821702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821702).length < 2 ^ (prefixWord ++ tailWord_4821702).sum := by decide
  have hdescent : baseEnd_4821702 < baseStart_4821702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821714 : List Nat := [3, 2, 2, 2, 3, 2, 1, 8]
def baseStart_4821714 : Nat := 118140960795 + 4821714 * 2 ^ 59
def prefixEnd_4821714 : Nat := 4983230072969 + 3 ^ 40 * 4821714 * 2
def baseEnd_4821714 : Nat := 91698402241224194648161

theorem tailTrace_4821714 : CollatzResearch.WordTrace tailWord_4821714 prefixEnd_4821714 91698402241224194648161 := by
  unfold tailWord_4821714
  simp only [CollatzResearch.WordTrace]
  refine ⟨43965589313440284008866049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117241571502507424023642797 43965589313440284008866049)
  ·
    refine ⟨32974191985080213006649537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43965589313440284008866049 32974191985080213006649537)
    ·
      refine ⟨24730643988810159754987153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32974191985080213006649537 24730643988810159754987153)
      ·
        refine ⟨18547982991607619816240365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24730643988810159754987153 18547982991607619816240365)
        ·
          refine ⟨6955493621852857431090137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18547982991607619816240365 6955493621852857431090137)
          ·
            refine ⟨5216620216389643073317603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6955493621852857431090137 5216620216389643073317603)
            ·
              refine ⟨7824930324584464609976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216620216389643073317603 7824930324584464609976405)
              ·
                refine ⟨91698402241224194648161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7824930324584464609976405 91698402241224194648161)
                ·
                  rfl

theorem cell23_4821714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_4821714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821714 prefixEnd_4821714 := by exact prefixLift 4821714
  have htrace : WordTrace (prefixWord ++ tailWord_4821714) baseStart_4821714 baseEnd_4821714 := by
    simpa [prefixWord, tailWord_4821714, baseEnd_4821714] using wordTrace_append hprefix tailTrace_4821714
  have hstable : (prefixWord ++ tailWord_4821714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821714).length < 2 ^ (prefixWord ++ tailWord_4821714).sum := by decide
  have hdescent : baseEnd_4821714 < baseStart_4821714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821740 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_4821740 : Nat := 118140960795 + 4821740 * 2 ^ 59
def prefixEnd_4821740 : Nat := 4983230072969 + 3 ^ 40 * 4821740 * 2
def baseEnd_4821740 : Nat := 825290070336690051258409

theorem tailTrace_4821740 : CollatzResearch.WordTrace tailWord_4821740 prefixEnd_4821740 825290070336690051258409 := by
  unfold tailWord_4821740
  simp only [CollatzResearch.WordTrace]
  refine ⟨87931652775833471237955337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117242203701111294983940449 87931652775833471237955337)
  ·
    refine ⟨65948739581875103428466503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87931652775833471237955337 65948739581875103428466503)
    ·
      refine ⟨98923109372812655142699755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65948739581875103428466503 98923109372812655142699755)
      ·
        refine ⟨148384664059218982714049633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98923109372812655142699755 148384664059218982714049633)
        ·
          refine ⟨111288498044414237035537225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148384664059218982714049633 111288498044414237035537225)
          ·
            refine ⟨83466373533310677776652919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111288498044414237035537225 83466373533310677776652919)
            ·
              refine ⟨125199560299966016664979379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83466373533310677776652919 125199560299966016664979379)
              ·
                refine ⟨187799340449949024997469069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125199560299966016664979379 187799340449949024997469069)
                ·
                  refine ⟨70424752668730884374050901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187799340449949024997469069 70424752668730884374050901)
                  ·
                    refine ⟨825290070336690051258409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70424752668730884374050901 825290070336690051258409)
                    ·
                      rfl

theorem cell23_4821740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_4821740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821740 prefixEnd_4821740 := by exact prefixLift 4821740
  have htrace : WordTrace (prefixWord ++ tailWord_4821740) baseStart_4821740 baseEnd_4821740 := by
    simpa [prefixWord, tailWord_4821740, baseEnd_4821740] using wordTrace_append hprefix tailTrace_4821740
  have hstable : (prefixWord ++ tailWord_4821740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821740).length < 2 ^ (prefixWord ++ tailWord_4821740).sum := by decide
  have hdescent : baseEnd_4821740 < baseStart_4821740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821758 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4821758 : Nat := 118140960795 + 4821758 * 2 ^ 59
def prefixEnd_4821758 : Nat := 4983230072969 + 3 ^ 40 * 4821758 * 2
def baseEnd_4821758 : Nat := 2475879453661851083350145

theorem tailTrace_4821758 : CollatzResearch.WordTrace tailWord_4821758 prefixEnd_4821758 2475879453661851083350145 := by
  unfold tailWord_4821758
  simp only [CollatzResearch.WordTrace]
  refine ⟨21982995258200216443758241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117242641377067821033377285 21982995258200216443758241)
  ·
    refine ⟨16487246443650162332818681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21982995258200216443758241 16487246443650162332818681)
    ·
      refine ⟨12365434832737621749614011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16487246443650162332818681 12365434832737621749614011)
      ·
        refine ⟨18548152249106432624421017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12365434832737621749614011 18548152249106432624421017)
        ·
          refine ⟨13911114186829824468315763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18548152249106432624421017 13911114186829824468315763)
          ·
            refine ⟨20866671280244736702473645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911114186829824468315763 20866671280244736702473645)
            ·
              refine ⟨7825001730091776263427617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20866671280244736702473645 7825001730091776263427617)
              ·
                refine ⟨5868751297568832197570713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7825001730091776263427617 5868751297568832197570713)
                ·
                  refine ⟨4401563473176624148178035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5868751297568832197570713 4401563473176624148178035)
                  ·
                    refine ⟨6602345209764936222267053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401563473176624148178035 6602345209764936222267053)
                    ·
                      refine ⟨2475879453661851083350145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6602345209764936222267053 2475879453661851083350145)
                      ·
                        rfl

theorem cell23_4821758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4821758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821758 prefixEnd_4821758 := by exact prefixLift 4821758
  have htrace : WordTrace (prefixWord ++ tailWord_4821758) baseStart_4821758 baseEnd_4821758 := by
    simpa [prefixWord, tailWord_4821758, baseEnd_4821758] using wordTrace_append hprefix tailTrace_4821758
  have hstable : (prefixWord ++ tailWord_4821758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821758).length < 2 ^ (prefixWord ++ tailWord_4821758).sum := by decide
  have hdescent : baseEnd_4821758 < baseStart_4821758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821760 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_4821760 : Nat := 118140960795 + 4821760 * 2 ^ 59
def prefixEnd_4821760 : Nat := 4983230072969 + 3 ^ 40 * 4821760 * 2
def baseEnd_4821760 : Nat := 2475880480623160075525135

theorem tailTrace_4821760 : CollatzResearch.WordTrace tailWord_4821760 prefixEnd_4821760 2475880480623160075525135 := by
  unfold tailWord_4821760
  simp only [CollatzResearch.WordTrace]
  refine ⟨87932017505797242945819367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117242690007729657261092489 87932017505797242945819367)
  ·
    refine ⟨131898026258695864418729051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87932017505797242945819367 131898026258695864418729051)
    ·
      refine ⟨197847039388043796628093577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131898026258695864418729051 197847039388043796628093577)
      ·
        refine ⟨148385279541032847471070183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197847039388043796628093577 148385279541032847471070183)
        ·
          refine ⟨222577919311549271206605275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148385279541032847471070183 222577919311549271206605275)
          ·
            refine ⟨333866878967323906809907913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222577919311549271206605275 333866878967323906809907913)
            ·
              refine ⟨250400159225492930107430935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333866878967323906809907913 250400159225492930107430935)
              ·
                refine ⟨375600238838239395161146403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250400159225492930107430935 375600238838239395161146403)
                ·
                  refine ⟨563400358257359092741719605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375600238838239395161146403 563400358257359092741719605)
                  ·
                    refine ⟨52818783586627414944536213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 563400358257359092741719605 52818783586627414944536213)
                    ·
                      refine ⟨2475880480623160075525135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52818783586627414944536213 2475880480623160075525135)
                      ·
                        rfl

theorem cell23_4821760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_4821760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821760 prefixEnd_4821760 := by exact prefixLift 4821760
  have htrace : WordTrace (prefixWord ++ tailWord_4821760) baseStart_4821760 baseEnd_4821760 := by
    simpa [prefixWord, tailWord_4821760, baseEnd_4821760] using wordTrace_append hprefix tailTrace_4821760
  have hstable : (prefixWord ++ tailWord_4821760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821760).length < 2 ^ (prefixWord ++ tailWord_4821760).sum := by decide
  have hdescent : baseEnd_4821760 < baseStart_4821760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821777 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_4821777 : Nat := 118140960795 + 4821777 * 2 ^ 59
def prefixEnd_4821777 : Nat := 4983230072969 + 3 ^ 40 * 4821777 * 2
def baseEnd_4821777 : Nat := 2475889209794286509012557

theorem tailTrace_4821777 : CollatzResearch.WordTrace tailWord_4821777 prefixEnd_4821777 2475889209794286509012557 := by
  unfold tailWord_4821777
  simp only [CollatzResearch.WordTrace]
  refine ⟨175864655052532897795007585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117243103368355265196671723 175864655052532897795007585)
  ·
    refine ⟨131898491289399673346255689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175864655052532897795007585 131898491289399673346255689)
    ·
      refine ⟨98923868467049755009691767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131898491289399673346255689 98923868467049755009691767)
      ·
        refine ⟨148385802700574632514537651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98923868467049755009691767 148385802700574632514537651)
        ·
          refine ⟨222578704050861948771806477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148385802700574632514537651 222578704050861948771806477)
          ·
            refine ⟨83467014019073230789427429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222578704050861948771806477 83467014019073230789427429)
            ·
              refine ⟨15650065128576230773017643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83467014019073230789427429 15650065128576230773017643)
              ·
                refine ⟨23475097692864346159526465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15650065128576230773017643 23475097692864346159526465)
                ·
                  refine ⟨17606323269648259619644849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23475097692864346159526465 17606323269648259619644849)
                  ·
                    refine ⟨13204742452236194714733637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17606323269648259619644849 13204742452236194714733637)
                    ·
                      refine ⟨2475889209794286509012557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13204742452236194714733637 2475889209794286509012557)
                      ·
                        rfl

theorem cell23_4821777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_4821777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821777 prefixEnd_4821777 := by exact prefixLift 4821777
  have htrace : WordTrace (prefixWord ++ tailWord_4821777) baseStart_4821777 baseEnd_4821777 := by
    simpa [prefixWord, tailWord_4821777, baseEnd_4821777] using wordTrace_append hprefix tailTrace_4821777
  have hstable : (prefixWord ++ tailWord_4821777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821777).length < 2 ^ (prefixWord ++ tailWord_4821777).sum := by decide
  have hdescent : baseEnd_4821777 < baseStart_4821777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821821 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 7]
def baseStart_4821821 : Nat := 118140960795 + 4821821 * 2 ^ 59
def prefixEnd_4821821 : Nat := 4983230072969 + 3 ^ 40 * 4821821 * 2
def baseEnd_4821821 : Nat := 275101311438120481873595

theorem tailTrace_4821821 : CollatzResearch.WordTrace tailWord_4821821 prefixEnd_4821821 275101311438120481873595 := by
  unfold tailWord_4821821
  simp only [CollatzResearch.WordTrace]
  refine ⟨175866259864373493309609317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117244173242915662206406211 175866259864373493309609317)
  ·
    refine ⟨32974923724570029995551747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175866259864373493309609317 32974923724570029995551747)
    ·
      refine ⟨49462385586855044993327621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32974923724570029995551747 49462385586855044993327621)
      ·
        refine ⟨9274197297535320936248929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49462385586855044993327621 9274197297535320936248929)
        ·
          refine ⟨6955647973151490702186697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9274197297535320936248929 6955647973151490702186697)
          ·
            refine ⟨5216735979863618026640023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6955647973151490702186697 5216735979863618026640023)
            ·
              refine ⟨7825103969795427039960035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216735979863618026640023 7825103969795427039960035)
              ·
                refine ⟨11737655954693140559940053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7825103969795427039960035 11737655954693140559940053)
                ·
                  refine ⟨275101311438120481873595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11737655954693140559940053 275101311438120481873595)
                  ·
                    rfl

theorem cell23_4821821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_4821821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821821 prefixEnd_4821821 := by exact prefixLift 4821821
  have htrace : WordTrace (prefixWord ++ tailWord_4821821) baseStart_4821821 baseEnd_4821821 := by
    simpa [prefixWord, tailWord_4821821, baseEnd_4821821] using wordTrace_append hprefix tailTrace_4821821
  have hstable : (prefixWord ++ tailWord_4821821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821821).length < 2 ^ (prefixWord ++ tailWord_4821821).sum := by decide
  have hdescent : baseEnd_4821821 < baseStart_4821821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821827 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5]
def baseStart_4821827 : Nat := 118140960795 + 4821827 * 2 ^ 59
def prefixEnd_4821827 : Nat := 4983230072969 + 3 ^ 40 * 4821827 * 2
def baseEnd_4821827 : Nat := 2475914883827011313387327

theorem tailTrace_4821827 : CollatzResearch.WordTrace tailWord_4821827 prefixEnd_4821827 2475914883827011313387327 := by
  unfold tailWord_4821827
  simp only [CollatzResearch.WordTrace]
  refine ⟨175866478702351756334327735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117244319134901170889551823 175866478702351756334327735)
  ·
    refine ⟨263799718053527634501491603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175866478702351756334327735 263799718053527634501491603)
    ·
      refine ⟨395699577080291451752237405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263799718053527634501491603 395699577080291451752237405)
      ·
        refine ⟨148387341405109294407089027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395699577080291451752237405 148387341405109294407089027)
        ·
          refine ⟨222581012107663941610633541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148387341405109294407089027 222581012107663941610633541)
          ·
            refine ⟨41733939770186989051993789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222581012107663941610633541 41733939770186989051993789)
            ·
              refine ⟨15650227413820120894497671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41733939770186989051993789 15650227413820120894497671)
              ·
                refine ⟨23475341120730181341746507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15650227413820120894497671 23475341120730181341746507)
                ·
                  refine ⟨35213011681095272012619761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23475341120730181341746507 35213011681095272012619761)
                  ·
                    refine ⟨26409758760821454009464821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35213011681095272012619761 26409758760821454009464821)
                    ·
                      refine ⟨2475914883827011313387327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26409758760821454009464821 2475914883827011313387327)
                      ·
                        rfl

theorem cell23_4821827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_4821827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821827 prefixEnd_4821827 := by exact prefixLift 4821827
  have htrace : WordTrace (prefixWord ++ tailWord_4821827) baseStart_4821827 baseEnd_4821827 := by
    simpa [prefixWord, tailWord_4821827, baseEnd_4821827] using wordTrace_append hprefix tailTrace_4821827
  have hstable : (prefixWord ++ tailWord_4821827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821827).length < 2 ^ (prefixWord ++ tailWord_4821827).sum := by decide
  have hdescent : baseEnd_4821827 < baseStart_4821827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821947 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_4821947 : Nat := 118140960795 + 4821947 * 2 ^ 59
def prefixEnd_4821947 : Nat := 4983230072969 + 3 ^ 40 * 4821947 * 2
def baseEnd_4821947 : Nat := 2475976501505550843886775

theorem tailTrace_4821947 : CollatzResearch.WordTrace tailWord_4821947 prefixEnd_4821947 2475976501505550843886775 := by
  unfold tailWord_4821947
  simp only [CollatzResearch.WordTrace]
  refine ⟨175870855461917016828696095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117247236974611344552464063 175870855461917016828696095)
  ·
    refine ⟨263806283192875525243044143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175870855461917016828696095 263806283192875525243044143)
    ·
      refine ⟨395709424789313287864566215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263806283192875525243044143 395709424789313287864566215)
      ·
        refine ⟨593564137183969931796849323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395709424789313287864566215 593564137183969931796849323)
        ·
          refine ⟨890346205775954897695273985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593564137183969931796849323 890346205775954897695273985)
          ·
            refine ⟨667759654331966173271455489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890346205775954897695273985 667759654331966173271455489)
            ·
              refine ⟨500819740748974629953591617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667759654331966173271455489 500819740748974629953591617)
              ·
                refine ⟨375614805561730972465193713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500819740748974629953591617 375614805561730972465193713)
                ·
                  refine ⟨281711104171298229348895285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375614805561730972465193713 281711104171298229348895285)
                  ·
                    refine ⟨26410416016059209001458933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 281711104171298229348895285 26410416016059209001458933)
                    ·
                      refine ⟨2475976501505550843886775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26410416016059209001458933 2475976501505550843886775)
                      ·
                        rfl

theorem cell23_4821947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_4821947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821947 prefixEnd_4821947 := by exact prefixLift 4821947
  have htrace : WordTrace (prefixWord ++ tailWord_4821947) baseStart_4821947 baseEnd_4821947 := by
    simpa [prefixWord, tailWord_4821947, baseEnd_4821947] using wordTrace_append hprefix tailTrace_4821947
  have hstable : (prefixWord ++ tailWord_4821947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821947).length < 2 ^ (prefixWord ++ tailWord_4821947).sum := by decide
  have hdescent : baseEnd_4821947 < baseStart_4821947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821964 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4821964 : Nat := 118140960795 + 4821964 * 2 ^ 59
def prefixEnd_4821964 : Nat := 4983230072969 + 3 ^ 40 * 4821964 * 2
def baseEnd_4821964 : Nat := 2475985230676677277374197

theorem tailTrace_4821964 : CollatzResearch.WordTrace tailWord_4821964 prefixEnd_4821964 2475985230676677277374197 := by
  unfold tailWord_4821964
  simp only [CollatzResearch.WordTrace]
  refine ⟨87935737751427714366032473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117247650335236952488043297 87935737751427714366032473)
  ·
    refine ⟨65951803313570785774524355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87935737751427714366032473 65951803313570785774524355)
    ·
      refine ⟨98927704970356178661786533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65951803313570785774524355 98927704970356178661786533)
      ·
        refine ⟨18548944681941783499084975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98927704970356178661786533 18548944681941783499084975)
        ·
          refine ⟨27823417022912675248627463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18548944681941783499084975 27823417022912675248627463)
          ·
            refine ⟨41735125534369012872941195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27823417022912675248627463 41735125534369012872941195)
            ·
              refine ⟨62602688301553519309411793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41735125534369012872941195 62602688301553519309411793)
              ·
                refine ⟨46952016226165139482058845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62602688301553519309411793 46952016226165139482058845)
                ·
                  refine ⟨17607006084811927305772067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46952016226165139482058845 17607006084811927305772067)
                  ·
                    refine ⟨26410509127217890958658101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17607006084811927305772067 26410509127217890958658101)
                    ·
                      refine ⟨2475985230676677277374197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26410509127217890958658101 2475985230676677277374197)
                      ·
                        rfl

theorem cell23_4821964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4821964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821964 prefixEnd_4821964 := by exact prefixLift 4821964
  have htrace : WordTrace (prefixWord ++ tailWord_4821964) baseStart_4821964 baseEnd_4821964 := by
    simpa [prefixWord, tailWord_4821964, baseEnd_4821964] using wordTrace_append hprefix tailTrace_4821964
  have hstable : (prefixWord ++ tailWord_4821964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821964).length < 2 ^ (prefixWord ++ tailWord_4821964).sum := by decide
  have hdescent : baseEnd_4821964 < baseStart_4821964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821972 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_4821972 : Nat := 118140960795 + 4821972 * 2 ^ 59
def prefixEnd_4821972 : Nat := 4983230072969 + 3 ^ 40 * 4821972 * 2
def baseEnd_4821972 : Nat := 2475989338521913246074161

theorem tailTrace_4821972 : CollatzResearch.WordTrace tailWord_4821972 prefixEnd_4821972 2475989338521913246074161 := by
  unfold tailWord_4821972
  simp only [CollatzResearch.WordTrace]
  refine ⟨87935883643413223049178085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117247844857884297398904113 87935883643413223049178085)
  ·
    refine ⟨16487978183139979321720891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87935883643413223049178085 16487978183139979321720891)
    ·
      refine ⟨24731967274709968982581337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16487978183139979321720891 24731967274709968982581337)
      ·
        refine ⟨18548975456032476736936003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24731967274709968982581337 18548975456032476736936003)
        ·
          refine ⟨27823463184048715105404005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18548975456032476736936003 27823463184048715105404005)
          ·
            refine ⟨5216899347009134082263251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27823463184048715105404005 5216899347009134082263251)
            ·
              refine ⟨7825349020513701123394877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216899347009134082263251 7825349020513701123394877)
              ·
                refine ⟨2934505882692637921273079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7825349020513701123394877 2934505882692637921273079)
                ·
                  refine ⟨4401758824038956881909619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934505882692637921273079 4401758824038956881909619)
                  ·
                    refine ⟨6602638236058435322864429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401758824038956881909619 6602638236058435322864429)
                    ·
                      refine ⟨2475989338521913246074161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6602638236058435322864429 2475989338521913246074161)
                      ·
                        rfl

theorem cell23_4821972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_4821972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821972 prefixEnd_4821972 := by exact prefixLift 4821972
  have htrace : WordTrace (prefixWord ++ tailWord_4821972) baseStart_4821972 baseEnd_4821972 := by
    simpa [prefixWord, tailWord_4821972, baseEnd_4821972] using wordTrace_append hprefix tailTrace_4821972
  have hstable : (prefixWord ++ tailWord_4821972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821972).length < 2 ^ (prefixWord ++ tailWord_4821972).sum := by decide
  have hdescent : baseEnd_4821972 < baseStart_4821972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821981 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4821981 : Nat := 118140960795 + 4821981 * 2 ^ 59
def prefixEnd_4821981 : Nat := 4983230072969 + 3 ^ 40 * 4821981 * 2
def baseEnd_4821981 : Nat := 2475993959847803710861619

theorem tailTrace_4821981 : CollatzResearch.WordTrace tailWord_4821981 prefixEnd_4821981 2475993959847803710861619 := by
  unfold tailWord_4821981
  simp only [CollatzResearch.WordTrace]
  refine ⟨175872095543793840635433797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117248063695862560423622531 175872095543793840635433797)
  ·
    refine ⟨32976017914461345119143837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175872095543793840635433797 32976017914461345119143837)
    ·
      refine ⟨12366006717923004419678939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32976017914461345119143837 12366006717923004419678939)
      ·
        refine ⟨18549010076884506629518409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12366006717923004419678939 18549010076884506629518409)
        ·
          refine ⟨13911757557663379972138807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18549010076884506629518409 13911757557663379972138807)
          ·
            refine ⟨20867636336495069958208211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911757557663379972138807 20867636336495069958208211)
            ·
              refine ⟨31301454504742604937312317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20867636336495069958208211 31301454504742604937312317)
              ·
                refine ⟨11738045439278476851492119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31301454504742604937312317 11738045439278476851492119)
                ·
                  refine ⟨17607068158917715277238179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11738045439278476851492119 17607068158917715277238179)
                  ·
                    refine ⟨26410602238376572915857269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17607068158917715277238179 26410602238376572915857269)
                    ·
                      refine ⟨2475993959847803710861619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26410602238376572915857269 2475993959847803710861619)
                      ·
                        rfl

theorem cell23_4821981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4821981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821981 prefixEnd_4821981 := by exact prefixLift 4821981
  have htrace : WordTrace (prefixWord ++ tailWord_4821981) baseStart_4821981 baseEnd_4821981 := by
    simpa [prefixWord, tailWord_4821981, baseEnd_4821981] using wordTrace_append hprefix tailTrace_4821981
  have hstable : (prefixWord ++ tailWord_4821981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821981).length < 2 ^ (prefixWord ++ tailWord_4821981).sum := by decide
  have hdescent : baseEnd_4821981 < baseStart_4821981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4821989 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4821989 : Nat := 118140960795 + 4821989 * 2 ^ 59
def prefixEnd_4821989 : Nat := 4983230072969 + 3 ^ 40 * 4821989 * 2
def baseEnd_4821989 : Nat := 2475998067693039679561583

theorem tailTrace_4821989 : CollatzResearch.WordTrace tailWord_4821989 prefixEnd_4821989 2475998067693039679561583 := by
  unfold tailWord_4821989
  simp only [CollatzResearch.WordTrace]
  refine ⟨175872387327764858001725021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117248258218509905334483347 175872387327764858001725021)
  ·
    refine ⟨65952145247911821750646883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175872387327764858001725021 65952145247911821750646883)
    ·
      refine ⟨98928217871867732625970325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65952145247911821750646883 98928217871867732625970325)
      ·
        refine ⟨4637260212743799966842359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98928217871867732625970325 4637260212743799966842359)
        ·
          refine ⟨6955890319115699950263539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637260212743799966842359 6955890319115699950263539)
          ·
            refine ⟨10433835478673549925395309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955890319115699950263539 10433835478673549925395309)
            ·
              refine ⟨3912688304502581222023241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10433835478673549925395309 3912688304502581222023241)
              ·
                refine ⟨2934516228376935916517431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3912688304502581222023241 2934516228376935916517431)
                ·
                  refine ⟨4401774342565403874776147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934516228376935916517431 4401774342565403874776147)
                  ·
                    refine ⟨6602661513848105812164221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401774342565403874776147 6602661513848105812164221)
                    ·
                      refine ⟨2475998067693039679561583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6602661513848105812164221 2475998067693039679561583)
                      ·
                        rfl

theorem cell23_4821989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4821989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4821989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4821989 prefixEnd_4821989 := by exact prefixLift 4821989
  have htrace : WordTrace (prefixWord ++ tailWord_4821989) baseStart_4821989 baseEnd_4821989 := by
    simpa [prefixWord, tailWord_4821989, baseEnd_4821989] using wordTrace_append hprefix tailTrace_4821989
  have hstable : (prefixWord ++ tailWord_4821989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4821989).length < 2 ^ (prefixWord ++ tailWord_4821989).sum := by decide
  have hdescent : baseEnd_4821989 < baseStart_4821989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4821989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822055 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4822055 : Nat := 118140960795 + 4822055 * 2 ^ 59
def prefixEnd_4822055 : Nat := 4983230072969 + 3 ^ 40 * 4822055 * 2
def baseEnd_4822055 : Nat := 2476031957416236421336279

theorem tailTrace_4822055 : CollatzResearch.WordTrace tailWord_4822055 prefixEnd_4822055 2476031957416236421336279 := by
  unfold tailWord_4822055
  simp only [CollatzResearch.WordTrace]
  refine ⟨175874794545525751273627619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117249863030350500849085079 175874794545525751273627619)
  ·
    refine ⟨263812191818288626910441429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175874794545525751273627619 263812191818288626910441429)
    ·
      refine ⟨6183098245741139693213471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 263812191818288626910441429 6183098245741139693213471)
      ·
        refine ⟨9274647368611709539820207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183098245741139693213471 9274647368611709539820207)
        ·
          refine ⟨13911971052917564309730311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9274647368611709539820207 13911971052917564309730311)
          ·
            refine ⟨20867956579376346464595467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911971052917564309730311 20867956579376346464595467)
            ·
              refine ⟨31301934869064519696893201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20867956579376346464595467 31301934869064519696893201)
              ·
                refine ⟨23476451151798389772669901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31301934869064519696893201 23476451151798389772669901)
                ·
                  refine ⟨8803669181924396164751213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23476451151798389772669901 8803669181924396164751213)
                  ·
                    refine ⟨3301375943221648561781705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8803669181924396164751213 3301375943221648561781705)
                    ·
                      refine ⟨2476031957416236421336279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301375943221648561781705 2476031957416236421336279)
                      ·
                        rfl

theorem cell23_4822055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4822055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822055 prefixEnd_4822055 := by exact prefixLift 4822055
  have htrace : WordTrace (prefixWord ++ tailWord_4822055) baseStart_4822055 baseEnd_4822055 := by
    simpa [prefixWord, tailWord_4822055, baseEnd_4822055] using wordTrace_append hprefix tailTrace_4822055
  have hstable : (prefixWord ++ tailWord_4822055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822055).length < 2 ^ (prefixWord ++ tailWord_4822055).sum := by decide
  have hdescent : baseEnd_4822055 < baseStart_4822055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822074 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_4822074 : Nat := 118140960795 + 4822074 * 2 ^ 59
def prefixEnd_4822074 : Nat := 4983230072969 + 3 ^ 40 * 4822074 * 2
def baseEnd_4822074 : Nat := 275115745949852427444299

theorem tailTrace_4822074 : CollatzResearch.WordTrace tailWord_4822074 prefixEnd_4822074 275115745949852427444299 := by
  unfold tailWord_4822074
  simp only [CollatzResearch.WordTrace]
  refine ⟨43968871883114229379642319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117250325021637945012379517 43968871883114229379642319)
  ·
    refine ⟨65953307824671344069463479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43968871883114229379642319 65953307824671344069463479)
    ·
      refine ⟨98929961737007016104195219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65953307824671344069463479 98929961737007016104195219)
      ·
        refine ⟨148394942605510524156292829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98929961737007016104195219 148394942605510524156292829)
        ·
          refine ⟨55648103477066446558609811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148394942605510524156292829 55648103477066446558609811)
          ·
            refine ⟨83472155215599669837914717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55648103477066446558609811 83472155215599669837914717)
            ·
              refine ⟨31302058205849876189218019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83472155215599669837914717 31302058205849876189218019)
              ·
                refine ⟨46953087308774814283827029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31302058205849876189218019 46953087308774814283827029)
                ·
                  refine ⟨275115745949852427444299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46953087308774814283827029 275115745949852427444299)
                  ·
                    rfl

theorem cell23_4822074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_4822074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822074 prefixEnd_4822074 := by exact prefixLift 4822074
  have htrace : WordTrace (prefixWord ++ tailWord_4822074) baseStart_4822074 baseEnd_4822074 := by
    simpa [prefixWord, tailWord_4822074, baseEnd_4822074] using wordTrace_append hprefix tailTrace_4822074
  have hstable : (prefixWord ++ tailWord_4822074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822074).length < 2 ^ (prefixWord ++ tailWord_4822074).sum := by decide
  have hdescent : baseEnd_4822074 < baseStart_4822074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822101 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_4822101 : Nat := 118140960795 + 4822101 * 2 ^ 59
def prefixEnd_4822101 : Nat := 4983230072969 + 3 ^ 40 * 4822101 * 2
def baseEnd_4822101 : Nat := 2476055577526343241361067

theorem tailTrace_4822101 : CollatzResearch.WordTrace tailWord_4822101 prefixEnd_4822101 2476055577526343241361067 := by
  unfold tailWord_4822101
  simp only [CollatzResearch.WordTrace]
  refine ⟨175876472303359101129802157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117250981535572734086534771 175876472303359101129802157)
  ·
    refine ⟨65953677113759662923675809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175876472303359101129802157 65953677113759662923675809)
    ·
      refine ⟨49465257835319747192756857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65953677113759662923675809 49465257835319747192756857)
      ·
        refine ⟨37098943376489810394567643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49465257835319747192756857 37098943376489810394567643)
        ·
          refine ⟨55648415064734715591851465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37098943376489810394567643 55648415064734715591851465)
          ·
            refine ⟨41736311298551036693888599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55648415064734715591851465 41736311298551036693888599)
            ·
              refine ⟨62604466947826555040832899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41736311298551036693888599 62604466947826555040832899)
              ·
                refine ⟨93906700421739832561249349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62604466947826555040832899 93906700421739832561249349)
                ·
                  refine ⟨17607506329076218605234253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93906700421739832561249349 17607506329076218605234253)
                  ·
                    refine ⟨6602814873403581976962845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17607506329076218605234253 6602814873403581976962845)
                    ·
                      refine ⟨2476055577526343241361067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6602814873403581976962845 2476055577526343241361067)
                      ·
                        rfl

theorem cell23_4822101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_4822101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822101 prefixEnd_4822101 := by exact prefixLift 4822101
  have htrace : WordTrace (prefixWord ++ tailWord_4822101) baseStart_4822101 baseEnd_4822101 := by
    simpa [prefixWord, tailWord_4822101, baseEnd_4822101] using wordTrace_append hprefix tailTrace_4822101
  have hstable : (prefixWord ++ tailWord_4822101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822101).length < 2 ^ (prefixWord ++ tailWord_4822101).sum := by decide
  have hdescent : baseEnd_4822101 < baseStart_4822101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822108 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 5]
def baseStart_4822108 : Nat := 118140960795 + 4822108 * 2 ^ 59
def prefixEnd_4822108 : Nat := 4983230072969 + 3 ^ 40 * 4822108 * 2
def baseEnd_4822108 : Nat := 275117685765658301552615

theorem tailTrace_4822108 : CollatzResearch.WordTrace tailWord_4822108 prefixEnd_4822108 275117685765658301552615 := by
  unfold tailWord_4822108
  simp only [CollatzResearch.WordTrace]
  refine ⟨87938363807166870662653489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117251151742889160883537985 87938363807166870662653489)
  ·
    refine ⟨65953772855375152996990117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87938363807166870662653489 65953772855375152996990117)
    ·
      refine ⟨12366332410382841186935647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65953772855375152996990117 12366332410382841186935647)
      ·
        refine ⟨18549498615574261780403471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12366332410382841186935647 18549498615574261780403471)
        ·
          refine ⟨27824247923361392670605207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18549498615574261780403471 27824247923361392670605207)
          ·
            refine ⟨41736371885042089005907811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27824247923361392670605207 41736371885042089005907811)
            ·
              refine ⟨62604557827563133508861717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41736371885042089005907811 62604557827563133508861717)
              ·
                refine ⟨2934588648167021883227893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62604557827563133508861717 2934588648167021883227893)
                ·
                  refine ⟨275117685765658301552615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2934588648167021883227893 275117685765658301552615)
                  ·
                    rfl

theorem cell23_4822108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_4822108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822108 prefixEnd_4822108 := by exact prefixLift 4822108
  have htrace : WordTrace (prefixWord ++ tailWord_4822108) baseStart_4822108 baseEnd_4822108 := by
    simpa [prefixWord, tailWord_4822108, baseEnd_4822108] using wordTrace_append hprefix tailTrace_4822108
  have hstable : (prefixWord ++ tailWord_4822108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822108).length < 2 ^ (prefixWord ++ tailWord_4822108).sum := by decide
  have hdescent : baseEnd_4822108 < baseStart_4822108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822141 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4822141 : Nat := 118140960795 + 4822141 * 2 ^ 59
def prefixEnd_4822141 : Nat := 4983230072969 + 3 ^ 40 * 4822141 * 2
def baseEnd_4822141 : Nat := 2476076116752523084860883

theorem tailTrace_4822141 : CollatzResearch.WordTrace tailWord_4822141 prefixEnd_4822141 2476076116752523084860883 := by
  unfold tailWord_4822141
  simp only [CollatzResearch.WordTrace]
  refine ⟨175877931223214187961258277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117251954148809458640838851 175877931223214187961258277)
  ·
    refine ⟨32977112104352660242735927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175877931223214187961258277 32977112104352660242735927)
    ·
      refine ⟨49465668156528990364103891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32977112104352660242735927 49465668156528990364103891)
      ·
        refine ⟨74198502234793485546155837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49465668156528990364103891 74198502234793485546155837)
        ·
          refine ⟨27824438338047557079808439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74198502234793485546155837 27824438338047557079808439)
          ·
            refine ⟨41736657507071335619712659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27824438338047557079808439 41736657507071335619712659)
            ·
              refine ⟨62604986260607003429568989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41736657507071335619712659 62604986260607003429568989)
              ·
                refine ⟨23476869847727626286088371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62604986260607003429568989 23476869847727626286088371)
                ·
                  refine ⟨35215304771591439429132557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23476869847727626286088371 35215304771591439429132557)
                  ·
                    refine ⟨13205739289346789785924709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35215304771591439429132557 13205739289346789785924709)
                    ·
                      refine ⟨2476076116752523084860883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13205739289346789785924709 2476076116752523084860883)
                      ·
                        rfl

theorem cell23_4822141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4822141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822141 prefixEnd_4822141 := by exact prefixLift 4822141
  have htrace : WordTrace (prefixWord ++ tailWord_4822141) baseStart_4822141 baseEnd_4822141 := by
    simpa [prefixWord, tailWord_4822141, baseEnd_4822141] using wordTrace_append hprefix tailTrace_4822141
  have hstable : (prefixWord ++ tailWord_4822141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822141).length < 2 ^ (prefixWord ++ tailWord_4822141).sum := by decide
  have hdescent : baseEnd_4822141 < baseStart_4822141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822158 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_4822158 : Nat := 118140960795 + 4822158 * 2 ^ 59
def prefixEnd_4822158 : Nat := 4983230072969 + 3 ^ 40 * 4822158 * 2
def baseEnd_4822158 : Nat := 2476084845923649518348305

theorem tailTrace_4822158 : CollatzResearch.WordTrace tailWord_4822158 prefixEnd_4822158 2476084845923649518348305 := by
  unfold tailWord_4822158
  simp only [CollatzResearch.WordTrace]
  refine ⟨21984818908019074983078391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117252367509435066576418085 21984818908019074983078391)
  ·
    refine ⟨32977228362028612474617587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21984818908019074983078391 32977228362028612474617587)
    ·
      refine ⟨49465842543042918711926381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32977228362028612474617587 49465842543042918711926381)
      ·
        refine ⟨18549690953641094516972393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49465842543042918711926381 18549690953641094516972393)
        ·
          refine ⟨13912268215230820887729295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18549690953641094516972393 13912268215230820887729295)
          ·
            refine ⟨20868402322846231331593943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13912268215230820887729295 20868402322846231331593943)
            ·
              refine ⟨31302603484269346997390915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20868402322846231331593943 31302603484269346997390915)
              ·
                refine ⟨46953905226404020496086373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31302603484269346997390915 46953905226404020496086373)
                ·
                  refine ⟨8803857229950753843016195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46953905226404020496086373 8803857229950753843016195)
                  ·
                    refine ⟨13205785844926130764524293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8803857229950753843016195 13205785844926130764524293)
                    ·
                      refine ⟨2476084845923649518348305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13205785844926130764524293 2476084845923649518348305)
                      ·
                        rfl

theorem cell23_4822158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_4822158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822158 prefixEnd_4822158 := by exact prefixLift 4822158
  have htrace : WordTrace (prefixWord ++ tailWord_4822158) baseStart_4822158 baseEnd_4822158 := by
    simpa [prefixWord, tailWord_4822158, baseEnd_4822158] using wordTrace_append hprefix tailTrace_4822158
  have hstable : (prefixWord ++ tailWord_4822158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822158).length < 2 ^ (prefixWord ++ tailWord_4822158).sum := by decide
  have hdescent : baseEnd_4822158 < baseStart_4822158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822191 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 3]
def baseStart_4822191 : Nat := 118140960795 + 4822191 * 2 ^ 59
def prefixEnd_4822191 : Nat := 4983230072969 + 3 ^ 40 * 4822191 * 2
def baseEnd_4822191 : Nat := 2476101790785247889235653

theorem tailTrace_4822191 : CollatzResearch.WordTrace tailWord_4822191 prefixEnd_4822191 2476101790785247889235653 := by
  unfold tailWord_4822191
  simp only [CollatzResearch.WordTrace]
  refine ⟨175879754873033046500578427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117253169915355364333718951 175879754873033046500578427)
  ·
    refine ⟨263819632309549569750867641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175879754873033046500578427 263819632309549569750867641)
    ·
      refine ⟨197864724232162177313150731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263819632309549569750867641 197864724232162177313150731)
      ·
        refine ⟨296797086348243265969726097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197864724232162177313150731 296797086348243265969726097)
        ·
          refine ⟨222597814761182449477294573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296797086348243265969726097 222597814761182449477294573)
          ·
            refine ⟨83474180535443418553985465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222597814761182449477294573 83474180535443418553985465)
            ·
              refine ⟨62605635401582563915489099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83474180535443418553985465 62605635401582563915489099)
              ·
                refine ⟨93908453102373845873233649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62605635401582563915489099 93908453102373845873233649)
                ·
                  refine ⟨70431339826780384404925237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93908453102373845873233649 70431339826780384404925237)
                  ·
                    refine ⟨6602938108760661037961741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70431339826780384404925237 6602938108760661037961741)
                    ·
                      refine ⟨2476101790785247889235653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6602938108760661037961741 2476101790785247889235653)
                      ·
                        rfl

theorem cell23_4822191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_4822191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822191 prefixEnd_4822191 := by exact prefixLift 4822191
  have htrace : WordTrace (prefixWord ++ tailWord_4822191) baseStart_4822191 baseEnd_4822191 := by
    simpa [prefixWord, tailWord_4822191, baseEnd_4822191] using wordTrace_append hprefix tailTrace_4822191
  have hstable : (prefixWord ++ tailWord_4822191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822191).length < 2 ^ (prefixWord ++ tailWord_4822191).sum := by decide
  have hdescent : baseEnd_4822191 < baseStart_4822191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822248 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4822248 : Nat := 118140960795 + 4822248 * 2 ^ 59
def prefixEnd_4822248 : Nat := 4983230072969 + 3 ^ 40 * 4822248 * 2
def baseEnd_4822248 : Nat := 2476131059182554166222891

theorem tailTrace_4822248 : CollatzResearch.WordTrace tailWord_4822248 prefixEnd_4822248 2476131059182554166222891 := by
  unfold tailWord_4822248
  simp only [CollatzResearch.WordTrace]
  refine ⟨87940916916913272617701699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117254555889217696823602265 87940916916913272617701699)
  ·
    refine ⟨131911375375369908926552549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87940916916913272617701699 131911375375369908926552549)
    ·
      refine ⟨24733382882881857923728603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131911375375369908926552549 24733382882881857923728603)
      ·
        refine ⟨37100074324322786885592905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24733382882881857923728603 37100074324322786885592905)
        ·
          refine ⟨27825055743242090164194679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37100074324322786885592905 27825055743242090164194679)
          ·
            refine ⟨41737583614863135246292019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27825055743242090164194679 41737583614863135246292019)
            ·
              refine ⟨62606375422294702869438029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41737583614863135246292019 62606375422294702869438029)
              ·
                refine ⟨23477390783360513576039261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62606375422294702869438029 23477390783360513576039261)
                ·
                  refine ⟨8804021543760192591014723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23477390783360513576039261 8804021543760192591014723)
                  ·
                    refine ⟨13206032315640288886522085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8804021543760192591014723 13206032315640288886522085)
                    ·
                      refine ⟨2476131059182554166222891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13206032315640288886522085 2476131059182554166222891)
                      ·
                        rfl

theorem cell23_4822248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4822248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822248 prefixEnd_4822248 := by exact prefixLift 4822248
  have htrace : WordTrace (prefixWord ++ tailWord_4822248) baseStart_4822248 baseEnd_4822248 := by
    simpa [prefixWord, tailWord_4822248, baseEnd_4822248] using wordTrace_append hprefix tailTrace_4822248
  have hstable : (prefixWord ++ tailWord_4822248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822248).length < 2 ^ (prefixWord ++ tailWord_4822248).sum := by decide
  have hdescent : baseEnd_4822248 < baseStart_4822248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822252 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 2, 3, 2]
def baseStart_4822252 : Nat := 118140960795 + 4822252 * 2 ^ 59
def prefixEnd_4822252 : Nat := 4983230072969 + 3 ^ 40 * 4822252 * 2
def baseEnd_4822252 : Nat := 2476133113105172150572873

theorem tailTrace_4822252 : CollatzResearch.WordTrace tailWord_4822252 prefixEnd_4822252 2476133113105172150572873 := by
  unfold tailWord_4822252
  simp only [CollatzResearch.WordTrace]
  refine ⟨87940989862906026959274505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117254653150541369279032673 87940989862906026959274505)
  ·
    refine ⟨65955742397179520219455879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87940989862906026959274505 65955742397179520219455879)
    ·
      refine ⟨98933613595769280329183819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65955742397179520219455879 98933613595769280329183819)
      ·
        refine ⟨148400420393653920493775729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98933613595769280329183819 148400420393653920493775729)
        ·
          refine ⟨111300315295240440370331797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148400420393653920493775729 111300315295240440370331797)
          ·
            refine ⟨5217202279464395642359303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111300315295240440370331797 5217202279464395642359303)
            ·
              refine ⟨7825803419196593463538955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217202279464395642359303 7825803419196593463538955)
              ·
                refine ⟨11738705128794890195308433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7825803419196593463538955 11738705128794890195308433)
                ·
                  refine ⟨8804028846596167646481325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11738705128794890195308433 8804028846596167646481325)
                  ·
                    refine ⟨3301510817473562867430497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8804028846596167646481325 3301510817473562867430497)
                    ·
                      refine ⟨2476133113105172150572873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301510817473562867430497 2476133113105172150572873)
                      ·
                        rfl

theorem cell23_4822252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_4822252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822252 prefixEnd_4822252 := by exact prefixLift 4822252
  have htrace : WordTrace (prefixWord ++ tailWord_4822252) baseStart_4822252 baseEnd_4822252 := by
    simpa [prefixWord, tailWord_4822252, baseEnd_4822252] using wordTrace_append hprefix tailTrace_4822252
  have hstable : (prefixWord ++ tailWord_4822252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822252).length < 2 ^ (prefixWord ++ tailWord_4822252).sum := by decide
  have hdescent : baseEnd_4822252 < baseStart_4822252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822265 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 5, 2, 2]
def baseStart_4822265 : Nat := 118140960795 + 4822265 * 2 ^ 59
def prefixEnd_4822265 : Nat := 4983230072969 + 3 ^ 40 * 4822265 * 2
def baseEnd_4822265 : Nat := 2476139788353680599710313

theorem tailTrace_4822265 : CollatzResearch.WordTrace tailWord_4822265 prefixEnd_4822265 2476139788353680599710313 := by
  unfold tailWord_4822265
  simp only [CollatzResearch.WordTrace]
  refine ⟨175882453874764957138772249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117254969249843304759181499 175882453874764957138772249)
  ·
    refine ⟨131911840406073717854079187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175882453874764957138772249 131911840406073717854079187)
    ·
      refine ⟨197867760609110576781118781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131911840406073717854079187 197867760609110576781118781)
      ·
        refine ⟨74200410228416466292919543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197867760609110576781118781 74200410228416466292919543)
        ·
          refine ⟨111300615342624699439379315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74200410228416466292919543 111300615342624699439379315)
          ·
            refine ⟨166950923013937049159068973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111300615342624699439379315 166950923013937049159068973)
            ·
              refine ⟨62606596130226393434650865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166950923013937049159068973 62606596130226393434650865)
              ·
                refine ⟨46954947097669795075988149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62606596130226393434650865 46954947097669795075988149)
                ·
                  refine ⟨4402026290406543288373889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46954947097669795075988149 4402026290406543288373889)
                  ·
                    refine ⟨3301519717804907466280417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4402026290406543288373889 3301519717804907466280417)
                    ·
                      refine ⟨2476139788353680599710313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301519717804907466280417 2476139788353680599710313)
                      ·
                        rfl

theorem cell23_4822265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_4822265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822265 prefixEnd_4822265 := by exact prefixLift 4822265
  have htrace : WordTrace (prefixWord ++ tailWord_4822265) baseStart_4822265 baseEnd_4822265 := by
    simpa [prefixWord, tailWord_4822265, baseEnd_4822265] using wordTrace_append hprefix tailTrace_4822265
  have hstable : (prefixWord ++ tailWord_4822265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822265).length < 2 ^ (prefixWord ++ tailWord_4822265).sum := by decide
  have hdescent : baseEnd_4822265 < baseStart_4822265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822271 : List Nat := [1, 1, 2, 2, 1, 6, 10]
def baseStart_4822271 : Nat := 118140960795 + 4822271 * 2 ^ 59
def prefixEnd_4822271 : Nat := 4983230072969 + 3 ^ 40 * 4822271 * 2
def baseEnd_4822271 : Nat := 30569665052316142916485

theorem tailTrace_4822271 : CollatzResearch.WordTrace tailWord_4822271 prefixEnd_4822271 30569665052316142916485 := by
  unfold tailWord_4822271
  simp only [CollatzResearch.WordTrace]
  refine ⟨175882672712743220163490667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117255115141828813442327111 175882672712743220163490667)
  ·
    refine ⟨263824009069114830245236001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175882672712743220163490667 263824009069114830245236001)
    ·
      refine ⟨197868006801836122683927001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263824009069114830245236001 197868006801836122683927001)
      ·
        refine ⟨148401005101377092012945251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197868006801836122683927001 148401005101377092012945251)
        ·
          refine ⟨222601507652065638019417877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148401005101377092012945251 222601507652065638019417877)
          ·
            refine ⟨10434445671190576782160213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 222601507652065638019417877 10434445671190576782160213)
            ·
              refine ⟨30569665052316142916485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10434445671190576782160213 30569665052316142916485)
              ·
                rfl

theorem cell23_4822271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 10].length) (baseStart_4822271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822271 prefixEnd_4822271 := by exact prefixLift 4822271
  have htrace : WordTrace (prefixWord ++ tailWord_4822271) baseStart_4822271 baseEnd_4822271 := by
    simpa [prefixWord, tailWord_4822271, baseEnd_4822271] using wordTrace_append hprefix tailTrace_4822271
  have hstable : (prefixWord ++ tailWord_4822271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822271).length < 2 ^ (prefixWord ++ tailWord_4822271).sum := by decide
  have hdescent : baseEnd_4822271 < baseStart_4822271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822275 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 2, 4]
def baseStart_4822275 : Nat := 118140960795 + 4822275 * 2 ^ 59
def prefixEnd_4822275 : Nat := 4983230072969 + 3 ^ 40 * 4822275 * 2
def baseEnd_4822275 : Nat := 825381641053408520195089

theorem tailTrace_4822275 : CollatzResearch.WordTrace tailWord_4822275 prefixEnd_4822275 825381641053408520195089 := by
  unfold tailWord_4822275
  simp only [CollatzResearch.WordTrace]
  refine ⟨175882818604728728846636279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117255212403152485897757519 175882818604728728846636279)
  ·
    refine ⟨263824227907093093269954419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175882818604728728846636279 263824227907093093269954419)
    ·
      refine ⟨395736341860639639904931629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263824227907093093269954419 395736341860639639904931629)
      ·
        refine ⟨148401128197739864964349361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395736341860639639904931629 148401128197739864964349361)
        ·
          refine ⟨111300846148304898723262021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148401128197739864964349361 111300846148304898723262021)
          ·
            refine ⟨20868908652807168510611629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111300846148304898723262021 20868908652807168510611629)
            ·
              refine ⟨7825840744802688191479361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20868908652807168510611629 7825840744802688191479361)
              ·
                refine ⟨5869380558602016143609521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7825840744802688191479361 5869380558602016143609521)
                ·
                  refine ⟨4402035418951512107707141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5869380558602016143609521 4402035418951512107707141)
                  ·
                    refine ⟨825381641053408520195089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402035418951512107707141 825381641053408520195089)
                    ·
                      rfl

theorem cell23_4822275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 4].length) (baseStart_4822275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822275 prefixEnd_4822275 := by exact prefixLift 4822275
  have htrace : WordTrace (prefixWord ++ tailWord_4822275) baseStart_4822275 baseEnd_4822275 := by
    simpa [prefixWord, tailWord_4822275, baseEnd_4822275] using wordTrace_append hprefix tailTrace_4822275
  have hstable : (prefixWord ++ tailWord_4822275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822275).length < 2 ^ (prefixWord ++ tailWord_4822275).sum := by decide
  have hdescent : baseEnd_4822275 < baseStart_4822275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822333 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4822333 : Nat := 118140960795 + 4822333 * 2 ^ 59
def prefixEnd_4822333 : Nat := 4983230072969 + 3 ^ 40 * 4822333 * 2
def baseEnd_4822333 : Nat := 2476174705038186333660001

theorem tailTrace_4822333 : CollatzResearch.WordTrace tailWord_4822333 prefixEnd_4822333 2476174705038186333660001 := by
  unfold tailWord_4822333
  simp only [CollatzResearch.WordTrace]
  refine ⟨175884934038518604752247653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117256622692345736501498435 175884934038518604752247653)
  ·
    refine ⟨32978425132222238391046435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175884934038518604752247653 32978425132222238391046435)
    ·
      refine ⟨49467637698333357586569653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32978425132222238391046435 49467637698333357586569653)
      ·
        refine ⟨4637591034218752273740905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49467637698333357586569653 4637591034218752273740905)
        ·
          refine ⟨3478193275664064205305679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4637591034218752273740905 3478193275664064205305679)
          ·
            refine ⟨5217289913496096307958519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478193275664064205305679 5217289913496096307958519)
            ·
              refine ⟨7825934870244144461937779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217289913496096307958519 7825934870244144461937779)
              ·
                refine ⟨11738902305366216692906669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7825934870244144461937779 11738902305366216692906669)
                ·
                  refine ⟨4402088364512331259840001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11738902305366216692906669 4402088364512331259840001)
                  ·
                    refine ⟨3301566273384248444880001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4402088364512331259840001 3301566273384248444880001)
                    ·
                      refine ⟨2476174705038186333660001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301566273384248444880001 2476174705038186333660001)
                      ·
                        rfl

theorem cell23_4822333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4822333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822333 prefixEnd_4822333 := by exact prefixLift 4822333
  have htrace : WordTrace (prefixWord ++ tailWord_4822333) baseStart_4822333 baseEnd_4822333 := by
    simpa [prefixWord, tailWord_4822333, baseEnd_4822333] using wordTrace_append hprefix tailTrace_4822333
  have hstable : (prefixWord ++ tailWord_4822333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822333).length < 2 ^ (prefixWord ++ tailWord_4822333).sum := by decide
  have hdescent : baseEnd_4822333 < baseStart_4822333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822355 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 1, 4, 2]
def baseStart_4822355 : Nat := 118140960795 + 4822355 * 2 ^ 59
def prefixEnd_4822355 : Nat := 4983230072969 + 3 ^ 40 * 4822355 * 2
def baseEnd_4822355 : Nat := 2476186001612585247584899

theorem tailTrace_4822355 : CollatzResearch.WordTrace tailWord_4822355 prefixEnd_4822355 2476186001612585247584899 := by
  unfold tailWord_4822355
  simp only [CollatzResearch.WordTrace]
  refine ⟨175885736444438902509548519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117257157629625935006365679 175885736444438902509548519)
  ·
    refine ⟨263828604666658353764322779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175885736444438902509548519 263828604666658353764322779)
    ·
      refine ⟨395742906999987530646484169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263828604666658353764322779 395742906999987530646484169)
      ·
        refine ⟨296807180249990647984863127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395742906999987530646484169 296807180249990647984863127)
        ·
          refine ⟨445210770374985971977294691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296807180249990647984863127 445210770374985971977294691)
          ·
            refine ⟨667816155562478957965942037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445210770374985971977294691 667816155562478957965942037)
            ·
              refine ⟨31303882291991201154653533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 667816155562478957965942037 31303882291991201154653533)
              ·
                refine ⟨11738955859496700432995075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31303882291991201154653533 11738955859496700432995075)
                ·
                  refine ⟨17608433789245050649492613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11738955859496700432995075 17608433789245050649492613)
                  ·
                    refine ⟨3301581335483446996779865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17608433789245050649492613 3301581335483446996779865)
                    ·
                      refine ⟨2476186001612585247584899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301581335483446996779865 2476186001612585247584899)
                      ·
                        rfl

theorem cell23_4822355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4, 2].length) (baseStart_4822355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822355 prefixEnd_4822355 := by exact prefixLift 4822355
  have htrace : WordTrace (prefixWord ++ tailWord_4822355) baseStart_4822355 baseEnd_4822355 := by
    simpa [prefixWord, tailWord_4822355, baseEnd_4822355] using wordTrace_append hprefix tailTrace_4822355
  have hstable : (prefixWord ++ tailWord_4822355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822355).length < 2 ^ (prefixWord ++ tailWord_4822355).sum := by decide
  have hdescent : baseEnd_4822355 < baseStart_4822355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822359 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 1, 3, 2]
def baseStart_4822359 : Nat := 118140960795 + 4822359 * 2 ^ 59
def prefixEnd_4822359 : Nat := 4983230072969 + 3 ^ 40 * 4822359 * 2
def baseEnd_4822359 : Nat := 2476188055535203231934881

theorem tailTrace_4822359 : CollatzResearch.WordTrace tailWord_4822359 prefixEnd_4822359 2476188055535203231934881 := by
  unfold tailWord_4822359
  simp only [CollatzResearch.WordTrace]
  refine ⟨175885882336424411192694131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117257254890949607461796087 175885882336424411192694131)
  ·
    refine ⟨263828823504636616789041197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175885882336424411192694131 263828823504636616789041197)
    ·
      refine ⟨98935808814238731295890449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263828823504636616789041197 98935808814238731295890449)
      ·
        refine ⟨74201856610679048471917837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98935808814238731295890449 74201856610679048471917837)
        ·
          refine ⟨27825696229004643176969189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74201856610679048471917837 27825696229004643176969189)
          ·
            refine ⟨5217318042938370595681723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27825696229004643176969189 5217318042938370595681723)
            ·
              refine ⟨7825977064407555893522585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217318042938370595681723 7825977064407555893522585)
              ·
                refine ⟨5869482798305666920141939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7825977064407555893522585 5869482798305666920141939)
                ·
                  refine ⟨8804224197458500380212909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5869482798305666920141939 8804224197458500380212909)
                  ·
                    refine ⟨3301584074046937642579841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8804224197458500380212909 3301584074046937642579841)
                    ·
                      refine ⟨2476188055535203231934881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301584074046937642579841 2476188055535203231934881)
                      ·
                        rfl

theorem cell23_4822359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_4822359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822359 prefixEnd_4822359 := by exact prefixLift 4822359
  have htrace : WordTrace (prefixWord ++ tailWord_4822359) baseStart_4822359 baseEnd_4822359 := by
    simpa [prefixWord, tailWord_4822359, baseEnd_4822359] using wordTrace_append hprefix tailTrace_4822359
  have hstable : (prefixWord ++ tailWord_4822359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822359).length < 2 ^ (prefixWord ++ tailWord_4822359).sum := by decide
  have hdescent : baseEnd_4822359 < baseStart_4822359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822372 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_4822372 : Nat := 118140960795 + 4822372 * 2 ^ 59
def prefixEnd_4822372 : Nat := 4983230072969 + 3 ^ 40 * 4822372 * 2
def baseEnd_4822372 : Nat := 2476194730783711681072321

theorem tailTrace_4822372 : CollatzResearch.WordTrace tailWord_4822372 prefixEnd_4822372 2476194730783711681072321 := by
  unfold tailWord_4822372
  simp only [CollatzResearch.WordTrace]
  refine ⟨87943178242688657206458685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117257570990251542941944913 87943178242688657206458685)
  ·
    refine ⟨32978691841008246452422007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87943178242688657206458685 32978691841008246452422007)
    ·
      refine ⟨49468037761512369678633011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32978691841008246452422007 49468037761512369678633011)
      ·
        refine ⟨74202056642268554517949517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49468037761512369678633011 74202056642268554517949517)
        ·
          refine ⟨27825771240850707944231069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74202056642268554517949517 27825771240850707944231069)
          ·
            refine ⟨10434664215319015479086651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27825771240850707944231069 10434664215319015479086651)
            ·
              refine ⟨15651996322978523218629977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10434664215319015479086651 15651996322978523218629977)
              ·
                refine ⟨11738997242233892413972483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15651996322978523218629977 11738997242233892413972483)
                ·
                  refine ⟨17608495863350838620958725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11738997242233892413972483 17608495863350838620958725)
                  ·
                    refine ⟨3301592974378282241429761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17608495863350838620958725 3301592974378282241429761)
                    ·
                      refine ⟨2476194730783711681072321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301592974378282241429761 2476194730783711681072321)
                      ·
                        rfl

theorem cell23_4822372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_4822372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822372 prefixEnd_4822372 := by exact prefixLift 4822372
  have htrace : WordTrace (prefixWord ++ tailWord_4822372) baseStart_4822372 baseEnd_4822372 := by
    simpa [prefixWord, tailWord_4822372, baseEnd_4822372] using wordTrace_append hprefix tailTrace_4822372
  have hstable : (prefixWord ++ tailWord_4822372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822372).length < 2 ^ (prefixWord ++ tailWord_4822372).sum := by decide
  have hdescent : baseEnd_4822372 < baseStart_4822372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822376 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4822376 : Nat := 118140960795 + 4822376 * 2 ^ 59
def prefixEnd_4822376 : Nat := 4983230072969 + 3 ^ 40 * 4822376 * 2
def baseEnd_4822376 : Nat := 2476196784706329665422303

theorem tailTrace_4822376 : CollatzResearch.WordTrace tailWord_4822376 prefixEnd_4822376 2476196784706329665422303 := by
  unfold tailWord_4822376
  simp only [CollatzResearch.WordTrace]
  refine ⟨87943251188681411548031491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117257668251575215397375321 87943251188681411548031491)
  ·
    refine ⟨131914876783022117322047237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87943251188681411548031491 131914876783022117322047237)
    ·
      refine ⟨24734039396816646997883857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131914876783022117322047237 24734039396816646997883857)
      ·
        refine ⟨18550529547612485248412893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24734039396816646997883857 18550529547612485248412893)
        ·
          refine ⟨6956448580354681968154835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18550529547612485248412893 6956448580354681968154835)
          ·
            refine ⟨10434672870532022952232253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6956448580354681968154835 10434672870532022952232253)
            ·
              refine ⟨3913002326449508607087095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10434672870532022952232253 3913002326449508607087095)
              ·
                refine ⟨5869503489674262910630643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913002326449508607087095 5869503489674262910630643)
                ·
                  refine ⟨8804255234511394365945965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5869503489674262910630643 8804255234511394365945965)
                  ·
                    refine ⟨3301595712941772887229737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8804255234511394365945965 3301595712941772887229737)
                    ·
                      refine ⟨2476196784706329665422303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301595712941772887229737 2476196784706329665422303)
                      ·
                        rfl

theorem cell23_4822376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4822376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822376 prefixEnd_4822376 := by exact prefixLift 4822376
  have htrace : WordTrace (prefixWord ++ tailWord_4822376) baseStart_4822376 baseEnd_4822376 := by
    simpa [prefixWord, tailWord_4822376, baseEnd_4822376] using wordTrace_append hprefix tailTrace_4822376
  have hstable : (prefixWord ++ tailWord_4822376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822376).length < 2 ^ (prefixWord ++ tailWord_4822376).sum := by decide
  have hdescent : baseEnd_4822376 < baseStart_4822376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822395 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 5]
def baseStart_4822395 : Nat := 118140960795 + 4822395 * 2 ^ 59
def prefixEnd_4822395 : Nat := 4983230072969 + 3 ^ 40 * 4822395 * 2
def baseEnd_4822395 : Nat := 275134060093196121231635

theorem tailTrace_4822395 : CollatzResearch.WordTrace tailWord_4822395 prefixEnd_4822395 275134060093196121231635 := by
  unfold tailWord_4822395
  simp only [CollatzResearch.WordTrace]
  refine ⟨175887195364293989341004639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117258130242862659560669759 175887195364293989341004639)
  ·
    refine ⟨263830793046440984011506959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175887195364293989341004639 263830793046440984011506959)
    ·
      refine ⟨395746189569661476017260439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263830793046440984011506959 395746189569661476017260439)
      ·
        refine ⟨593619284354492214025890659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395746189569661476017260439 593619284354492214025890659)
        ·
          refine ⟨890428926531738321038835989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593619284354492214025890659 890428926531738321038835989)
          ·
            refine ⟨41738855931175233798695437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 890428926531738321038835989 41738855931175233798695437)
            ·
              refine ⟨15652070974190712674510789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41738855931175233798695437 15652070974190712674510789)
              ·
                refine ⟨2934763307660758626470773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15652070974190712674510789 2934763307660758626470773)
                ·
                  refine ⟨275134060093196121231635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2934763307660758626470773 275134060093196121231635)
                  ·
                    rfl

theorem cell23_4822395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 5].length) (baseStart_4822395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822395 prefixEnd_4822395 := by exact prefixLift 4822395
  have htrace : WordTrace (prefixWord ++ tailWord_4822395) baseStart_4822395 baseEnd_4822395 := by
    simpa [prefixWord, tailWord_4822395, baseEnd_4822395] using wordTrace_append hprefix tailTrace_4822395
  have hstable : (prefixWord ++ tailWord_4822395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822395).length < 2 ^ (prefixWord ++ tailWord_4822395).sum := by decide
  have hdescent : baseEnd_4822395 < baseStart_4822395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822402 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4822402 : Nat := 118140960795 + 4822402 * 2 ^ 59
def prefixEnd_4822402 : Nat := 4983230072969 + 3 ^ 40 * 4822402 * 2
def baseEnd_4822402 : Nat := 2476210135203346563697183

theorem tailTrace_4822402 : CollatzResearch.WordTrace tailWord_4822402 prefixEnd_4822402 2476210135203346563697183 := by
  unfold tailWord_4822402
  simp only [CollatzResearch.WordTrace]
  refine ⟨43971862668817157384127365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117258300450179086357672973 43971862668817157384127365)
  ·
    refine ⟨8244724250403217009523881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43971862668817157384127365 8244724250403217009523881)
    ·
      refine ⟨6183543187802412757142911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8244724250403217009523881 6183543187802412757142911)
      ·
        refine ⟨9275314781703619135714367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183543187802412757142911 9275314781703619135714367)
        ·
          refine ⟨13912972172555428703571551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9275314781703619135714367 13912972172555428703571551)
          ·
            refine ⟨20869458258833143055357327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13912972172555428703571551 20869458258833143055357327)
            ·
              refine ⟨31304187388249714583035991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20869458258833143055357327 31304187388249714583035991)
              ·
                refine ⟨46956281082374571874553987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31304187388249714583035991 46956281082374571874553987)
                ·
                  refine ⟨70434421623561857811830981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46956281082374571874553987 70434421623561857811830981)
                  ·
                    refine ⟨13206454054417848339718309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70434421623561857811830981 13206454054417848339718309)
                    ·
                      refine ⟨2476210135203346563697183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13206454054417848339718309 2476210135203346563697183)
                      ·
                        rfl

theorem cell23_4822402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4822402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822402 prefixEnd_4822402 := by exact prefixLift 4822402
  have htrace : WordTrace (prefixWord ++ tailWord_4822402) baseStart_4822402 baseEnd_4822402 := by
    simpa [prefixWord, tailWord_4822402, baseEnd_4822402] using wordTrace_append hprefix tailTrace_4822402
  have hstable : (prefixWord ++ tailWord_4822402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822402).length < 2 ^ (prefixWord ++ tailWord_4822402).sum := by decide
  have hdescent : baseEnd_4822402 < baseStart_4822402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822425 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 2, 5]
def baseStart_4822425 : Nat := 118140960795 + 4822425 * 2 ^ 59
def prefixEnd_4822425 : Nat := 4983230072969 + 3 ^ 40 * 4822425 * 2
def baseEnd_4822425 : Nat := 825407315086133324569859

theorem tailTrace_4822425 : CollatzResearch.WordTrace tailWord_4822425 prefixEnd_4822425 825407315086133324569859 := by
  unfold tailWord_4822425
  simp only [CollatzResearch.WordTrace]
  refine ⟨175888289554185304464596729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117258859702790202976397819 175888289554185304464596729)
  ·
    refine ⟨131916217165638978348447547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175888289554185304464596729 131916217165638978348447547)
    ·
      refine ⟨197874325748458467522671321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131916217165638978348447547 197874325748458467522671321)
      ·
        refine ⟨148405744311343850642003491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197874325748458467522671321 148405744311343850642003491)
        ·
          refine ⟨222608616467015775963005237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148405744311343850642003491 222608616467015775963005237)
          ·
            refine ⟨20869557793782728996531741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222608616467015775963005237 20869557793782728996531741)
            ·
              refine ⟨7826084172668523373699403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20869557793782728996531741 7826084172668523373699403)
              ·
                refine ⟨11739126259002785060549105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7826084172668523373699403 11739126259002785060549105)
                ·
                  refine ⟨8804344694252088795411829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11739126259002785060549105 8804344694252088795411829)
                  ·
                    refine ⟨825407315086133324569859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8804344694252088795411829 825407315086133324569859)
                    ·
                      rfl

theorem cell23_4822425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_4822425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822425 prefixEnd_4822425 := by exact prefixLift 4822425
  have htrace : WordTrace (prefixWord ++ tailWord_4822425) baseStart_4822425 baseEnd_4822425 := by
    simpa [prefixWord, tailWord_4822425, baseEnd_4822425] using wordTrace_append hprefix tailTrace_4822425
  have hstable : (prefixWord ++ tailWord_4822425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822425).length < 2 ^ (prefixWord ++ tailWord_4822425).sum := by decide
  have hdescent : baseEnd_4822425 < baseStart_4822425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822440 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4822440 : Nat := 118140960795 + 4822440 * 2 ^ 59
def prefixEnd_4822440 : Nat := 4983230072969 + 3 ^ 40 * 4822440 * 2
def baseEnd_4822440 : Nat := 2476229647468217415022009

theorem tailTrace_4822440 : CollatzResearch.WordTrace tailWord_4822440 prefixEnd_4822440 2476229647468217415022009 := by
  unfold tailWord_4822440
  simp only [CollatzResearch.WordTrace]
  refine ⟨87944418324565481013196387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117259224432753974684261849 87944418324565481013196387)
  ·
    refine ⟨131916627486848221519794581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87944418324565481013196387 131916627486848221519794581)
    ·
      refine ⟨6183591913446010383740371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131916627486848221519794581 6183591913446010383740371)
      ·
        refine ⟨9275387870169015575610557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183591913446010383740371 9275387870169015575610557)
        ·
          refine ⟨3478270451313380840853959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9275387870169015575610557 3478270451313380840853959)
          ·
            refine ⟨5217405676970071261280939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478270451313380840853959 5217405676970071261280939)
            ·
              refine ⟨7826108515455106891921409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217405676970071261280939 7826108515455106891921409)
              ·
                refine ⟨5869581386591330168941057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7826108515455106891921409 5869581386591330168941057)
                ·
                  refine ⟨4402186039943497626705793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5869581386591330168941057 4402186039943497626705793)
                  ·
                    refine ⟨3301639529957623220029345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4402186039943497626705793 3301639529957623220029345)
                    ·
                      refine ⟨2476229647468217415022009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301639529957623220029345 2476229647468217415022009)
                      ·
                        rfl

theorem cell23_4822440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4822440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822440 prefixEnd_4822440 := by exact prefixLift 4822440
  have htrace : WordTrace (prefixWord ++ tailWord_4822440) baseStart_4822440 baseEnd_4822440 := by
    simpa [prefixWord, tailWord_4822440, baseEnd_4822440] using wordTrace_append hprefix tailTrace_4822440
  have hstable : (prefixWord ++ tailWord_4822440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822440).length < 2 ^ (prefixWord ++ tailWord_4822440).sum := by decide
  have hdescent : baseEnd_4822440 < baseStart_4822440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822489 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 1, 4]
def baseStart_4822489 : Nat := 118140960795 + 4822489 * 2 ^ 59
def prefixEnd_4822489 : Nat := 4983230072969 + 3 ^ 40 * 4822489 * 2
def baseEnd_4822489 : Nat := 825418269340095907769761

theorem tailTrace_4822489 : CollatzResearch.WordTrace tailWord_4822489 prefixEnd_4822489 825418269340095907769761 := by
  unfold tailWord_4822489
  simp only [CollatzResearch.WordTrace]
  refine ⟨175890623825953443394926521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117260415883968962263284347 175890623825953443394926521)
  ·
    refine ⟨131917967869465082546194891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175890623825953443394926521 131917967869465082546194891)
    ·
      refine ⟨197876951804197623819292337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131917967869465082546194891 197876951804197623819292337)
      ·
        refine ⟨148407713853148217864469253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197876951804197623819292337 148407713853148217864469253)
        ·
          refine ⟨27826446347465290849587985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148407713853148217864469253 27826446347465290849587985)
          ·
            refine ⟨20869834760598968137190989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27826446347465290849587985 20869834760598968137190989)
            ·
              refine ⟨7826188035224613051446621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20869834760598968137190989 7826188035224613051446621)
              ·
                refine ⟨2934820513209229894292483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7826188035224613051446621 2934820513209229894292483)
                ·
                  refine ⟨4402230769813844841438725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934820513209229894292483 4402230769813844841438725)
                  ·
                    refine ⟨825418269340095907769761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402230769813844841438725 825418269340095907769761)
                    ·
                      rfl

theorem cell23_4822489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 4].length) (baseStart_4822489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822489 prefixEnd_4822489 := by exact prefixLift 4822489
  have htrace : WordTrace (prefixWord ++ tailWord_4822489) baseStart_4822489 baseEnd_4822489 := by
    simpa [prefixWord, tailWord_4822489, baseEnd_4822489] using wordTrace_append hprefix tailTrace_4822489
  have hstable : (prefixWord ++ tailWord_4822489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822489).length < 2 ^ (prefixWord ++ tailWord_4822489).sum := by decide
  have hdescent : baseEnd_4822489 < baseStart_4822489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822506 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_4822506 : Nat := 118140960795 + 4822506 * 2 ^ 59
def prefixEnd_4822506 : Nat := 4983230072969 + 3 ^ 40 * 4822506 * 2
def baseEnd_4822506 : Nat := 825421179063804718932235

theorem tailTrace_4822506 : CollatzResearch.WordTrace tailWord_4822506 prefixEnd_4822506 825421179063804718932235 := by
  unfold tailWord_4822506
  simp only [CollatzResearch.WordTrace]
  refine ⟨43972810966722963824573843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117260829244594570198863581 43972810966722963824573843)
  ·
    refine ⟨65959216450084445736860765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43972810966722963824573843 65959216450084445736860765)
    ·
      refine ⟨24734706168781667151322787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65959216450084445736860765 24734706168781667151322787)
      ·
        refine ⟨37102059253172500726984181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24734706168781667151322787 37102059253172500726984181)
        ·
          refine ⟨3478318054984921943154767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37102059253172500726984181 3478318054984921943154767)
          ·
            refine ⟨5217477082477382914732151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478318054984921943154767 5217477082477382914732151)
            ·
              refine ⟨7826215623716074372098227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217477082477382914732151 7826215623716074372098227)
              ·
                refine ⟨11739323435574111558147341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7826215623716074372098227 11739323435574111558147341)
                ·
                  refine ⟨4402246288340291834305253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11739323435574111558147341 4402246288340291834305253)
                  ·
                    refine ⟨825421179063804718932235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402246288340291834305253 825421179063804718932235)
                    ·
                      rfl

theorem cell23_4822506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_4822506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822506 prefixEnd_4822506 := by exact prefixLift 4822506
  have htrace : WordTrace (prefixWord ++ tailWord_4822506) baseStart_4822506 baseEnd_4822506 := by
    simpa [prefixWord, tailWord_4822506, baseEnd_4822506] using wordTrace_append hprefix tailTrace_4822506
  have hstable : (prefixWord ++ tailWord_4822506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822506).length < 2 ^ (prefixWord ++ tailWord_4822506).sum := by decide
  have hdescent : baseEnd_4822506 < baseStart_4822506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822522 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2]
def baseStart_4822522 : Nat := 118140960795 + 4822522 * 2 ^ 59
def prefixEnd_4822522 : Nat := 4983230072969 + 3 ^ 40 * 4822522 * 2
def baseEnd_4822522 : Nat := 2476271752881886094196631

theorem tailTrace_4822522 : CollatzResearch.WordTrace tailWord_4822522 prefixEnd_4822522 2476271752881886094196631 := by
  unfold tailWord_4822522
  simp only [CollatzResearch.WordTrace]
  refine ⟨43972956858708472507719455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117261218289889260020585213 43972956858708472507719455)
  ·
    refine ⟨65959435288062708761579183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43972956858708472507719455 65959435288062708761579183)
    ·
      refine ⟨98939152932094063142368775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65959435288062708761579183 98939152932094063142368775)
      ·
        refine ⟨148408729398141094713553163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98939152932094063142368775 148408729398141094713553163)
        ·
          refine ⟨222613094097211642070329745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148408729398141094713553163 222613094097211642070329745)
          ·
            refine ⟨166959820572908731552747309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222613094097211642070329745 166959820572908731552747309)
            ·
              refine ⟨62609932714840774332280241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166959820572908731552747309 62609932714840774332280241)
              ·
                refine ⟨46957449536130580749210181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62609932714840774332280241 46957449536130580749210181)
                ·
                  refine ⟨8804521788024483890476909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46957449536130580749210181 8804521788024483890476909)
                  ·
                    refine ⟨3301695670509181458928841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8804521788024483890476909 3301695670509181458928841)
                    ·
                      refine ⟨2476271752881886094196631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301695670509181458928841 2476271752881886094196631)
                      ·
                        rfl

theorem cell23_4822522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_4822522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822522 prefixEnd_4822522 := by exact prefixLift 4822522
  have htrace : WordTrace (prefixWord ++ tailWord_4822522) baseStart_4822522 baseEnd_4822522 := by
    simpa [prefixWord, tailWord_4822522, baseEnd_4822522] using wordTrace_append hprefix tailTrace_4822522
  have hstable : (prefixWord ++ tailWord_4822522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822522).length < 2 ^ (prefixWord ++ tailWord_4822522).sum := by decide
  have hdescent : baseEnd_4822522 < baseStart_4822522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822545 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_4822545 : Nat := 118140960795 + 4822545 * 2 ^ 59
def prefixEnd_4822545 : Nat := 4983230072969 + 3 ^ 40 * 4822545 * 2
def baseEnd_4822545 : Nat := 825427854312313168069675

theorem tailTrace_4822545 : CollatzResearch.WordTrace tailWord_4822545 prefixEnd_4822545 825427854312313168069675 := by
  unfold tailWord_4822545
  simp only [CollatzResearch.WordTrace]
  refine ⟨175892666313750564958965089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117261777542500376639310059 175892666313750564958965089)
  ·
    refine ⟨131919499735312923719223817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175892666313750564958965089 131919499735312923719223817)
    ·
      refine ⟨98939624801484692789417863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131919499735312923719223817 98939624801484692789417863)
      ·
        refine ⟨148409437202227039184126795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98939624801484692789417863 148409437202227039184126795)
        ·
          refine ⟨222614155803340558776190193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148409437202227039184126795 222614155803340558776190193)
          ·
            refine ⟨166960616852505419082142645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222614155803340558776190193 166960616852505419082142645)
            ·
              refine ⟨15652557829922383038950873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166960616852505419082142645 15652557829922383038950873)
              ·
                refine ⟨11739418372441787279213155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15652557829922383038950873 11739418372441787279213155)
                ·
                  refine ⟨17609127558662680918819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11739418372441787279213155 17609127558662680918819733)
                  ·
                    refine ⟨825427854312313168069675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17609127558662680918819733 825427854312313168069675)
                    ·
                      rfl

theorem cell23_4822545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_4822545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822545 prefixEnd_4822545 := by exact prefixLift 4822545
  have htrace : WordTrace (prefixWord ++ tailWord_4822545) baseStart_4822545 baseEnd_4822545 := by
    simpa [prefixWord, tailWord_4822545, baseEnd_4822545] using wordTrace_append hprefix tailTrace_4822545
  have hstable : (prefixWord ++ tailWord_4822545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822545).length < 2 ^ (prefixWord ++ tailWord_4822545).sum := by decide
  have hdescent : baseEnd_4822545 < baseStart_4822545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822549 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_4822549 : Nat := 118140960795 + 4822549 * 2 ^ 59
def prefixEnd_4822549 : Nat := 4983230072969 + 3 ^ 40 * 4822549 * 2
def baseEnd_4822549 : Nat := 825428538953185829519669

theorem tailTrace_4822549 : CollatzResearch.WordTrace tailWord_4822549 prefixEnd_4822549 825428538953185829519669 := by
  unfold tailWord_4822549
  simp only [CollatzResearch.WordTrace]
  refine ⟨175892812205736073642110701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117261874803824049094740467 175892812205736073642110701)
  ·
    refine ⟨65959804577151027615791513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175892812205736073642110701 65959804577151027615791513)
    ·
      refine ⟨49469853432863270711843635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65959804577151027615791513 49469853432863270711843635)
      ·
        refine ⟨74204780149294906067765453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49469853432863270711843635 74204780149294906067765453)
        ·
          refine ⟨27826792555985589775412045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74204780149294906067765453 27826792555985589775412045)
          ·
            refine ⟨10435047208494596165779517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27826792555985589775412045 10435047208494596165779517)
            ·
              refine ⟨3913142703185473562167319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10435047208494596165779517 3913142703185473562167319)
              ·
                refine ⟨5869714054778210343250979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913142703185473562167319 5869714054778210343250979)
                ·
                  refine ⟨8804571082167315514876469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5869714054778210343250979 8804571082167315514876469)
                  ·
                    refine ⟨825428538953185829519669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8804571082167315514876469 825428538953185829519669)
                    ·
                      rfl

theorem cell23_4822549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_4822549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822549 prefixEnd_4822549 := by exact prefixLift 4822549
  have htrace : WordTrace (prefixWord ++ tailWord_4822549) baseStart_4822549 baseEnd_4822549 := by
    simpa [prefixWord, tailWord_4822549, baseEnd_4822549] using wordTrace_append hprefix tailTrace_4822549
  have hstable : (prefixWord ++ tailWord_4822549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822549).length < 2 ^ (prefixWord ++ tailWord_4822549).sum := by decide
  have hdescent : baseEnd_4822549 < baseStart_4822549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822562 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_4822562 : Nat := 118140960795 + 4822562 * 2 ^ 59
def prefixEnd_4822562 : Nat := 4983230072969 + 3 ^ 40 * 4822562 * 2
def baseEnd_4822562 : Nat := 825430764036021979232149

theorem tailTrace_4822562 : CollatzResearch.WordTrace tailWord_4822562 prefixEnd_4822562 825430764036021979232149 := by
  unfold tailWord_4822562
  simp only [CollatzResearch.WordTrace]
  refine ⟨43973321588672244215583485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117262190903125984574889293 43973321588672244215583485)
  ·
    refine ⟨16489995595752091580843807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43973321588672244215583485 16489995595752091580843807)
    ·
      refine ⟨24734993393628137371265711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16489995595752091580843807 24734993393628137371265711)
      ·
        refine ⟨37102490090442206056898567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24734993393628137371265711 37102490090442206056898567)
        ·
          refine ⟨55653735135663309085347851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37102490090442206056898567 55653735135663309085347851)
          ·
            refine ⟨83480602703494963628021777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55653735135663309085347851 83480602703494963628021777)
            ·
              refine ⟨62610452027621222721016333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83480602703494963628021777 62610452027621222721016333)
              ·
                refine ⟨23478919510357958520381125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62610452027621222721016333 23478919510357958520381125)
                ·
                  refine ⟨4402297408192117222571461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23478919510357958520381125 4402297408192117222571461)
                  ·
                    refine ⟨825430764036021979232149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402297408192117222571461 825430764036021979232149)
                    ·
                      rfl

theorem cell23_4822562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_4822562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822562 prefixEnd_4822562 := by exact prefixLift 4822562
  have htrace : WordTrace (prefixWord ++ tailWord_4822562) baseStart_4822562 baseEnd_4822562 := by
    simpa [prefixWord, tailWord_4822562, baseEnd_4822562] using wordTrace_append hprefix tailTrace_4822562
  have hstable : (prefixWord ++ tailWord_4822562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822562).length < 2 ^ (prefixWord ++ tailWord_4822562).sum := by decide
  have hdescent : baseEnd_4822562 < baseStart_4822562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822565 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_4822565 : Nat := 118140960795 + 4822565 * 2 ^ 59
def prefixEnd_4822565 : Nat := 4983230072969 + 3 ^ 40 * 4822565 * 2
def baseEnd_4822565 : Nat := 2476293832550029425958933

theorem tailTrace_4822565 : CollatzResearch.WordTrace tailWord_4822565 prefixEnd_4822565 2476293832550029425958933 := by
  unfold tailWord_4822565
  simp only [CollatzResearch.WordTrace]
  refine ⟨175893395773678108374693149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117262263849118738916462099 175893395773678108374693149)
  ·
    refine ⟨65960023415129290640509931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175893395773678108374693149 65960023415129290640509931)
    ·
      refine ⟨98940035122693935960764897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65960023415129290640509931 98940035122693935960764897)
      ·
        refine ⟨74205026342020451970573673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98940035122693935960764897 74205026342020451970573673)
        ·
          refine ⟨55653769756515338977930255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74205026342020451970573673 55653769756515338977930255)
          ·
            refine ⟨83480654634773008466895383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55653769756515338977930255 83480654634773008466895383)
            ·
              refine ⟨125220981952159512700343075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83480654634773008466895383 125220981952159512700343075)
              ·
                refine ⟨187831472928239269050514613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125220981952159512700343075 187831472928239269050514613)
                ·
                  refine ⟨17609200587022431473485745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187831472928239269050514613 17609200587022431473485745)
                  ·
                    refine ⟨13206900440266823605114309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17609200587022431473485745 13206900440266823605114309)
                    ·
                      refine ⟨2476293832550029425958933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13206900440266823605114309 2476293832550029425958933)
                      ·
                        rfl

theorem cell23_4822565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_4822565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822565 prefixEnd_4822565 := by exact prefixLift 4822565
  have htrace : WordTrace (prefixWord ++ tailWord_4822565) baseStart_4822565 baseEnd_4822565 := by
    simpa [prefixWord, tailWord_4822565, baseEnd_4822565] using wordTrace_append hprefix tailTrace_4822565
  have hstable : (prefixWord ++ tailWord_4822565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822565).length < 2 ^ (prefixWord ++ tailWord_4822565).sum := by decide
  have hdescent : baseEnd_4822565 < baseStart_4822565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822602 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_4822602 : Nat := 118140960795 + 4822602 * 2 ^ 59
def prefixEnd_4822602 : Nat := 4983230072969 + 3 ^ 40 * 4822602 * 2
def baseEnd_4822602 : Nat := 2476312831334245781196263

theorem tailTrace_4822602 : CollatzResearch.WordTrace tailWord_4822602 prefixEnd_4822602 2476312831334245781196263 := by
  unfold tailWord_4822602
  simp only [CollatzResearch.WordTrace]
  refine ⟨43973686318636015923447515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117263163516362709129193373 43973686318636015923447515)
  ·
    refine ⟨65960529477954023885171273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43973686318636015923447515 65960529477954023885171273)
    ·
      refine ⟨49470397108465517913878455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65960529477954023885171273 49470397108465517913878455)
      ·
        refine ⟨74205595662698276870817683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49470397108465517913878455 74205595662698276870817683)
        ·
          refine ⟨111308393494047415306226525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74205595662698276870817683 111308393494047415306226525)
          ·
            refine ⟨41740647560267780739834947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111308393494047415306226525 41740647560267780739834947)
            ·
              refine ⟨62610971340401671109752421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41740647560267780739834947 62610971340401671109752421)
              ·
                refine ⟨11739557126325313333078579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62610971340401671109752421 11739557126325313333078579)
                ·
                  refine ⟨17609335689487969999617869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11739557126325313333078579 17609335689487969999617869)
                  ·
                    refine ⟨6603500883557988749856701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17609335689487969999617869 6603500883557988749856701)
                    ·
                      refine ⟨2476312831334245781196263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6603500883557988749856701 2476312831334245781196263)
                      ·
                        rfl

theorem cell23_4822602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_4822602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822602 prefixEnd_4822602 := by exact prefixLift 4822602
  have htrace : WordTrace (prefixWord ++ tailWord_4822602) baseStart_4822602 baseEnd_4822602 := by
    simpa [prefixWord, tailWord_4822602, baseEnd_4822602] using wordTrace_append hprefix tailTrace_4822602
  have hstable : (prefixWord ++ tailWord_4822602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822602).length < 2 ^ (prefixWord ++ tailWord_4822602).sum := by decide
  have hdescent : baseEnd_4822602 < baseStart_4822602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822665 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 9]
def baseStart_4822665 : Nat := 118140960795 + 4822665 * 2 ^ 59
def prefixEnd_4822665 : Nat := 4983230072969 + 3 ^ 40 * 4822665 * 2
def baseEnd_4822665 : Nat := 275149464512831003856497

theorem tailTrace_4822665 : CollatzResearch.WordTrace tailWord_4822665 prefixEnd_4822665 275149464512831003856497 := by
  unfold tailWord_4822665
  simp only [CollatzResearch.WordTrace]
  refine ⟨175897043073315825453333449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117264695382210550302222299 175897043073315825453333449)
  ·
    refine ⟨131922782304986869090000087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175897043073315825453333449 131922782304986869090000087)
    ·
      refine ⟨197884173457480303635000131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131922782304986869090000087 197884173457480303635000131)
      ·
        refine ⟨296826260186220455452500197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197884173457480303635000131 296826260186220455452500197)
        ·
          refine ⟨55654923784916335397343787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296826260186220455452500197 55654923784916335397343787)
          ·
            refine ⟨83482385677374503096015681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55654923784916335397343787 83482385677374503096015681)
            ·
              refine ⟨62611789258030877322011761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83482385677374503096015681 62611789258030877322011761)
              ·
                refine ⟨46958841943523157991508821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62611789258030877322011761 46958841943523157991508821)
                ·
                  refine ⟨275149464512831003856497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46958841943523157991508821 275149464512831003856497)
                  ·
                    rfl

theorem cell23_4822665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_4822665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822665 prefixEnd_4822665 := by exact prefixLift 4822665
  have htrace : WordTrace (prefixWord ++ tailWord_4822665) baseStart_4822665 baseEnd_4822665 := by
    simpa [prefixWord, tailWord_4822665, baseEnd_4822665] using wordTrace_append hprefix tailTrace_4822665
  have hstable : (prefixWord ++ tailWord_4822665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822665).length < 2 ^ (prefixWord ++ tailWord_4822665).sum := by decide
  have hdescent : baseEnd_4822665 < baseStart_4822665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822687 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4822687 : Nat := 118140960795 + 4822687 * 2 ^ 59
def prefixEnd_4822687 : Nat := 4983230072969 + 3 ^ 40 * 4822687 * 2
def baseEnd_4822687 : Nat := 2476356477189877948633373

theorem tailTrace_4822687 : CollatzResearch.WordTrace tailWord_4822687 prefixEnd_4822687 2476356477189877948633373 := by
  unfold tailWord_4822687
  simp only [CollatzResearch.WordTrace]
  refine ⟨175897845479236123210634315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117265230319490748807089543 175897845479236123210634315)
  ·
    refine ⟨263846768218854184815951473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175897845479236123210634315 263846768218854184815951473)
    ·
      refine ⟨197885076164140638611963605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263846768218854184815951473 197885076164140638611963605)
      ·
        refine ⟨4637931472597046217467897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 197885076164140638611963605 4637931472597046217467897)
        ·
          refine ⟨3478448604447784663100923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4637931472597046217467897 3478448604447784663100923)
          ·
            refine ⟨5217672906671676994651385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478448604447784663100923 5217672906671676994651385)
            ·
              refine ⟨3913254680003757745988539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5217672906671676994651385 3913254680003757745988539)
              ·
                refine ⟨5869882020005636618982809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913254680003757745988539 5869882020005636618982809)
                ·
                  refine ⟨4402411515004227464237107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5869882020005636618982809 4402411515004227464237107)
                  ·
                    refine ⟨6603617272506341196355661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402411515004227464237107 6603617272506341196355661)
                    ·
                      refine ⟨2476356477189877948633373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6603617272506341196355661 2476356477189877948633373)
                      ·
                        rfl

theorem cell23_4822687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4822687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822687 prefixEnd_4822687 := by exact prefixLift 4822687
  have htrace : WordTrace (prefixWord ++ tailWord_4822687) baseStart_4822687 baseEnd_4822687 := by
    simpa [prefixWord, tailWord_4822687, baseEnd_4822687] using wordTrace_append hprefix tailTrace_4822687
  have hstable : (prefixWord ++ tailWord_4822687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822687).length < 2 ^ (prefixWord ++ tailWord_4822687).sum := by decide
  have hdescent : baseEnd_4822687 < baseStart_4822687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822693 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 2, 2, 2]
def baseStart_4822693 : Nat := 118140960795 + 4822693 * 2 ^ 59
def prefixEnd_4822693 : Nat := 4983230072969 + 3 ^ 40 * 4822693 * 2
def baseEnd_4822693 : Nat := 2476359558073804925158345

theorem tailTrace_4822693 : CollatzResearch.WordTrace tailWord_4822693 prefixEnd_4822693 2476359558073804925158345 := by
  unfold tailWord_4822693
  simp only [CollatzResearch.WordTrace]
  refine ⟨175898064317214386235352733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117265376211476257490235155 175898064317214386235352733)
  ·
    refine ⟨65961774118955394838257275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175898064317214386235352733 65961774118955394838257275)
    ·
      refine ⟨98942661178433092257385913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65961774118955394838257275 98942661178433092257385913)
      ·
        refine ⟨74206995883824819193039435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98942661178433092257385913 74206995883824819193039435)
        ·
          refine ⟨111310493825737228789559153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74206995883824819193039435 111310493825737228789559153)
          ·
            refine ⟨83482870369302921592169365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111310493825737228789559153 83482870369302921592169365)
            ·
              refine ⟨3913259548561074449632939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83482870369302921592169365 3913259548561074449632939)
              ·
                refine ⟨5869889322841611674449409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913259548561074449632939 5869889322841611674449409)
                ·
                  refine ⟨4402416992131208755837057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5869889322841611674449409 4402416992131208755837057)
                  ·
                    refine ⟨3301812744098406566877793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4402416992131208755837057 3301812744098406566877793)
                    ·
                      refine ⟨2476359558073804925158345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301812744098406566877793 2476359558073804925158345)
                      ·
                        rfl

theorem cell23_4822693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_4822693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822693 prefixEnd_4822693 := by exact prefixLift 4822693
  have htrace : WordTrace (prefixWord ++ tailWord_4822693) baseStart_4822693 baseEnd_4822693 := by
    simpa [prefixWord, tailWord_4822693, baseEnd_4822693] using wordTrace_append hprefix tailTrace_4822693
  have hstable : (prefixWord ++ tailWord_4822693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822693).length < 2 ^ (prefixWord ++ tailWord_4822693).sum := by decide
  have hdescent : baseEnd_4822693 < baseStart_4822693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822733 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 5]
def baseStart_4822733 : Nat := 118140960795 + 4822733 * 2 ^ 59
def prefixEnd_4822733 : Nat := 4983230072969 + 3 ^ 40 * 4822733 * 2
def baseEnd_4822733 : Nat := 275153344144442752073129

theorem tailTrace_4822733 : CollatzResearch.WordTrace tailWord_4822733 prefixEnd_4822733 275153344144442752073129 := by
  unfold tailWord_4822733
  simp only [CollatzResearch.WordTrace]
  refine ⟨175899523237069473066808853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117266348824712982044539235 175899523237069473066808853)
  ·
    refine ⟨8245290151737631550006665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 175899523237069473066808853 8245290151737631550006665)
    ·
      refine ⟨6183967613803223662504999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8245290151737631550006665 6183967613803223662504999)
      ·
        refine ⟨9275951420704835493757499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183967613803223662504999 9275951420704835493757499)
        ·
          refine ⟨13913927131057253240636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9275951420704835493757499 13913927131057253240636249)
          ·
            refine ⟨10435445348292939930477187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13913927131057253240636249 10435445348292939930477187)
            ·
              refine ⟨15653168022439409895715781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10435445348292939930477187 15653168022439409895715781)
              ·
                refine ⟨2934969004207389355446709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15653168022439409895715781 2934969004207389355446709)
                ·
                  refine ⟨275153344144442752073129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2934969004207389355446709 275153344144442752073129)
                  ·
                    rfl

theorem cell23_4822733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_4822733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822733 prefixEnd_4822733 := by exact prefixLift 4822733
  have htrace : WordTrace (prefixWord ++ tailWord_4822733) baseStart_4822733 baseEnd_4822733 := by
    simpa [prefixWord, tailWord_4822733, baseEnd_4822733] using wordTrace_append hprefix tailTrace_4822733
  have hstable : (prefixWord ++ tailWord_4822733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822733).length < 2 ^ (prefixWord ++ tailWord_4822733).sum := by decide
  have hdescent : baseEnd_4822733 < baseStart_4822733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822769 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_4822769 : Nat := 118140960795 + 4822769 * 2 ^ 59
def prefixEnd_4822769 : Nat := 4983230072969 + 3 ^ 40 * 4822769 * 2
def baseEnd_4822769 : Nat := 2476398582603546627807995

theorem tailTrace_4822769 : CollatzResearch.WordTrace tailWord_4822769 prefixEnd_4822769 2476398582603546627807995 := by
  unfold tailWord_4822769
  simp only [CollatzResearch.WordTrace]
  refine ⟨175900836264939051215119361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117267224176626034143412907 175900836264939051215119361)
  ·
    refine ⟨131925627198704288411339521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175900836264939051215119361 131925627198704288411339521)
    ·
      refine ⟨98944220399028216308504641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131925627198704288411339521 98944220399028216308504641)
      ·
        refine ⟨74208165299271162231378481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98944220399028216308504641 74208165299271162231378481)
        ·
          refine ⟨55656123974453371673533861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74208165299271162231378481 55656123974453371673533861)
          ·
            refine ⟨10435523245210007188787599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55656123974453371673533861 10435523245210007188787599)
            ·
              refine ⟨15653284867815010783181399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10435523245210007188787599 15653284867815010783181399)
              ·
                refine ⟨23479927301722516174772099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15653284867815010783181399 23479927301722516174772099)
                ·
                  refine ⟨35219890952583774262158149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23479927301722516174772099 35219890952583774262158149)
                  ·
                    refine ⟨6603729553609457674154653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35219890952583774262158149 6603729553609457674154653)
                    ·
                      refine ⟨2476398582603546627807995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6603729553609457674154653 2476398582603546627807995)
                      ·
                        rfl

theorem cell23_4822769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_4822769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822769 prefixEnd_4822769 := by exact prefixLift 4822769
  have htrace : WordTrace (prefixWord ++ tailWord_4822769) baseStart_4822769 baseEnd_4822769 := by
    simpa [prefixWord, tailWord_4822769, baseEnd_4822769] using wordTrace_append hprefix tailTrace_4822769
  have hstable : (prefixWord ++ tailWord_4822769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822769).length < 2 ^ (prefixWord ++ tailWord_4822769).sum := by decide
  have hdescent : baseEnd_4822769 < baseStart_4822769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822786 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_4822786 : Nat := 118140960795 + 4822786 * 2 ^ 59
def prefixEnd_4822786 : Nat := 4983230072969 + 3 ^ 40 * 4822786 * 2
def baseEnd_4822786 : Nat := 2476407311774673061295417

theorem tailTrace_4822786 : CollatzResearch.WordTrace tailWord_4822786 prefixEnd_4822786 2476407311774673061295417 := by
  unfold tailWord_4822786
  simp only [CollatzResearch.WordTrace]
  refine ⟨43975364076469365779622053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117267637537251642078992141 43975364076469365779622053)
  ·
    refine ⟨8245380764338006083679135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43975364076469365779622053 8245380764338006083679135)
    ·
      refine ⟨12368071146507009125518703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8245380764338006083679135 12368071146507009125518703)
      ·
        refine ⟨18552106719760513688278055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12368071146507009125518703 18552106719760513688278055)
        ·
          refine ⟨27828160079640770532417083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18552106719760513688278055 27828160079640770532417083)
          ·
            refine ⟨41742240119461155798625625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27828160079640770532417083 41742240119461155798625625)
            ·
              refine ⟨31306680089595866848969219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41742240119461155798625625 31306680089595866848969219)
              ·
                refine ⟨46960020134393800273453829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31306680089595866848969219 46960020134393800273453829)
                ·
                  refine ⟨8805003775198837551272593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46960020134393800273453829 8805003775198837551272593)
                  ·
                    refine ⟨6603752831399128163454445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8805003775198837551272593 6603752831399128163454445)
                    ·
                      refine ⟨2476407311774673061295417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6603752831399128163454445 2476407311774673061295417)
                      ·
                        rfl

theorem cell23_4822786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_4822786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822786 prefixEnd_4822786 := by exact prefixLift 4822786
  have htrace : WordTrace (prefixWord ++ tailWord_4822786) baseStart_4822786 baseEnd_4822786 := by
    simpa [prefixWord, tailWord_4822786, baseEnd_4822786] using wordTrace_append hprefix tailTrace_4822786
  have hstable : (prefixWord ++ tailWord_4822786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822786).length < 2 ^ (prefixWord ++ tailWord_4822786).sum := by decide
  have hdescent : baseEnd_4822786 < baseStart_4822786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822792 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_4822792 : Nat := 118140960795 + 4822792 * 2 ^ 59
def prefixEnd_4822792 : Nat := 4983230072969 + 3 ^ 40 * 4822792 * 2
def baseEnd_4822792 : Nat := 2476410392658600037820389

theorem tailTrace_4822792 : CollatzResearch.WordTrace tailWord_4822792 prefixEnd_4822792 2476410392658600037820389 := by
  unfold tailWord_4822792
  simp only [CollatzResearch.WordTrace]
  refine ⟨87950837571927863071603315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117267783429237150762137753 87950837571927863071603315)
  ·
    refine ⟨131926256357891794607404973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87950837571927863071603315 131926256357891794607404973)
    ·
      refine ⟨49472346134209422977776865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131926256357891794607404973 49472346134209422977776865)
      ·
        refine ⟨37104259600657067233332649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49472346134209422977776865 37104259600657067233332649)
        ·
          refine ⟨27828194700492800424999487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37104259600657067233332649 27828194700492800424999487)
          ·
            refine ⟨41742292050739200637499231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27828194700492800424999487 41742292050739200637499231)
            ·
              refine ⟨62613438076108800956248847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41742292050739200637499231 62613438076108800956248847)
              ·
                refine ⟨93920157114163201434373271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62613438076108800956248847 93920157114163201434373271)
                ·
                  refine ⟨140880235671244802151559907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93920157114163201434373271 140880235671244802151559907)
                  ·
                    refine ⟨211320353506867203227339861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140880235671244802151559907 211320353506867203227339861)
                    ·
                      refine ⟨2476410392658600037820389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 211320353506867203227339861 2476410392658600037820389)
                      ·
                        rfl

theorem cell23_4822792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_4822792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822792 prefixEnd_4822792 := by exact prefixLift 4822792
  have htrace : WordTrace (prefixWord ++ tailWord_4822792) baseStart_4822792 baseEnd_4822792 := by
    simpa [prefixWord, tailWord_4822792, baseEnd_4822792] using wordTrace_append hprefix tailTrace_4822792
  have hstable : (prefixWord ++ tailWord_4822792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822792).length < 2 ^ (prefixWord ++ tailWord_4822792).sum := by decide
  have hdescent : baseEnd_4822792 < baseStart_4822792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822816 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4822816 : Nat := 118140960795 + 4822816 * 2 ^ 59
def prefixEnd_4822816 : Nat := 4983230072969 + 3 ^ 40 * 4822816 * 2
def baseEnd_4822816 : Nat := 2476422716194307943920279

theorem tailTrace_4822816 : CollatzResearch.WordTrace tailWord_4822816 prefixEnd_4822816 2476422716194307943920279 := by
  unfold tailWord_4822816
  simp only [CollatzResearch.WordTrace]
  refine ⟨87951275247884389121040151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117268366997179185494720201 87951275247884389121040151)
  ·
    refine ⟨131926912871826583681560227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87951275247884389121040151 131926912871826583681560227)
    ·
      refine ⟨197890369307739875522340341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131926912871826583681560227 197890369307739875522340341)
      ·
        refine ⟨18552222122600613330219407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197890369307739875522340341 18552222122600613330219407)
        ·
          refine ⟨27828333183900919995329111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18552222122600613330219407 27828333183900919995329111)
          ·
            refine ⟨41742499775851379992993667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27828333183900919995329111 41742499775851379992993667)
            ·
              refine ⟨62613749663777069989490501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41742499775851379992993667 62613749663777069989490501)
              ·
                refine ⟨11740078061958200623029469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62613749663777069989490501 11740078061958200623029469)
                ·
                  refine ⟨4402529273234325233636051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11740078061958200623029469 4402529273234325233636051)
                  ·
                    refine ⟨6603793909851487850454077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402529273234325233636051 6603793909851487850454077)
                    ·
                      refine ⟨2476422716194307943920279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6603793909851487850454077 2476422716194307943920279)
                      ·
                        rfl

theorem cell23_4822816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4822816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822816 prefixEnd_4822816 := by exact prefixLift 4822816
  have htrace : WordTrace (prefixWord ++ tailWord_4822816) baseStart_4822816 baseEnd_4822816 := by
    simpa [prefixWord, tailWord_4822816, baseEnd_4822816] using wordTrace_append hprefix tailTrace_4822816
  have hstable : (prefixWord ++ tailWord_4822816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822816).length < 2 ^ (prefixWord ++ tailWord_4822816).sum := by decide
  have hdescent : baseEnd_4822816 < baseStart_4822816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822819 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 1, 5]
def baseStart_4822819 : Nat := 118140960795 + 4822819 * 2 ^ 59
def prefixEnd_4822819 : Nat := 4983230072969 + 3 ^ 40 * 4822819 * 2
def baseEnd_4822819 : Nat := 825474752212090477394255

theorem tailTrace_4822819 : CollatzResearch.WordTrace tailWord_4822819 prefixEnd_4822819 825474752212090477394255 := by
  unfold tailWord_4822819
  simp only [CollatzResearch.WordTrace]
  refine ⟨175902659914757909754439511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117268439943171939836293007 175902659914757909754439511)
  ·
    refine ⟨263853989872136864631659267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175902659914757909754439511 263853989872136864631659267)
    ·
      refine ⟨395780984808205296947488901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263853989872136864631659267 395780984808205296947488901)
      ·
        refine ⟨74208934651538493177654169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395780984808205296947488901 74208934651538493177654169)
        ·
          refine ⟨55656700988653869883240627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74208934651538493177654169 55656700988653869883240627)
          ·
            refine ⟨83485051482980804824860941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55656700988653869883240627 83485051482980804824860941)
            ·
              refine ⟨31306894306117801809322853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83485051482980804824860941 31306894306117801809322853)
              ·
                refine ⟨5870042682397087839248035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31306894306117801809322853 5870042682397087839248035)
                ·
                  refine ⟨8805064023595631758872053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5870042682397087839248035 8805064023595631758872053)
                  ·
                    refine ⟨825474752212090477394255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8805064023595631758872053 825474752212090477394255)
                    ·
                      rfl

theorem cell23_4822819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 5].length) (baseStart_4822819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822819 prefixEnd_4822819 := by exact prefixLift 4822819
  have htrace : WordTrace (prefixWord ++ tailWord_4822819) baseStart_4822819 baseEnd_4822819 := by
    simpa [prefixWord, tailWord_4822819, baseEnd_4822819] using wordTrace_append hprefix tailTrace_4822819
  have hstable : (prefixWord ++ tailWord_4822819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822819).length < 2 ^ (prefixWord ++ tailWord_4822819).sum := by decide
  have hdescent : baseEnd_4822819 < baseStart_4822819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822869 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4822869 : Nat := 118140960795 + 4822869 * 2 ^ 59
def prefixEnd_4822869 : Nat := 4983230072969 + 3 ^ 40 * 4822869 * 2
def baseEnd_4822869 : Nat := 2476449930668996236557535

theorem tailTrace_4822869 : CollatzResearch.WordTrace tailWord_4822869 prefixEnd_4822869 2476449930668996236557535 := by
  unfold tailWord_4822869
  simp only [CollatzResearch.WordTrace]
  refine ⟨175904483564576768293759661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117269655709717845529173107 175904483564576768293759661)
  ·
    refine ⟨65964181336716288110159873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175904483564576768293759661 65964181336716288110159873)
    ·
      refine ⟨49473136002537216082619905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65964181336716288110159873 49473136002537216082619905)
      ·
        refine ⟨37104852001902912061964929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49473136002537216082619905 37104852001902912061964929)
        ·
          refine ⟨27828639001427184046473697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37104852001902912061964929 27828639001427184046473697)
          ·
            refine ⟨20871479251070388034855273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27828639001427184046473697 20871479251070388034855273)
            ·
              refine ⟨15653609438302791026141455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20871479251070388034855273 15653609438302791026141455)
              ·
                refine ⟨23480414157454186539212183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15653609438302791026141455 23480414157454186539212183)
                ·
                  refine ⟨35220621236181279808818275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23480414157454186539212183 35220621236181279808818275)
                  ·
                    refine ⟨52830931854271919713227413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35220621236181279808818275 52830931854271919713227413)
                    ·
                      refine ⟨2476449930668996236557535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52830931854271919713227413 2476449930668996236557535)
                      ·
                        rfl

theorem cell23_4822869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4822869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822869 prefixEnd_4822869 := by exact prefixLift 4822869
  have htrace : WordTrace (prefixWord ++ tailWord_4822869) baseStart_4822869 baseEnd_4822869 := by
    simpa [prefixWord, tailWord_4822869, baseEnd_4822869] using wordTrace_append hprefix tailTrace_4822869
  have hstable : (prefixWord ++ tailWord_4822869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822869).length < 2 ^ (prefixWord ++ tailWord_4822869).sum := by decide
  have hdescent : baseEnd_4822869 < baseStart_4822869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822906 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_4822906 : Nat := 118140960795 + 4822906 * 2 ^ 59
def prefixEnd_4822906 : Nat := 4983230072969 + 3 ^ 40 * 4822906 * 2
def baseEnd_4822906 : Nat := 2476468929453212591794865

theorem tailTrace_4822906 : CollatzResearch.WordTrace tailWord_4822906 prefixEnd_4822906 2476468929453212591794865 := by
  unfold tailWord_4822906
  simp only [CollatzResearch.WordTrace]
  refine ⟨43976458266360680903214143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117270555376961815741904381 43976458266360680903214143)
  ·
    refine ⟨65964687399541021354821215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43976458266360680903214143 65964687399541021354821215)
    ·
      refine ⟨98947031099311532032231823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65964687399541021354821215 98947031099311532032231823)
      ·
        refine ⟨148420546648967298048347735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98947031099311532032231823 148420546648967298048347735)
        ·
          refine ⟨222630819973450947072521603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148420546648967298048347735 222630819973450947072521603)
          ·
            refine ⟨333946229960176420608782405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222630819973450947072521603 333946229960176420608782405)
            ·
              refine ⟨62614918117533078864146701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 333946229960176420608782405 62614918117533078864146701)
              ·
                refine ⟨23480594294074904574055013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62614918117533078864146701 23480594294074904574055013)
                ·
                  refine ⟨4402611430139044607635315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23480594294074904574055013 4402611430139044607635315)
                  ·
                    refine ⟨6603917145208566911452973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402611430139044607635315 6603917145208566911452973)
                    ·
                      refine ⟨2476468929453212591794865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6603917145208566911452973 2476468929453212591794865)
                      ·
                        rfl

theorem cell23_4822906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_4822906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822906 prefixEnd_4822906 := by exact prefixLift 4822906
  have htrace : WordTrace (prefixWord ++ tailWord_4822906) baseStart_4822906 baseEnd_4822906 := by
    simpa [prefixWord, tailWord_4822906, baseEnd_4822906] using wordTrace_append hprefix tailTrace_4822906
  have hstable : (prefixWord ++ tailWord_4822906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822906).length < 2 ^ (prefixWord ++ tailWord_4822906).sum := by decide
  have hdescent : baseEnd_4822906 < baseStart_4822906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822913 : List Nat := [1, 2, 4, 4, 1, 2, 1, 8]
def baseStart_4822913 : Nat := 118140960795 + 4822913 * 2 ^ 59
def prefixEnd_4822913 : Nat := 4983230072969 + 3 ^ 40 * 4822913 * 2
def baseEnd_4822913 : Nat := 91721204585844224607679

theorem tailTrace_4822913 : CollatzResearch.WordTrace tailWord_4822913 prefixEnd_4822913 91721204585844224607679 := by
  unfold tailWord_4822913
  simp only [CollatzResearch.WordTrace]
  refine ⟨175906088376417363808361393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117270725584278242538907595 175906088376417363808361393)
  ·
    refine ⟨131929566282313022856271045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175906088376417363808361393 131929566282313022856271045)
    ·
      refine ⟨24736793677933691785550821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131929566282313022856271045 24736793677933691785550821)
      ·
        refine ⟨4638148814612567209790779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24736793677933691785550821 4638148814612567209790779)
        ·
          refine ⟨6957223221918850814686169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638148814612567209790779 6957223221918850814686169)
          ·
            refine ⟨5217917416439138111014627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957223221918850814686169 5217917416439138111014627)
            ·
              refine ⟨7826876124658707166521941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217917416439138111014627 7826876124658707166521941)
              ·
                refine ⟨91721204585844224607679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7826876124658707166521941 91721204585844224607679)
                ·
                  rfl

theorem cell23_4822913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 8].length) (baseStart_4822913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822913 prefixEnd_4822913 := by exact prefixLift 4822913
  have htrace : WordTrace (prefixWord ++ tailWord_4822913) baseStart_4822913 baseEnd_4822913 := by
    simpa [prefixWord, tailWord_4822913, baseEnd_4822913] using wordTrace_append hprefix tailTrace_4822913
  have hstable : (prefixWord ++ tailWord_4822913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822913).length < 2 ^ (prefixWord ++ tailWord_4822913).sum := by decide
  have hdescent : baseEnd_4822913 < baseStart_4822913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822933 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_4822933 : Nat := 118140960795 + 4822933 * 2 ^ 59
def prefixEnd_4822933 : Nat := 4983230072969 + 3 ^ 40 * 4822933 * 2
def baseEnd_4822933 : Nat := 2476482793430883986157241

theorem tailTrace_4822933 : CollatzResearch.WordTrace tailWord_4822933 prefixEnd_4822933 2476482793430883986157241 := by
  unfold tailWord_4822933
  simp only [CollatzResearch.WordTrace]
  refine ⟨175906817836344907224089453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117271211890896604816059635 175906817836344907224089453)
  ·
    refine ⟨65965056688629340209033545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175906817836344907224089453 65965056688629340209033545)
    ·
      refine ⟨49473792516472005156775159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65965056688629340209033545 49473792516472005156775159)
      ·
        refine ⟨74210688774708007735162739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49473792516472005156775159 74210688774708007735162739)
        ·
          refine ⟨111316033162062011602744109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74210688774708007735162739 111316033162062011602744109)
          ·
            refine ⟨41743512435773254351029041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111316033162062011602744109 41743512435773254351029041)
            ·
              refine ⟨31307634326829940763271781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41743512435773254351029041 31307634326829940763271781)
              ·
                refine ⟨5870181436280613893113459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31307634326829940763271781 5870181436280613893113459)
                ·
                  refine ⟨8805272154420920839670189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5870181436280613893113459 8805272154420920839670189)
                  ·
                    refine ⟨3301977057907845314876321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8805272154420920839670189 3301977057907845314876321)
                    ·
                      refine ⟨2476482793430883986157241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301977057907845314876321 2476482793430883986157241)
                      ·
                        rfl

theorem cell23_4822933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_4822933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822933 prefixEnd_4822933 := by exact prefixLift 4822933
  have htrace : WordTrace (prefixWord ++ tailWord_4822933) baseStart_4822933 baseEnd_4822933 := by
    simpa [prefixWord, tailWord_4822933, baseEnd_4822933] using wordTrace_append hprefix tailTrace_4822933
  have hstable : (prefixWord ++ tailWord_4822933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822933).length < 2 ^ (prefixWord ++ tailWord_4822933).sum := by decide
  have hdescent : baseEnd_4822933 < baseStart_4822933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822949 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_4822949 : Nat := 118140960795 + 4822949 * 2 ^ 59
def prefixEnd_4822949 : Nat := 4983230072969 + 3 ^ 40 * 4822949 * 2
def baseEnd_4822949 : Nat := 2476491009121355923557167

theorem tailTrace_4822949 : CollatzResearch.WordTrace tailWord_4822949 prefixEnd_4822949 2476491009121355923557167 := by
  unfold tailWord_4822949
  simp only [CollatzResearch.WordTrace]
  refine ⟨175907401404286941956671901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117271600936191294637781267 175907401404286941956671901)
  ·
    refine ⟨65965275526607603233751963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175907401404286941956671901 65965275526607603233751963)
    ·
      refine ⟨98947913289911404850627945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65965275526607603233751963 98947913289911404850627945)
      ·
        refine ⟨74210934967433553637970959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98947913289911404850627945 74210934967433553637970959)
        ·
          refine ⟨111316402451150330456956439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74210934967433553637970959 111316402451150330456956439)
          ·
            refine ⟨166974603676725495685434659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111316402451150330456956439 166974603676725495685434659)
            ·
              refine ⟨250461905515088243528151989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166974603676725495685434659 250461905515088243528151989)
              ·
                refine ⟨23480803642039522830764249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250461905515088243528151989 23480803642039522830764249)
                ·
                  refine ⟨17610602731529642123073187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23480803642039522830764249 17610602731529642123073187)
                  ·
                    refine ⟨26415904097294463184609781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17610602731529642123073187 26415904097294463184609781)
                    ·
                      refine ⟨2476491009121355923557167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26415904097294463184609781 2476491009121355923557167)
                      ·
                        rfl

theorem cell23_4822949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_4822949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822949 prefixEnd_4822949 := by exact prefixLift 4822949
  have htrace : WordTrace (prefixWord ++ tailWord_4822949) baseStart_4822949 baseEnd_4822949 := by
    simpa [prefixWord, tailWord_4822949, baseEnd_4822949] using wordTrace_append hprefix tailTrace_4822949
  have hstable : (prefixWord ++ tailWord_4822949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822949).length < 2 ^ (prefixWord ++ tailWord_4822949).sum := by decide
  have hdescent : baseEnd_4822949 < baseStart_4822949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822959 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_4822959 : Nat := 118140960795 + 4822959 * 2 ^ 59
def prefixEnd_4822959 : Nat := 4983230072969 + 3 ^ 40 * 4822959 * 2
def baseEnd_4822959 : Nat := 2476496143927900884432121

theorem tailTrace_4822959 : CollatzResearch.WordTrace tailWord_4822959 prefixEnd_4822959 2476496143927900884432121 := by
  unfold tailWord_4822959
  simp only [CollatzResearch.WordTrace]
  refine ⟨175907766134250713664535931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117271844089500475776357287 175907766134250713664535931)
  ·
    refine ⟨263861649201376070496803897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175907766134250713664535931 263861649201376070496803897)
    ·
      refine ⟨197896236901032052872602923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263861649201376070496803897 197896236901032052872602923)
      ·
        refine ⟨296844355351548079308904385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197896236901032052872602923 296844355351548079308904385)
        ·
          refine ⟨222633266513661059481678289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296844355351548079308904385 222633266513661059481678289)
          ·
            refine ⟨166974949885245794611258717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222633266513661059481678289 166974949885245794611258717)
            ·
              refine ⟨62615606206967172979222019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166974949885245794611258717 62615606206967172979222019)
              ·
                refine ⟨93923409310450759468833029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62615606206967172979222019 93923409310450759468833029)
                ·
                  refine ⟨17610639245709517400406193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93923409310450759468833029 17610639245709517400406193)
                  ·
                    refine ⟨13207979434282138050304645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17610639245709517400406193 13207979434282138050304645)
                    ·
                      refine ⟨2476496143927900884432121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13207979434282138050304645 2476496143927900884432121)
                      ·
                        rfl

theorem cell23_4822959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_4822959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822959 prefixEnd_4822959 := by exact prefixLift 4822959
  have htrace : WordTrace (prefixWord ++ tailWord_4822959) baseStart_4822959 baseEnd_4822959 := by
    simpa [prefixWord, tailWord_4822959, baseEnd_4822959] using wordTrace_append hprefix tailTrace_4822959
  have hstable : (prefixWord ++ tailWord_4822959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822959).length < 2 ^ (prefixWord ++ tailWord_4822959).sum := by decide
  have hdescent : baseEnd_4822959 < baseStart_4822959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822963 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 4, 2, 2]
def baseStart_4822963 : Nat := 118140960795 + 4822963 * 2 ^ 59
def prefixEnd_4822963 : Nat := 4983230072969 + 3 ^ 40 * 4822963 * 2
def baseEnd_4822963 : Nat := 2476498197850518868782103

theorem tailTrace_4822963 : CollatzResearch.WordTrace tailWord_4822963 prefixEnd_4822963 2476498197850518868782103 := by
  unfold tailWord_4822963
  simp only [CollatzResearch.WordTrace]
  refine ⟨175907912026236222347681543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117271941350824148231787695 175907912026236222347681543)
  ·
    refine ⟨263861868039354333521522315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175907912026236222347681543 263861868039354333521522315)
    ·
      refine ⟨395792802059031500282283473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263861868039354333521522315 395792802059031500282283473)
      ·
        refine ⟨296844601544273625211712605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395792802059031500282283473 296844601544273625211712605)
        ·
          refine ⟨111316725579102609454392227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296844601544273625211712605 111316725579102609454392227)
          ·
            refine ⟨166975088368653914181588341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111316725579102609454392227 166975088368653914181588341)
            ·
              refine ⟨15653914534561304454523907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166975088368653914181588341 15653914534561304454523907)
              ·
                refine ⟨23480871801841956681785861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15653914534561304454523907 23480871801841956681785861)
                ·
                  refine ⟨4402663462845366877834849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23480871801841956681785861 4402663462845366877834849)
                  ·
                    refine ⟨3301997597134025158376137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4402663462845366877834849 3301997597134025158376137)
                    ·
                      refine ⟨2476498197850518868782103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3301997597134025158376137 2476498197850518868782103)
                      ·
                        rfl

theorem cell23_4822963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 2, 2].length) (baseStart_4822963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822963 prefixEnd_4822963 := by exact prefixLift 4822963
  have htrace : WordTrace (prefixWord ++ tailWord_4822963) baseStart_4822963 baseEnd_4822963 := by
    simpa [prefixWord, tailWord_4822963, baseEnd_4822963] using wordTrace_append hprefix tailTrace_4822963
  have hstable : (prefixWord ++ tailWord_4822963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822963).length < 2 ^ (prefixWord ++ tailWord_4822963).sum := by decide
  have hdescent : baseEnd_4822963 < baseStart_4822963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4822999 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 1, 7]
def baseStart_4822999 : Nat := 118140960795 + 4822999 * 2 ^ 59
def prefixEnd_4822999 : Nat := 4983230072969 + 3 ^ 40 * 4822999 * 2
def baseEnd_4822999 : Nat := 825505561051360242643979

theorem tailTrace_4822999 : CollatzResearch.WordTrace tailWord_4822999 prefixEnd_4822999 825505561051360242643979 := by
  unfold tailWord_4822999
  simp only [CollatzResearch.WordTrace]
  refine ⟨175909225054105800495992051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117272816702737200330661367 175909225054105800495992051)
  ·
    refine ⟨263863837581158700743988077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175909225054105800495992051 263863837581158700743988077)
    ·
      refine ⟨98948939092934512778995529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263863837581158700743988077 98948939092934512778995529)
      ·
        refine ⟨74211704319700884584246647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98948939092934512778995529 74211704319700884584246647)
        ·
          refine ⟨111317556479551326876369971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74211704319700884584246647 111317556479551326876369971)
          ·
            refine ⟨166976334719326990314554957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111317556479551326876369971 166976334719326990314554957)
            ·
              refine ⟨62616125519747621367958109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166976334719326990314554957 62616125519747621367958109)
              ·
                refine ⟨23481047069905358012984291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62616125519747621367958109 23481047069905358012984291)
                ·
                  refine ⟨35221570604858037019476437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23481047069905358012984291 35221570604858037019476437)
                  ·
                    refine ⟨825505561051360242643979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35221570604858037019476437 825505561051360242643979)
                    ·
                      rfl

theorem cell23_4822999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_4822999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4822999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4822999 prefixEnd_4822999 := by exact prefixLift 4822999
  have htrace : WordTrace (prefixWord ++ tailWord_4822999) baseStart_4822999 baseEnd_4822999 := by
    simpa [prefixWord, tailWord_4822999, baseEnd_4822999] using wordTrace_append hprefix tailTrace_4822999
  have hstable : (prefixWord ++ tailWord_4822999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4822999).length < 2 ^ (prefixWord ++ tailWord_4822999).sum := by decide
  have hdescent : baseEnd_4822999 < baseStart_4822999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4822999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823036 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_4823036 : Nat := 118140960795 + 4823036 * 2 ^ 59
def prefixEnd_4823036 : Nat := 4983230072969 + 3 ^ 40 * 4823036 * 2
def baseEnd_4823036 : Nat := 2476535681938297083169267

theorem tailTrace_4823036 : CollatzResearch.WordTrace tailWord_4823036 prefixEnd_4823036 2476535681938297083169267 := by
  unfold tailWord_4823036
  simp only [CollatzResearch.WordTrace]
  refine ⟨87955287277485877907544481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117273716369981170543392641 87955287277485877907544481)
  ·
    refine ⟨65966465458114408430658361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87955287277485877907544481 65966465458114408430658361)
    ·
      refine ⟨49474849093585806322993771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65966465458114408430658361 49474849093585806322993771)
      ·
        refine ⟨74212273640378709484490657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49474849093585806322993771 74212273640378709484490657)
        ·
          refine ⟨55659205230284032113367993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74212273640378709484490657 55659205230284032113367993)
          ·
            refine ⟨41744403922713024085025995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55659205230284032113367993 41744403922713024085025995)
            ·
              refine ⟨62616605884069536127538993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41744403922713024085025995 62616605884069536127538993)
              ·
                refine ⟨46962454413052152095654245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62616605884069536127538993 46962454413052152095654245)
                ·
                  refine ⟨8805460202447278517935171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46962454413052152095654245 8805460202447278517935171)
                  ·
                    refine ⟨13208190303670917776902757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8805460202447278517935171 13208190303670917776902757)
                    ·
                      refine ⟨2476535681938297083169267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13208190303670917776902757 2476535681938297083169267)
                      ·
                        rfl

theorem cell23_4823036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_4823036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823036 prefixEnd_4823036 := by exact prefixLift 4823036
  have htrace : WordTrace (prefixWord ++ tailWord_4823036) baseStart_4823036 baseEnd_4823036 := by
    simpa [prefixWord, tailWord_4823036, baseEnd_4823036] using wordTrace_append hprefix tailTrace_4823036
  have hstable : (prefixWord ++ tailWord_4823036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823036).length < 2 ^ (prefixWord ++ tailWord_4823036).sum := by decide
  have hdescent : baseEnd_4823036 < baseStart_4823036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823039 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_4823039 : Nat := 118140960795 + 4823039 * 2 ^ 59
def prefixEnd_4823039 : Nat := 4983230072969 + 3 ^ 40 * 4823039 * 2
def baseEnd_4823039 : Nat := 2476537222380260571431753

theorem tailTrace_4823039 : CollatzResearch.WordTrace tailWord_4823039 prefixEnd_4823039 2476537222380260571431753 := by
  unfold tailWord_4823039
  simp only [CollatzResearch.WordTrace]
  refine ⟨175910683973960887327448171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117273789315973924884965447 175910683973960887327448171)
  ·
    refine ⟨263866025960941330991172257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175910683973960887327448171 263866025960941330991172257)
    ·
      refine ⟨197899519470705998243379193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263866025960941330991172257 197899519470705998243379193)
      ·
        refine ⟨148424639603029498682534395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197899519470705998243379193 148424639603029498682534395)
        ·
          refine ⟨222636959404544248023801593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148424639603029498682534395 222636959404544248023801593)
          ·
            refine ⟨166977719553408186017851195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222636959404544248023801593 166977719553408186017851195)
            ·
              refine ⟨250466579330112279026776793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166977719553408186017851195 250466579330112279026776793)
              ·
                refine ⟨187849934497584209270082595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250466579330112279026776793 187849934497584209270082595)
                ·
                  refine ⟨281774901746376313905123893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187849934497584209270082595 281774901746376313905123893)
                  ·
                    refine ⟨26416397038722779428605365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 281774901746376313905123893 26416397038722779428605365)
                    ·
                      refine ⟨2476537222380260571431753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26416397038722779428605365 2476537222380260571431753)
                      ·
                        rfl

theorem cell23_4823039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_4823039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823039 prefixEnd_4823039 := by exact prefixLift 4823039
  have htrace : WordTrace (prefixWord ++ tailWord_4823039) baseStart_4823039 baseEnd_4823039 := by
    simpa [prefixWord, tailWord_4823039, baseEnd_4823039] using wordTrace_append hprefix tailTrace_4823039
  have hstable : (prefixWord ++ tailWord_4823039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823039).length < 2 ^ (prefixWord ++ tailWord_4823039).sum := by decide
  have hdescent : baseEnd_4823039 < baseStart_4823039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823049 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_4823049 : Nat := 118140960795 + 4823049 * 2 ^ 59
def prefixEnd_4823049 : Nat := 4983230072969 + 3 ^ 40 * 4823049 * 2
def baseEnd_4823049 : Nat := 2476542357186805532306707

theorem tailTrace_4823049 : CollatzResearch.WordTrace tailWord_4823049 prefixEnd_4823049 2476542357186805532306707 := by
  unfold tailWord_4823049
  simp only [CollatzResearch.WordTrace]
  refine ⟨175911048703924659035312201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117274032469283106023541467 175911048703924659035312201)
  ·
    refine ⟨131933286527943494276484151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175911048703924659035312201 131933286527943494276484151)
    ·
      refine ⟨197899929791915241414726227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131933286527943494276484151 197899929791915241414726227)
      ·
        refine ⟨296849894687872862122089341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197899929791915241414726227 296849894687872862122089341)
        ·
          refine ⟨111318710507952323295783503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296849894687872862122089341 111318710507952323295783503)
          ·
            refine ⟨166978065761928484943675255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111318710507952323295783503 166978065761928484943675255)
            ·
              refine ⟨250467098642892727415512883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166978065761928484943675255 250467098642892727415512883)
              ·
                refine ⟨375700647964339091123269325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250467098642892727415512883 375700647964339091123269325)
                ·
                  refine ⟨140887742986627159171225997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375700647964339091123269325 140887742986627159171225997)
                  ·
                    refine ⟨52832903619985184689209749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140887742986627159171225997 52832903619985184689209749)
                    ·
                      refine ⟨2476542357186805532306707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52832903619985184689209749 2476542357186805532306707)
                      ·
                        rfl

theorem cell23_4823049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_4823049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823049 prefixEnd_4823049 := by exact prefixLift 4823049
  have htrace : WordTrace (prefixWord ++ tailWord_4823049) baseStart_4823049 baseEnd_4823049 := by
    simpa [prefixWord, tailWord_4823049, baseEnd_4823049] using wordTrace_append hprefix tailTrace_4823049
  have hstable : (prefixWord ++ tailWord_4823049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823049).length < 2 ^ (prefixWord ++ tailWord_4823049).sum := by decide
  have hdescent : baseEnd_4823049 < baseStart_4823049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823056 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_4823056 : Nat := 118140960795 + 4823056 * 2 ^ 59
def prefixEnd_4823056 : Nat := 4983230072969 + 3 ^ 40 * 4823056 * 2
def baseEnd_4823056 : Nat := 2476545951551387004919175

theorem tailTrace_4823056 : CollatzResearch.WordTrace tailWord_4823056 prefixEnd_4823056 2476545951551387004919175 := by
  unfold tailWord_4823056
  simp only [CollatzResearch.WordTrace]
  refine ⟨87955652007449649615408511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117274202676599532820544681 87955652007449649615408511)
  ·
    refine ⟨131933478011174474423112767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87955652007449649615408511 131933478011174474423112767)
    ·
      refine ⟨197900217016761711634669151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131933478011174474423112767 197900217016761711634669151)
      ·
        refine ⟨296850325525142567452003727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197900217016761711634669151 296850325525142567452003727)
        ·
          refine ⟨445275488287713851178005591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296850325525142567452003727 445275488287713851178005591)
          ·
            refine ⟨667913232431570776767008387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445275488287713851178005591 667913232431570776767008387)
            ·
              refine ⟨1001869848647356165150512581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667913232431570776767008387 1001869848647356165150512581)
              ·
                refine ⟨187850596621379280965721109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1001869848647356165150512581 187850596621379280965721109)
                ·
                  refine ⟨8805496716627153795268177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187850596621379280965721109 8805496716627153795268177)
                  ·
                    refine ⟨6604122537470365346451133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8805496716627153795268177 6604122537470365346451133)
                    ·
                      refine ⟨2476545951551387004919175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6604122537470365346451133 2476545951551387004919175)
                      ·
                        rfl

theorem cell23_4823056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_4823056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823056 prefixEnd_4823056 := by exact prefixLift 4823056
  have htrace : WordTrace (prefixWord ++ tailWord_4823056) baseStart_4823056 baseEnd_4823056 := by
    simpa [prefixWord, tailWord_4823056, baseEnd_4823056] using wordTrace_append hprefix tailTrace_4823056
  have hstable : (prefixWord ++ tailWord_4823056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823056).length < 2 ^ (prefixWord ++ tailWord_4823056).sum := by decide
  have hdescent : baseEnd_4823056 < baseStart_4823056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823059 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 10]
def baseStart_4823059 : Nat := 118140960795 + 4823059 * 2 ^ 59
def prefixEnd_4823059 : Nat := 4983230072969 + 3 ^ 40 * 4823059 * 2
def baseEnd_4823059 : Nat := 275171943554816721464629

theorem tailTrace_4823059 : CollatzResearch.WordTrace tailWord_4823059 prefixEnd_4823059 275171943554816721464629 := by
  unfold tailWord_4823059
  simp only [CollatzResearch.WordTrace]
  refine ⟨175911413433888430743176231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117274275622592287162117487 175911413433888430743176231)
  ·
    refine ⟨263867120150832646114764347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175911413433888430743176231 263867120150832646114764347)
    ·
      refine ⟨395800680226248969172146521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263867120150832646114764347 395800680226248969172146521)
      ·
        refine ⟨296850510169686726879109891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395800680226248969172146521 296850510169686726879109891)
        ·
          refine ⟨445275765254530090318664837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296850510169686726879109891 445275765254530090318664837)
          ·
            refine ⟨83489205985224391934749657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 445275765254530090318664837 83489205985224391934749657)
            ·
              refine ⟨62616904488918293951062243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83489205985224391934749657 62616904488918293951062243)
              ·
                refine ⟨93925356733377440926593365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62616904488918293951062243 93925356733377440926593365)
                ·
                  refine ⟨275171943554816721464629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 93925356733377440926593365 275171943554816721464629)
                  ·
                    rfl

theorem cell23_4823059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 10].length) (baseStart_4823059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823059 prefixEnd_4823059 := by exact prefixLift 4823059
  have htrace : WordTrace (prefixWord ++ tailWord_4823059) baseStart_4823059 baseEnd_4823059 := by
    simpa [prefixWord, tailWord_4823059, baseEnd_4823059] using wordTrace_append hprefix tailTrace_4823059
  have hstable : (prefixWord ++ tailWord_4823059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823059).length < 2 ^ (prefixWord ++ tailWord_4823059).sum := by decide
  have hdescent : baseEnd_4823059 < baseStart_4823059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823103 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 3]
def baseStart_4823103 : Nat := 118140960795 + 4823103 * 2 ^ 59
def prefixEnd_4823103 : Nat := 4983230072969 + 3 ^ 40 * 4823103 * 2
def baseEnd_4823103 : Nat := 2476570085142148321031459

theorem tailTrace_4823103 : CollatzResearch.WordTrace tailWord_4823103 prefixEnd_4823103 2476570085142148321031459 := by
  unfold tailWord_4823103
  simp only [CollatzResearch.WordTrace]
  refine ⟨175913018245729026257777963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117275345497152684171851975 175913018245729026257777963)
  ·
    refine ⟨263869527368593539386666945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175913018245729026257777963 263869527368593539386666945)
    ·
      refine ⟨197902145526445154540000209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263869527368593539386666945 197902145526445154540000209)
      ·
        refine ⟨148426609144833865905000157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197902145526445154540000209 148426609144833865905000157)
        ·
          refine ⟨55659978429312699714375059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148426609144833865905000157 55659978429312699714375059)
          ·
            refine ⟨83489967643969049571562589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55659978429312699714375059 83489967643969049571562589)
            ·
              refine ⟨31308737866488393589335971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83489967643969049571562589 31308737866488393589335971)
              ·
                refine ⟨46963106799732590384003957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31308737866488393589335971 46963106799732590384003957)
                ·
                  refine ⟨4402791262474930348500371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46963106799732590384003957 4402791262474930348500371)
                  ·
                    refine ⟨6604186893712395522750557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402791262474930348500371 6604186893712395522750557)
                    ·
                      refine ⟨2476570085142148321031459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6604186893712395522750557 2476570085142148321031459)
                      ·
                        rfl

theorem cell23_4823103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_4823103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823103 prefixEnd_4823103 := by exact prefixLift 4823103
  have htrace : WordTrace (prefixWord ++ tailWord_4823103) baseStart_4823103 baseEnd_4823103 := by
    simpa [prefixWord, tailWord_4823103, baseEnd_4823103] using wordTrace_append hprefix tailTrace_4823103
  have hstable : (prefixWord ++ tailWord_4823103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823103).length < 2 ^ (prefixWord ++ tailWord_4823103).sum := by decide
  have hdescent : baseEnd_4823103 < baseStart_4823103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823113 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 1, 5, 2]
def baseStart_4823113 : Nat := 118140960795 + 4823113 * 2 ^ 59
def prefixEnd_4823113 : Nat := 4983230072969 + 3 ^ 40 * 4823113 * 2
def baseEnd_4823113 : Nat := 2476575219948693281906413

theorem tailTrace_4823113 : CollatzResearch.WordTrace tailWord_4823113 prefixEnd_4823113 2476575219948693281906413 := by
  unfold tailWord_4823113
  simp only [CollatzResearch.WordTrace]
  refine ⟨175913382975692797965641993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117275588650461865310427995 175913382975692797965641993)
  ·
    refine ⟨131935037231769598474231495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175913382975692797965641993 131935037231769598474231495)
    ·
      refine ⟨197902555847654397711347243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131935037231769598474231495 197902555847654397711347243)
      ·
        refine ⟨296853833771481596567020865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197902555847654397711347243 296853833771481596567020865)
        ·
          refine ⟨222640375328611197425265649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296853833771481596567020865 222640375328611197425265649)
          ·
            refine ⟨166980281496458398068949237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222640375328611197425265649 166980281496458398068949237)
            ·
              refine ⟨15654401390292974818963991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166980281496458398068949237 15654401390292974818963991)
              ·
                refine ⟨23481602085439462228445987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15654401390292974818963991 23481602085439462228445987)
                ·
                  refine ⟨35222403128159193342668981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23481602085439462228445987 35222403128159193342668981)
                  ·
                    refine ⟨3302100293264924375875217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35222403128159193342668981 3302100293264924375875217)
                    ·
                      refine ⟨2476575219948693281906413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302100293264924375875217 2476575219948693281906413)
                      ·
                        rfl

theorem cell23_4823113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 5, 2].length) (baseStart_4823113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823113 prefixEnd_4823113 := by exact prefixLift 4823113
  have htrace : WordTrace (prefixWord ++ tailWord_4823113) baseStart_4823113 baseEnd_4823113 := by
    simpa [prefixWord, tailWord_4823113, baseEnd_4823113] using wordTrace_append hprefix tailTrace_4823113
  have hstable : (prefixWord ++ tailWord_4823113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823113).length < 2 ^ (prefixWord ++ tailWord_4823113).sum := by decide
  have hdescent : baseEnd_4823113 < baseStart_4823113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823188 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4823188 : Nat := 118140960795 + 4823188 * 2 ^ 59
def prefixEnd_4823188 : Nat := 4983230072969 + 3 ^ 40 * 4823188 * 2
def baseEnd_4823188 : Nat := 2476613730997780488468569

theorem tailTrace_4823188 : CollatzResearch.WordTrace tailWord_4823188 prefixEnd_4823188 2476613730997780488468569 := by
  unfold tailWord_4823188
  simp only [CollatzResearch.WordTrace]
  refine ⟨87958059225210542887311109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117277412300280723849748145 87958059225210542887311109)
  ·
    refine ⟨16492136104726976791370833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87958059225210542887311109 16492136104726976791370833)
    ·
      refine ⟨12369102078545232593528125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16492136104726976791370833 12369102078545232593528125)
      ·
        refine ⟨4638413279454462222573047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12369102078545232593528125 4638413279454462222573047)
        ·
          refine ⟨6957619919181693333859571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638413279454462222573047 6957619919181693333859571)
          ·
            refine ⟨10436429878772540000789357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6957619919181693333859571 10436429878772540000789357)
            ·
              refine ⟨3913661204539702500296009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10436429878772540000789357 3913661204539702500296009)
              ·
                refine ⟨2935245903404776875222007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3913661204539702500296009 2935245903404776875222007)
                ·
                  refine ⟨4402868855107165312833011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935245903404776875222007 4402868855107165312833011)
                  ·
                    refine ⟨6604303282660747969249517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402868855107165312833011 6604303282660747969249517)
                    ·
                      refine ⟨2476613730997780488468569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6604303282660747969249517 2476613730997780488468569)
                      ·
                        rfl

theorem cell23_4823188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4823188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823188 prefixEnd_4823188 := by exact prefixLift 4823188
  have htrace : WordTrace (prefixWord ++ tailWord_4823188) baseStart_4823188 baseEnd_4823188 := by
    simpa [prefixWord, tailWord_4823188, baseEnd_4823188] using wordTrace_append hprefix tailTrace_4823188
  have hstable : (prefixWord ++ tailWord_4823188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823188).length < 2 ^ (prefixWord ++ tailWord_4823188).sum := by decide
  have hdescent : baseEnd_4823188 < baseStart_4823188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823203 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 9, 2]
def baseStart_4823203 : Nat := 118140960795 + 4823203 * 2 ^ 59
def prefixEnd_4823203 : Nat := 4983230072969 + 3 ^ 40 * 4823203 * 2
def baseEnd_4823203 : Nat := 2476621433207597929780999

theorem tailTrace_4823203 : CollatzResearch.WordTrace tailWord_4823203 prefixEnd_4823203 2476621433207597929780999 := by
  unfold tailWord_4823203
  simp only [CollatzResearch.WordTrace]
  refine ⟨175916665545366743336418263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117277777030244495557612175 175916665545366743336418263)
  ·
    refine ⟨263874998318050115004627395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175916665545366743336418263 263874998318050115004627395)
    ·
      refine ⟨395812497477075172506941093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263874998318050115004627395 395812497477075172506941093)
      ·
        refine ⟨74214843276951594845051455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395812497477075172506941093 74214843276951594845051455)
        ·
          refine ⟨111322264915427392267577183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74214843276951594845051455 111322264915427392267577183)
          ·
            refine ⟨166983397373141088401365775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111322264915427392267577183 166983397373141088401365775)
            ·
              refine ⟨250475096059711632602048663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166983397373141088401365775 250475096059711632602048663)
              ·
                refine ⟨375712644089567448903072995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250475096059711632602048663 375712644089567448903072995)
                ·
                  refine ⟨563568966134351173354609493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375712644089567448903072995 563568966134351173354609493)
                  ·
                    refine ⟨3302161910943463906374665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 563568966134351173354609493 3302161910943463906374665)
                    ·
                      refine ⟨2476621433207597929780999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302161910943463906374665 2476621433207597929780999)
                      ·
                        rfl

theorem cell23_4823203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_4823203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823203 prefixEnd_4823203 := by exact prefixLift 4823203
  have htrace : WordTrace (prefixWord ++ tailWord_4823203) baseStart_4823203 baseEnd_4823203 := by
    simpa [prefixWord, tailWord_4823203, baseEnd_4823203] using wordTrace_append hprefix tailTrace_4823203
  have hstable : (prefixWord ++ tailWord_4823203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823203).length < 2 ^ (prefixWord ++ tailWord_4823203).sum := by decide
  have hdescent : baseEnd_4823203 < baseStart_4823203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823204 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_4823204 : Nat := 118140960795 + 4823204 * 2 ^ 59
def prefixEnd_4823204 : Nat := 4983230072969 + 3 ^ 40 * 4823204 * 2
def baseEnd_4823204 : Nat := 825540648896084141956165

theorem tailTrace_4823204 : CollatzResearch.WordTrace tailWord_4823204 prefixEnd_4823204 825540648896084141956165 := by
  unfold tailWord_4823204
  simp only [CollatzResearch.WordTrace]
  refine ⟨87958351009181560253602333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117277801345575413671469777 87958351009181560253602333)
  ·
    refine ⟨32984381628443085095100875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87958351009181560253602333 32984381628443085095100875)
    ·
      refine ⟨49476572442664627642651313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32984381628443085095100875 49476572442664627642651313)
      ·
        refine ⟨37107429331998470731988485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49476572442664627642651313 37107429331998470731988485)
        ·
          refine ⟨6957642999749713262247841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37107429331998470731988485 6957642999749713262247841)
          ·
            refine ⟨5218232249812284946685881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957642999749713262247841 5218232249812284946685881)
            ·
              refine ⟨3913674187359213710014411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5218232249812284946685881 3913674187359213710014411)
              ·
                refine ⟨5870511281038820565021617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913674187359213710014411 5870511281038820565021617)
                ·
                  refine ⟨4402883460779115423766213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5870511281038820565021617 4402883460779115423766213)
                  ·
                    refine ⟨825540648896084141956165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4402883460779115423766213 825540648896084141956165)
                    ·
                      rfl

theorem cell23_4823204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_4823204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823204 prefixEnd_4823204 := by exact prefixLift 4823204
  have htrace : WordTrace (prefixWord ++ tailWord_4823204) baseStart_4823204 baseEnd_4823204 := by
    simpa [prefixWord, tailWord_4823204, baseEnd_4823204] using wordTrace_append hprefix tailTrace_4823204
  have hstable : (prefixWord ++ tailWord_4823204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823204).length < 2 ^ (prefixWord ++ tailWord_4823204).sum := by decide
  have hdescent : baseEnd_4823204 < baseStart_4823204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823214 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4823214 : Nat := 118140960795 + 4823214 * 2 ^ 59
def prefixEnd_4823214 : Nat := 4983230072969 + 3 ^ 40 * 4823214 * 2
def baseEnd_4823214 : Nat := 2476627081494797386743449

theorem tailTrace_4823214 : CollatzResearch.WordTrace tailWord_4823214 prefixEnd_4823214 2476627081494797386743449 := by
  unfold tailWord_4823214
  simp only [CollatzResearch.WordTrace]
  refine ⟨21989633343540861526883587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117278044498884594810045797 21989633343540861526883587)
  ·
    refine ⟨32984450015311292290325381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21989633343540861526883587 32984450015311292290325381)
    ·
      refine ⟨6184584377870867304436009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32984450015311292290325381 6184584377870867304436009)
      ·
        refine ⟨4638438283403150478327007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6184584377870867304436009 4638438283403150478327007)
        ·
          refine ⟨6957657425104725717490511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638438283403150478327007 6957657425104725717490511)
          ·
            refine ⟨10436486137657088576235767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6957657425104725717490511 10436486137657088576235767)
            ·
              refine ⟨15654729206485632864353651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10436486137657088576235767 15654729206485632864353651)
              ·
                refine ⟨23482093809728449296530477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15654729206485632864353651 23482093809728449296530477)
                ·
                  refine ⟨8805785178648168486198929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23482093809728449296530477 8805785178648168486198929)
                  ·
                    refine ⟨6604338883986126364649197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8805785178648168486198929 6604338883986126364649197)
                    ·
                      refine ⟨2476627081494797386743449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6604338883986126364649197 2476627081494797386743449)
                      ·
                        rfl

theorem cell23_4823214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4823214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823214 prefixEnd_4823214 := by exact prefixLift 4823214
  have htrace : WordTrace (prefixWord ++ tailWord_4823214) baseStart_4823214 baseEnd_4823214 := by
    simpa [prefixWord, tailWord_4823214, baseEnd_4823214] using wordTrace_append hprefix tailTrace_4823214
  have hstable : (prefixWord ++ tailWord_4823214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823214).length < 2 ^ (prefixWord ++ tailWord_4823214).sum := by decide
  have hdescent : baseEnd_4823214 < baseStart_4823214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823254 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4823254 : Nat := 118140960795 + 4823254 * 2 ^ 59
def prefixEnd_4823254 : Nat := 4983230072969 + 3 ^ 40 * 4823254 * 2
def baseEnd_4823254 : Nat := 2476647620720977230243265

theorem tailTrace_4823254 : CollatzResearch.WordTrace tailWord_4823254 prefixEnd_4823254 2476647620720977230243265 := by
  unfold tailWord_4823254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994907854261373690407801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117279017112121319364349877 10994907854261373690407801)
  ·
    refine ⟨8246180890696030267805851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10994907854261373690407801 8246180890696030267805851)
    ·
      refine ⟨12369271336044045401708777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8246180890696030267805851 12369271336044045401708777)
      ·
        refine ⟨9276953502033034051281583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12369271336044045401708777 9276953502033034051281583)
        ·
          refine ⟨13915430253049551076922375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9276953502033034051281583 13915430253049551076922375)
          ·
            refine ⟨20873145379574326615383563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13915430253049551076922375 20873145379574326615383563)
            ·
              refine ⟨31309718069361489923075345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20873145379574326615383563 31309718069361489923075345)
              ·
                refine ⟨23482288552021117442306509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31309718069361489923075345 23482288552021117442306509)
                ·
                  refine ⟨8805858207007919040864941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23482288552021117442306509 8805858207007919040864941)
                  ·
                    refine ⟨3302196827627969640324353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8805858207007919040864941 3302196827627969640324353)
                    ·
                      refine ⟨2476647620720977230243265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302196827627969640324353 2476647620720977230243265)
                      ·
                        rfl

theorem cell23_4823254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4823254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823254 prefixEnd_4823254 := by exact prefixLift 4823254
  have htrace : WordTrace (prefixWord ++ tailWord_4823254) baseStart_4823254 baseEnd_4823254 := by
    simpa [prefixWord, tailWord_4823254, baseEnd_4823254] using wordTrace_append hprefix tailTrace_4823254
  have hstable : (prefixWord ++ tailWord_4823254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823254).length < 2 ^ (prefixWord ++ tailWord_4823254).sum := by decide
  have hdescent : baseEnd_4823254 < baseStart_4823254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823283 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 3]
def baseStart_4823283 : Nat := 118140960795 + 4823283 * 2 ^ 59
def prefixEnd_4823283 : Nat := 4983230072969 + 3 ^ 40 * 4823283 * 2
def baseEnd_4823283 : Nat := 2476662511659957616780631

theorem tailTrace_4823283 : CollatzResearch.WordTrace tailWord_4823283 prefixEnd_4823283 2476662511659957616780631 := by
  unfold tailWord_4823283
  simp only [CollatzResearch.WordTrace]
  refine ⟨175919583385076916999330503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117279722256717944666220335 175919583385076916999330503)
  ·
    refine ⟨263879375077615375498995755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175919583385076916999330503 263879375077615375498995755)
    ·
      refine ⟨395819062616423063248493633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263879375077615375498995755 395819062616423063248493633)
      ·
        refine ⟨296864296962317297436370225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395819062616423063248493633 296864296962317297436370225)
        ·
          refine ⟨222648222721737973077277669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296864296962317297436370225 222648222721737973077277669)
          ·
            refine ⟨41746541760325869951989563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222648222721737973077277669 41746541760325869951989563)
            ·
              refine ⟨62619812640488804927984345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41746541760325869951989563 62619812640488804927984345)
              ·
                refine ⟨46964859480366603695988259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62619812640488804927984345 46964859480366603695988259)
                ·
                  refine ⟨70447289220549905543982389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46964859480366603695988259 70447289220549905543982389)
                  ·
                    refine ⟨6604433364426553644748349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70447289220549905543982389 6604433364426553644748349)
                    ·
                      refine ⟨2476662511659957616780631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6604433364426553644748349 2476662511659957616780631)
                      ·
                        rfl

theorem cell23_4823283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_4823283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823283 prefixEnd_4823283 := by exact prefixLift 4823283
  have htrace : WordTrace (prefixWord ++ tailWord_4823283) baseStart_4823283 baseEnd_4823283 := by
    simpa [prefixWord, tailWord_4823283, baseEnd_4823283] using wordTrace_append hprefix tailTrace_4823283
  have hstable : (prefixWord ++ tailWord_4823283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823283).length < 2 ^ (prefixWord ++ tailWord_4823283).sum := by decide
  have hdescent : baseEnd_4823283 < baseStart_4823283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823290 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 5]
def baseStart_4823290 : Nat := 118140960795 + 4823290 * 2 ^ 59
def prefixEnd_4823290 : Nat := 4983230072969 + 3 ^ 40 * 4823290 * 2
def baseEnd_4823290 : Nat := 275185122891615454377011

theorem tailTrace_4823290 : CollatzResearch.WordTrace tailWord_4823290 prefixEnd_4823290 275185122891615454377011 := by
  unfold tailWord_4823290
  simp only [CollatzResearch.WordTrace]
  refine ⟨43979959674012889298708831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117279892464034371463223549 43979959674012889298708831)
  ·
    refine ⟨65969939511019333948063247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43979959674012889298708831 65969939511019333948063247)
    ·
      refine ⟨98954909266529000922094871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65969939511019333948063247 98954909266529000922094871)
      ·
        refine ⟨148432363899793501383142307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98954909266529000922094871 148432363899793501383142307)
        ·
          refine ⟨222648545849690252074713461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148432363899793501383142307 222648545849690252074713461)
          ·
            refine ⟨20873301173408461132004387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222648545849690252074713461 20873301173408461132004387)
            ·
              refine ⟨31309951760112691698006581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20873301173408461132004387 31309951760112691698006581)
              ·
                refine ⟨2935307977510564846688117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31309951760112691698006581 2935307977510564846688117)
                ·
                  refine ⟨275185122891615454377011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2935307977510564846688117 275185122891615454377011)
                  ·
                    rfl

theorem cell23_4823290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_4823290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823290 prefixEnd_4823290 := by exact prefixLift 4823290
  have htrace : WordTrace (prefixWord ++ tailWord_4823290) baseStart_4823290 baseEnd_4823290 := by
    simpa [prefixWord, tailWord_4823290, baseEnd_4823290] using wordTrace_append hprefix tailTrace_4823290
  have hstable : (prefixWord ++ tailWord_4823290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823290).length < 2 ^ (prefixWord ++ tailWord_4823290).sum := by decide
  have hdescent : baseEnd_4823290 < baseStart_4823290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823323 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4]
def baseStart_4823323 : Nat := 118140960795 + 4823323 * 2 ^ 59
def prefixEnd_4823323 : Nat := 4983230072969 + 3 ^ 40 * 4823323 * 2
def baseEnd_4823323 : Nat := 2476683050886137460280447

theorem tailTrace_4823323 : CollatzResearch.WordTrace tailWord_4823323 prefixEnd_4823323 2476683050886137460280447 := by
  unfold tailWord_4823323
  simp only [CollatzResearch.WordTrace]
  refine ⟨175921042304932003830786623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117280694869954669220524415 175921042304932003830786623)
  ·
    refine ⟨263881563457398005746179935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175921042304932003830786623 263881563457398005746179935)
    ·
      refine ⟨395822345186097008619269903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263881563457398005746179935 395822345186097008619269903)
      ·
        refine ⟨593733517779145512928904855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395822345186097008619269903 593733517779145512928904855)
        ·
          refine ⟨890600276668718269393357283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593733517779145512928904855 890600276668718269393357283)
          ·
            refine ⟨1335900415003077404090035925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890600276668718269393357283 1335900415003077404090035925)
            ·
              refine ⟨31310165976634626658360217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1335900415003077404090035925 31310165976634626658360217)
              ·
                refine ⟨23482624482475969993770163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31310165976634626658360217 23482624482475969993770163)
                ·
                  refine ⟨35223936723713954990655245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23482624482475969993770163 35223936723713954990655245)
                  ·
                    refine ⟨13208976271392733121495717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35223936723713954990655245 13208976271392733121495717)
                    ·
                      refine ⟨2476683050886137460280447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13208976271392733121495717 2476683050886137460280447)
                      ·
                        rfl

theorem cell23_4823323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_4823323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823323 prefixEnd_4823323 := by exact prefixLift 4823323
  have htrace : WordTrace (prefixWord ++ tailWord_4823323) baseStart_4823323 baseEnd_4823323 := by
    simpa [prefixWord, tailWord_4823323, baseEnd_4823323] using wordTrace_append hprefix tailTrace_4823323
  have hstable : (prefixWord ++ tailWord_4823323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823323).length < 2 ^ (prefixWord ++ tailWord_4823323).sum := by decide
  have hdescent : baseEnd_4823323 < baseStart_4823323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823340 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 6, 2]
def baseStart_4823340 : Nat := 118140960795 + 4823340 * 2 ^ 59
def prefixEnd_4823340 : Nat := 4983230072969 + 3 ^ 40 * 4823340 * 2
def baseEnd_4823340 : Nat := 2476691780057263893767869

theorem tailTrace_4823340 : CollatzResearch.WordTrace tailWord_4823340 prefixEnd_4823340 2476691780057263893767869 := by
  unfold tailWord_4823340
  simp only [CollatzResearch.WordTrace]
  refine ⟨87960831172935207867077737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117281108230580277156103649 87960831172935207867077737)
  ·
    refine ⟨65970623379701405900308303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87960831172935207867077737 65970623379701405900308303)
    ·
      refine ⟨98955935069552108850462455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65970623379701405900308303 98955935069552108850462455)
      ·
        refine ⟨148433902604328163275693683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98955935069552108850462455 148433902604328163275693683)
        ·
          refine ⟨222650853906492244913540525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148433902604328163275693683 222650853906492244913540525)
          ·
            refine ⟨83494070214934591842577697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222650853906492244913540525 83494070214934591842577697)
            ·
              refine ⟨62620552661200943881933273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83494070214934591842577697 62620552661200943881933273)
              ·
                refine ⟨46965414495900707911449955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62620552661200943881933273 46965414495900707911449955)
                ·
                  refine ⟨70448121743851061867174933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46965414495900707911449955 70448121743851061867174933)
                  ·
                    refine ⟨3302255706743018525023825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70448121743851061867174933 3302255706743018525023825)
                    ·
                      refine ⟨2476691780057263893767869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302255706743018525023825 2476691780057263893767869)
                      ·
                        rfl

theorem cell23_4823340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_4823340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823340 prefixEnd_4823340 := by exact prefixLift 4823340
  have htrace : WordTrace (prefixWord ++ tailWord_4823340) baseStart_4823340 baseEnd_4823340 := by
    simpa [prefixWord, tailWord_4823340, baseEnd_4823340] using wordTrace_append hprefix tailTrace_4823340
  have hstable : (prefixWord ++ tailWord_4823340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823340).length < 2 ^ (prefixWord ++ tailWord_4823340).sum := by decide
  have hdescent : baseEnd_4823340 < baseStart_4823340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823341 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 5]
def baseStart_4823341 : Nat := 118140960795 + 4823341 * 2 ^ 59
def prefixEnd_4823341 : Nat := 4983230072969 + 3 ^ 40 * 4823341 * 2
def baseEnd_4823341 : Nat := 275188032615324265539485

theorem tailTrace_4823341 : CollatzResearch.WordTrace tailWord_4823341 prefixEnd_4823341 275188032615324265539485 := by
  unfold tailWord_4823341
  simp only [CollatzResearch.WordTrace]
  refine ⟨175921698818866792904941877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117281132545911195269961251 175921698818866792904941877)
  ·
    refine ⟨16492659264268761834838301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175921698818866792904941877 16492659264268761834838301)
    ·
      refine ⟨6184747224100785688064363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16492659264268761834838301 6184747224100785688064363)
      ·
        refine ⟨9277120836151178532096545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6184747224100785688064363 9277120836151178532096545)
        ·
          refine ⟨6957840627113383899072409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9277120836151178532096545 6957840627113383899072409)
          ·
            refine ⟨5218380470335037924304307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957840627113383899072409 5218380470335037924304307)
            ·
              refine ⟨7827570705502556886456461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218380470335037924304307 7827570705502556886456461)
              ·
                refine ⟨2935339014563458832421173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7827570705502556886456461 2935339014563458832421173)
                ·
                  refine ⟨275188032615324265539485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2935339014563458832421173 275188032615324265539485)
                  ·
                    rfl

theorem cell23_4823341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_4823341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823341 prefixEnd_4823341 := by exact prefixLift 4823341
  have htrace : WordTrace (prefixWord ++ tailWord_4823341) baseStart_4823341 baseEnd_4823341 := by
    simpa [prefixWord, tailWord_4823341, baseEnd_4823341] using wordTrace_append hprefix tailTrace_4823341
  have hstable : (prefixWord ++ tailWord_4823341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823341).length < 2 ^ (prefixWord ++ tailWord_4823341).sum := by decide
  have hdescent : baseEnd_4823341 < baseStart_4823341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823363 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 8]
def baseStart_4823363 : Nat := 118140960795 + 4823363 * 2 ^ 59
def prefixEnd_4823363 : Nat := 4983230072969 + 3 ^ 40 * 4823363 * 2
def baseEnd_4823363 : Nat := 275189287790257478197807

theorem tailTrace_4823363 : CollatzResearch.WordTrace tailWord_4823363 prefixEnd_4823363 275189287790257478197807 := by
  unfold tailWord_4823363
  simp only [CollatzResearch.WordTrace]
  refine ⟨175922501224787090662242743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117281667483191393774828495 175922501224787090662242743)
  ·
    refine ⟨263883751837180635993364115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175922501224787090662242743 263883751837180635993364115)
    ·
      refine ⟨395825627755770953990046173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263883751837180635993364115 395825627755770953990046173)
      ·
        refine ⟨148434610408414107746267315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395825627755770953990046173 148434610408414107746267315)
        ·
          refine ⟨222651915612621161619400973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148434610408414107746267315 222651915612621161619400973)
          ·
            refine ⟨83494468354732935607275365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222651915612621161619400973 83494468354732935607275365)
            ·
              refine ⟨15655212816512425426364131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83494468354732935607275365 15655212816512425426364131)
              ·
                refine ⟨23482819224768638139546197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15655212816512425426364131 23482819224768638139546197)
                ·
                  refine ⟨275189287790257478197807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23482819224768638139546197 275189287790257478197807)
                  ·
                    rfl

theorem cell23_4823363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 8].length) (baseStart_4823363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823363 prefixEnd_4823363 := by exact prefixLift 4823363
  have htrace : WordTrace (prefixWord ++ tailWord_4823363) baseStart_4823363 baseEnd_4823363 := by
    simpa [prefixWord, tailWord_4823363, baseEnd_4823363] using wordTrace_append hprefix tailTrace_4823363
  have hstable : (prefixWord ++ tailWord_4823363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823363).length < 2 ^ (prefixWord ++ tailWord_4823363).sum := by decide
  have hdescent : baseEnd_4823363 < baseStart_4823363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823394 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_4823394 : Nat := 118140960795 + 4823394 * 2 ^ 59
def prefixEnd_4823394 : Nat := 4983230072969 + 3 ^ 40 * 4823394 * 2
def baseEnd_4823394 : Nat := 2476719508012606682492621

theorem tailTrace_4823394 : CollatzResearch.WordTrace tailWord_4823394 prefixEnd_4823394 2476719508012606682492621 := by
  unfold tailWord_4823394
  simp only [CollatzResearch.WordTrace]
  refine ⟨43980907971918695739155309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117282421258449855304414157 43980907971918695739155309)
  ·
    refine ⟨16492840489469510902183241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43980907971918695739155309 16492840489469510902183241)
    ·
      refine ⟨12369630367102133176637431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16492840489469510902183241 12369630367102133176637431)
      ·
        refine ⟨18554445550653199764956147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12369630367102133176637431 18554445550653199764956147)
        ·
          refine ⟨27831668325979799647434221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18554445550653199764956147 27831668325979799647434221)
          ·
            refine ⟨10436875622242424867787833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27831668325979799647434221 10436875622242424867787833)
            ·
              refine ⟨7827656716681818650840875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10436875622242424867787833 7827656716681818650840875)
              ·
                refine ⟨11741485075022727976261313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7827656716681818650840875 11741485075022727976261313)
                ·
                  refine ⟨8806113806267045982195985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11741485075022727976261313 8806113806267045982195985)
                  ·
                    refine ⟨6604585354700284486646989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8806113806267045982195985 6604585354700284486646989)
                    ·
                      refine ⟨2476719508012606682492621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6604585354700284486646989 2476719508012606682492621)
                      ·
                        rfl

theorem cell23_4823394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_4823394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823394 prefixEnd_4823394 := by exact prefixLift 4823394
  have htrace : WordTrace (prefixWord ++ tailWord_4823394) baseStart_4823394 baseEnd_4823394 := by
    simpa [prefixWord, tailWord_4823394, baseEnd_4823394] using wordTrace_append hprefix tailTrace_4823394
  have hstable : (prefixWord ++ tailWord_4823394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823394).length < 2 ^ (prefixWord ++ tailWord_4823394).sum := by decide
  have hdescent : baseEnd_4823394 < baseStart_4823394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823481 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 3, 2, 2]
def baseStart_4823481 : Nat := 118140960795 + 4823481 * 2 ^ 59
def prefixEnd_4823481 : Nat := 4983230072969 + 3 ^ 40 * 4823481 * 2
def baseEnd_4823481 : Nat := 2476764180829547842104721

theorem tailTrace_4823481 : CollatzResearch.WordTrace tailWord_4823481 prefixEnd_4823481 2476764180829547842104721 := by
  unfold tailWord_4823481
  simp only [CollatzResearch.WordTrace]
  refine ⟨175926805038359596815038297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117284536692239731210025531 175926805038359596815038297)
  ·
    refine ⟨131945103778769697611278723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175926805038359596815038297 131945103778769697611278723)
    ·
      refine ⟨197917655668154546416918085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131945103778769697611278723 197917655668154546416918085)
      ·
        refine ⟨37109560437778977453172141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197917655668154546416918085 37109560437778977453172141)
        ·
          refine ⟨13916085164167116544939553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37109560437778977453172141 13916085164167116544939553)
          ·
            refine ⟨10437063873125337408704665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13916085164167116544939553 10437063873125337408704665)
            ·
              refine ⟨7827797904844003056528499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10437063873125337408704665 7827797904844003056528499)
              ·
                refine ⟨11741696857266004584792749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7827797904844003056528499 11741696857266004584792749)
                ·
                  refine ⟨4403136321474751719297281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11741696857266004584792749 4403136321474751719297281)
                  ·
                    refine ⟨3302352241106063789472961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4403136321474751719297281 3302352241106063789472961)
                    ·
                      refine ⟨2476764180829547842104721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302352241106063789472961 2476764180829547842104721)
                      ·
                        rfl

theorem cell23_4823481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_4823481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823481 prefixEnd_4823481 := by exact prefixLift 4823481
  have htrace : WordTrace (prefixWord ++ tailWord_4823481) baseStart_4823481 baseEnd_4823481 := by
    simpa [prefixWord, tailWord_4823481, baseEnd_4823481] using wordTrace_append hprefix tailTrace_4823481
  have hstable : (prefixWord ++ tailWord_4823481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823481).length < 2 ^ (prefixWord ++ tailWord_4823481).sum := by decide
  have hdescent : baseEnd_4823481 < baseStart_4823481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823497 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_4823497 : Nat := 118140960795 + 4823497 * 2 ^ 59
def prefixEnd_4823497 : Nat := 4983230072969 + 3 ^ 40 * 4823497 * 2
def baseEnd_4823497 : Nat := 2476772396520019779504647

theorem tailTrace_4823497 : CollatzResearch.WordTrace tailWord_4823497 prefixEnd_4823497 2476772396520019779504647 := by
  unfold tailWord_4823497
  simp only [CollatzResearch.WordTrace]
  refine ⟨175927388606301631547620745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117284925737534421031747163 175927388606301631547620745)
  ·
    refine ⟨131945541454726223660715559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175927388606301631547620745 131945541454726223660715559)
    ·
      refine ⟨197918312182089335491073339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131945541454726223660715559 197918312182089335491073339)
      ·
        refine ⟨296877468273134003236610009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197918312182089335491073339 296877468273134003236610009)
        ·
          refine ⟨222658101204850502427457507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296877468273134003236610009 222658101204850502427457507)
          ·
            refine ⟨333987151807275753641186261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222658101204850502427457507 333987151807275753641186261)
            ·
              refine ⟨7827823870483025475965303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 333987151807275753641186261 7827823870483025475965303)
              ·
                refine ⟨11741735805724538213947955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7827823870483025475965303 11741735805724538213947955)
                ·
                  refine ⟨17612603708586807320921933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11741735805724538213947955 17612603708586807320921933)
                  ·
                    refine ⟨6604726390720052745345725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17612603708586807320921933 6604726390720052745345725)
                    ·
                      refine ⟨2476772396520019779504647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6604726390720052745345725 2476772396520019779504647)
                      ·
                        rfl

theorem cell23_4823497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_4823497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823497 prefixEnd_4823497 := by exact prefixLift 4823497
  have htrace : WordTrace (prefixWord ++ tailWord_4823497) baseStart_4823497 baseEnd_4823497 := by
    simpa [prefixWord, tailWord_4823497, baseEnd_4823497] using wordTrace_append hprefix tailTrace_4823497
  have hstable : (prefixWord ++ tailWord_4823497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823497).length < 2 ^ (prefixWord ++ tailWord_4823497).sum := by decide
  have hdescent : baseEnd_4823497 < baseStart_4823497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823507 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 9, 3, 2]
def baseStart_4823507 : Nat := 118140960795 + 4823507 * 2 ^ 59
def prefixEnd_4823507 : Nat := 4983230072969 + 3 ^ 40 * 4823507 * 2
def baseEnd_4823507 : Nat := 2476777531326564740379601

theorem tailTrace_4823507 : CollatzResearch.WordTrace tailWord_4823507 prefixEnd_4823507 2476777531326564740379601 := by
  unfold tailWord_4823507
  simp only [CollatzResearch.WordTrace]
  refine ⟨175927753336265403255484775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117285168890843602170323183 175927753336265403255484775)
  ·
    refine ⟨263891630004398104883227163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175927753336265403255484775 263891630004398104883227163)
    ·
      refine ⟨395837445006597157324840745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263891630004398104883227163 395837445006597157324840745)
      ·
        refine ⟨296878083754947867993630559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395837445006597157324840745 296878083754947867993630559)
        ·
          refine ⟨445317125632421801990445839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296878083754947867993630559 445317125632421801990445839)
          ·
            refine ⟨667975688448632702985668759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445317125632421801990445839 667975688448632702985668759)
            ·
              refine ⟨1001963532672949054478503139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667975688448632702985668759 1001963532672949054478503139)
              ·
                refine ⟨1502945299009423581717754709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001963532672949054478503139 1502945299009423581717754709)
                ·
                  refine ⟨8806320111383341299127469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1502945299009423581717754709 8806320111383341299127469)
                  ·
                    refine ⟨3302370041768752987172801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8806320111383341299127469 3302370041768752987172801)
                    ·
                      refine ⟨2476777531326564740379601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302370041768752987172801 2476777531326564740379601)
                      ·
                        rfl

theorem cell23_4823507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3, 2].length) (baseStart_4823507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823507 prefixEnd_4823507 := by exact prefixLift 4823507
  have htrace : WordTrace (prefixWord ++ tailWord_4823507) baseStart_4823507 baseEnd_4823507 := by
    simpa [prefixWord, tailWord_4823507, baseEnd_4823507] using wordTrace_append hprefix tailTrace_4823507
  have hstable : (prefixWord ++ tailWord_4823507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823507).length < 2 ^ (prefixWord ++ tailWord_4823507).sum := by decide
  have hdescent : baseEnd_4823507 < baseStart_4823507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823560 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 9]
def baseStart_4823560 : Nat := 118140960795 + 4823560 * 2 ^ 59
def prefixEnd_4823560 : Nat := 4983230072969 + 3 ^ 40 * 4823560 * 2
def baseEnd_4823560 : Nat := 275200527311250337001873

theorem tailTrace_4823560 : CollatzResearch.WordTrace tailWord_4823560 prefixEnd_4823560 275200527311250337001873 := by
  unfold tailWord_4823560
  simp only [CollatzResearch.WordTrace]
  refine ⟨87964843202536696653582067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117286457603382262204776089 87964843202536696653582067)
  ·
    refine ⟨131947264803805044980373101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87964843202536696653582067 131947264803805044980373101)
    ·
      refine ⟨49480224301426891867639913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131947264803805044980373101 49480224301426891867639913)
      ·
        refine ⟨37110168226070168900729935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49480224301426891867639913 37110168226070168900729935)
        ·
          refine ⟨55665252339105253351094903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37110168226070168900729935 55665252339105253351094903)
          ·
            refine ⟨83497878508657880026642355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55665252339105253351094903 83497878508657880026642355)
            ·
              refine ⟨125246817762986820039963533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83497878508657880026642355 125246817762986820039963533)
              ·
                refine ⟨46967556661120057514986325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125246817762986820039963533 46967556661120057514986325)
                ·
                  refine ⟨275200527311250337001873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46967556661120057514986325 275200527311250337001873)
                  ·
                    rfl

theorem cell23_4823560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 9].length) (baseStart_4823560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823560 prefixEnd_4823560 := by exact prefixLift 4823560
  have htrace : WordTrace (prefixWord ++ tailWord_4823560) baseStart_4823560 baseEnd_4823560 := by
    simpa [prefixWord, tailWord_4823560, baseEnd_4823560] using wordTrace_append hprefix tailTrace_4823560
  have hstable : (prefixWord ++ tailWord_4823560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823560).length < 2 ^ (prefixWord ++ tailWord_4823560).sum := by decide
  have hdescent : baseEnd_4823560 < baseStart_4823560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823575 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4823575 : Nat := 118140960795 + 4823575 * 2 ^ 59
def prefixEnd_4823575 : Nat := 4983230072969 + 3 ^ 40 * 4823575 * 2
def baseEnd_4823575 : Nat := 2476812448011070474329289

theorem tailTrace_4823575 : CollatzResearch.WordTrace tailWord_4823575 prefixEnd_4823575 2476812448011070474329289 := by
  unfold tailWord_4823575
  simp only [CollatzResearch.WordTrace]
  refine ⟨175930233500019050868960179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117286822333346033912640119 175930233500019050868960179)
  ·
    refine ⟨263895350250028576303440269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175930233500019050868960179 263895350250028576303440269)
    ·
      refine ⟨98960756343760716113790101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263895350250028576303440269 98960756343760716113790101)
      ·
        refine ⟨4638785453613783567833911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98960756343760716113790101 4638785453613783567833911)
        ·
          refine ⟨6958178180420675351750867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638785453613783567833911 6958178180420675351750867)
          ·
            refine ⟨10437267270631013027626301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6958178180420675351750867 10437267270631013027626301)
            ·
              refine ⟨3913975226486629885359863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10437267270631013027626301 3913975226486629885359863)
              ·
                refine ⟨5870962839729944828039795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913975226486629885359863 5870962839729944828039795)
                ·
                  refine ⟨8806444259594917242059693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5870962839729944828039795 8806444259594917242059693)
                  ·
                    refine ⟨3302416597348093965772385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8806444259594917242059693 3302416597348093965772385)
                    ·
                      refine ⟨2476812448011070474329289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302416597348093965772385 2476812448011070474329289)
                      ·
                        rfl

theorem cell23_4823575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4823575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823575 prefixEnd_4823575 := by exact prefixLift 4823575
  have htrace : WordTrace (prefixWord ++ tailWord_4823575) baseStart_4823575 baseEnd_4823575 := by
    simpa [prefixWord, tailWord_4823575, baseEnd_4823575] using wordTrace_append hprefix tailTrace_4823575
  have hstable : (prefixWord ++ tailWord_4823575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823575).length < 2 ^ (prefixWord ++ tailWord_4823575).sum := by decide
  have hdescent : baseEnd_4823575 < baseStart_4823575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823661 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_4823661 : Nat := 118140960795 + 4823661 * 2 ^ 59
def prefixEnd_4823661 : Nat := 4983230072969 + 3 ^ 40 * 4823661 * 2
def baseEnd_4823661 : Nat := 2476856607347357137853893

theorem tailTrace_4823661 : CollatzResearch.WordTrace tailWord_4823661 prefixEnd_4823661 2476856607347357137853893 := by
  unfold tailWord_4823661
  simp only [CollatzResearch.WordTrace]
  refine ⟨175933370177707487556590837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117288913451804991704393891 175933370177707487556590837)
  ·
    refine ⟨16493753454160076958430391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175933370177707487556590837 16493753454160076958430391)
    ·
      refine ⟨24740630181240115437645587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16493753454160076958430391 24740630181240115437645587)
      ·
        refine ⟨37110945271860173156468381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24740630181240115437645587 37110945271860173156468381)
        ·
          refine ⟨13916604476947564933675643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37110945271860173156468381 13916604476947564933675643)
          ·
            refine ⟨20874906715421347400513465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13916604476947564933675643 20874906715421347400513465)
            ·
              refine ⟨15656180036566010550385099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20874906715421347400513465 15656180036566010550385099)
              ·
                refine ⟨23484270054849015825577649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15656180036566010550385099 23484270054849015825577649)
                ·
                  refine ⟨17613202541136761869183237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23484270054849015825577649 17613202541136761869183237)
                  ·
                    refine ⟨3302475476463142850471857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17613202541136761869183237 3302475476463142850471857)
                    ·
                      refine ⟨2476856607347357137853893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302475476463142850471857 2476856607347357137853893)
                      ·
                        rfl

theorem cell23_4823661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_4823661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823661 prefixEnd_4823661 := by exact prefixLift 4823661
  have htrace : WordTrace (prefixWord ++ tailWord_4823661) baseStart_4823661 baseEnd_4823661 := by
    simpa [prefixWord, tailWord_4823661, baseEnd_4823661] using wordTrace_append hprefix tailTrace_4823661
  have hstable : (prefixWord ++ tailWord_4823661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823661).length < 2 ^ (prefixWord ++ tailWord_4823661).sum := by decide
  have hdescent : baseEnd_4823661 < baseStart_4823661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823717 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_4823717 : Nat := 118140960795 + 4823717 * 2 ^ 59
def prefixEnd_4823717 : Nat := 4983230072969 + 3 ^ 40 * 4823717 * 2
def baseEnd_4823717 : Nat := 2476885362264008918753635

theorem tailTrace_4823717 : CollatzResearch.WordTrace tailWord_4823717 prefixEnd_4823717 2476885362264008918753635 := by
  unfold tailWord_4823717
  simp only [CollatzResearch.WordTrace]
  refine ⟨175935412665504609120629405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117290275110336406080419603 175935412665504609120629405)
  ·
    refine ⟨65975779749564228420236027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175935412665504609120629405 65975779749564228420236027)
    ·
      refine ⟨98963669624346342630354041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65975779749564228420236027 98963669624346342630354041)
      ·
        refine ⟨74222752218259756972765531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98963669624346342630354041 74222752218259756972765531)
        ·
          refine ⟨111334128327389635459148297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74222752218259756972765531 111334128327389635459148297)
          ·
            refine ⟨83500596245542226594361223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111334128327389635459148297 83500596245542226594361223)
            ·
              refine ⟨125250894368313339891541835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83500596245542226594361223 125250894368313339891541835)
              ·
                refine ⟨187876341552470009837312753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125250894368313339891541835 187876341552470009837312753)
                ·
                  refine ⟨140907256164352507377984565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187876341552470009837312753 140907256164352507377984565)
                  ·
                    refine ⟨13210055265408047566686053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 140907256164352507377984565 13210055265408047566686053)
                    ·
                      refine ⟨2476885362264008918753635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13210055265408047566686053 2476885362264008918753635)
                      ·
                        rfl

theorem cell23_4823717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_4823717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823717 prefixEnd_4823717 := by exact prefixLift 4823717
  have htrace : WordTrace (prefixWord ++ tailWord_4823717) baseStart_4823717 baseEnd_4823717 := by
    simpa [prefixWord, tailWord_4823717, baseEnd_4823717] using wordTrace_append hprefix tailTrace_4823717
  have hstable : (prefixWord ++ tailWord_4823717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823717).length < 2 ^ (prefixWord ++ tailWord_4823717).sum := by decide
  have hdescent : baseEnd_4823717 < baseStart_4823717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823731 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 1, 5]
def baseStart_4823731 : Nat := 118140960795 + 4823731 * 2 ^ 59
def prefixEnd_4823731 : Nat := 4983230072969 + 3 ^ 40 * 4823731 * 2
def baseEnd_4823731 : Nat := 825630850331057287992857

theorem tailTrace_4823731 : CollatzResearch.WordTrace tailWord_4823731 prefixEnd_4823731 825630850331057287992857 := by
  unfold tailWord_4823731
  simp only [CollatzResearch.WordTrace]
  refine ⟨175935923287453889511639047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117290615524969259674426031 175935923287453889511639047)
  ·
    refine ⟨263903884931180834267458571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175935923287453889511639047 263903884931180834267458571)
    ·
      refine ⟨395855827396771251401187857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263903884931180834267458571 395855827396771251401187857)
      ·
        refine ⟨296891870547578438550890893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395855827396771251401187857 296891870547578438550890893)
        ·
          refine ⟨111334451455341914456584085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296891870547578438550890893 111334451455341914456584085)
          ·
            refine ⟨5218802411969152240152379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111334451455341914456584085 5218802411969152240152379)
            ·
              refine ⟨7828203617953728360228569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218802411969152240152379 7828203617953728360228569)
              ·
                refine ⟨5871152713465296270171427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7828203617953728360228569 5871152713465296270171427)
                ·
                  refine ⟨8806729070197944405257141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871152713465296270171427 8806729070197944405257141)
                  ·
                    refine ⟨825630850331057287992857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8806729070197944405257141 825630850331057287992857)
                    ·
                      rfl

theorem cell23_4823731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 5].length) (baseStart_4823731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823731 prefixEnd_4823731 := by exact prefixLift 4823731
  have htrace : WordTrace (prefixWord ++ tailWord_4823731) baseStart_4823731 baseEnd_4823731 := by
    simpa [prefixWord, tailWord_4823731, baseEnd_4823731] using wordTrace_append hprefix tailTrace_4823731
  have hstable : (prefixWord ++ tailWord_4823731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823731).length < 2 ^ (prefixWord ++ tailWord_4823731).sum := by decide
  have hdescent : baseEnd_4823731 < baseStart_4823731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823744 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 1, 6]
def baseStart_4823744 : Nat := 118140960795 + 4823744 * 2 ^ 59
def prefixEnd_4823744 : Nat := 4983230072969 + 3 ^ 40 * 4823744 * 2
def baseEnd_4823744 : Nat := 825633075413893437705337

theorem tailTrace_4823744 : CollatzResearch.WordTrace tailWord_4823744 prefixEnd_4823744 825633075413893437705337 := by
  unfold tailWord_4823744
  simp only [CollatzResearch.WordTrace]
  refine ⟨87968198718203396365931143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117290931624271195154574857 87968198718203396365931143)
  ·
    refine ⟨131952298077305094548896715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87968198718203396365931143 131952298077305094548896715)
    ·
      refine ⟨197928447115957641823345073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131952298077305094548896715 197928447115957641823345073)
      ·
        refine ⟨148446335336968231367508805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197928447115957641823345073 148446335336968231367508805)
        ·
          refine ⟨27833687875681543381407901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148446335336968231367508805 27833687875681543381407901)
          ·
            refine ⟨10437632953380578768027963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27833687875681543381407901 10437632953380578768027963)
            ·
              refine ⟨15656449430070868152041945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10437632953380578768027963 15656449430070868152041945)
              ·
                refine ⟨11742337072553151114031459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15656449430070868152041945 11742337072553151114031459)
                ·
                  refine ⟨17613505608829726671047189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11742337072553151114031459 17613505608829726671047189)
                  ·
                    refine ⟨825633075413893437705337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17613505608829726671047189 825633075413893437705337)
                    ·
                      rfl

theorem cell23_4823744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_4823744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823744 prefixEnd_4823744 := by exact prefixLift 4823744
  have htrace : WordTrace (prefixWord ++ tailWord_4823744) baseStart_4823744 baseEnd_4823744 := by
    simpa [prefixWord, tailWord_4823744, baseEnd_4823744] using wordTrace_append hprefix tailTrace_4823744
  have hstable : (prefixWord ++ tailWord_4823744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823744).length < 2 ^ (prefixWord ++ tailWord_4823744).sum := by decide
  have hdescent : baseEnd_4823744 < baseStart_4823744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823748 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_4823748 : Nat := 118140960795 + 4823748 * 2 ^ 59
def prefixEnd_4823748 : Nat := 4983230072969 + 3 ^ 40 * 4823748 * 2
def baseEnd_4823748 : Nat := 825633760054766099155331

theorem tailTrace_4823748 : CollatzResearch.WordTrace tailWord_4823748 prefixEnd_4823748 825633760054766099155331 := by
  unfold tailWord_4823748
  simp only [CollatzResearch.WordTrace]
  refine ⟨87968271664196150707503949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117291028885594867610005265 87968271664196150707503949)
  ·
    refine ⟨32988101874073556515313981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87968271664196150707503949 32988101874073556515313981)
    ·
      refine ⟨12370538202777583693242743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32988101874073556515313981 12370538202777583693242743)
      ·
        refine ⟨18555807304166375539864115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12370538202777583693242743 18555807304166375539864115)
        ·
          refine ⟨27833710956249563309796173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18555807304166375539864115 27833710956249563309796173)
          ·
            refine ⟨10437641608593586241173565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27833710956249563309796173 10437641608593586241173565)
            ·
              refine ⟨3914115603222594840440087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10437641608593586241173565 3914115603222594840440087)
              ·
                refine ⟨5871173404833892260660131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914115603222594840440087 5871173404833892260660131)
                ·
                  refine ⟨8806760107250838390990197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871173404833892260660131 8806760107250838390990197)
                  ·
                    refine ⟨825633760054766099155331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8806760107250838390990197 825633760054766099155331)
                    ·
                      rfl

theorem cell23_4823748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_4823748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823748 prefixEnd_4823748 := by exact prefixLift 4823748
  have htrace : WordTrace (prefixWord ++ tailWord_4823748) baseStart_4823748 baseEnd_4823748 := by
    simpa [prefixWord, tailWord_4823748, baseEnd_4823748] using wordTrace_append hprefix tailTrace_4823748
  have hstable : (prefixWord ++ tailWord_4823748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823748).length < 2 ^ (prefixWord ++ tailWord_4823748).sum := by decide
  have hdescent : baseEnd_4823748 < baseStart_4823748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823751 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_4823751 : Nat := 118140960795 + 4823751 * 2 ^ 59
def prefixEnd_4823751 : Nat := 4983230072969 + 3 ^ 40 * 4823751 * 2
def baseEnd_4823751 : Nat := 2476902820606261785728479

theorem tailTrace_4823751 : CollatzResearch.WordTrace tailWord_4823751 prefixEnd_4823751 2476902820606261785728479 := by
  unfold tailWord_4823751
  simp only [CollatzResearch.WordTrace]
  refine ⟨175936652747381432927367107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117291101831587621951578071 175936652747381432927367107)
  ·
    refine ⟨263904979121072149391050661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175936652747381432927367107 263904979121072149391050661)
    ·
      refine ⟨49482183585201028010821999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263904979121072149391050661 49482183585201028010821999)
      ·
        refine ⟨74223275377801542016232999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49482183585201028010821999 74223275377801542016232999)
        ·
          refine ⟨111334913066702313024349499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74223275377801542016232999 111334913066702313024349499)
          ·
            refine ⟨167002369600053469536524249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111334913066702313024349499 167002369600053469536524249)
            ·
              refine ⟨125251777200040102152393187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167002369600053469536524249 125251777200040102152393187)
              ·
                refine ⟨187877665800060153228589781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125251777200040102152393187 187877665800060153228589781)
                ·
                  refine ⟨4403382792188909841295073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 187877665800060153228589781 4403382792188909841295073)
                  ·
                    refine ⟨3302537094141682380971305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4403382792188909841295073 3302537094141682380971305)
                    ·
                      refine ⟨2476902820606261785728479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302537094141682380971305 2476902820606261785728479)
                      ·
                        rfl

theorem cell23_4823751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_4823751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823751 prefixEnd_4823751 := by exact prefixLift 4823751
  have htrace : WordTrace (prefixWord ++ tailWord_4823751) baseStart_4823751 baseEnd_4823751 := by
    simpa [prefixWord, tailWord_4823751, baseEnd_4823751] using wordTrace_append hprefix tailTrace_4823751
  have hstable : (prefixWord ++ tailWord_4823751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823751).length < 2 ^ (prefixWord ++ tailWord_4823751).sum := by decide
  have hdescent : baseEnd_4823751 < baseStart_4823751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823761 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 2, 4]
def baseStart_4823761 : Nat := 118140960795 + 4823761 * 2 ^ 59
def prefixEnd_4823761 : Nat := 4983230072969 + 3 ^ 40 * 4823761 * 2
def baseEnd_4823761 : Nat := 825635985137602248867811

theorem tailTrace_4823761 : CollatzResearch.WordTrace tailWord_4823761 prefixEnd_4823761 825635985137602248867811 := by
  unfold tailWord_4823761
  simp only [CollatzResearch.WordTrace]
  refine ⟨175937017477345204635231137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117291344984896803090154091 175937017477345204635231137)
  ·
    refine ⟨131952763108008903476423353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175937017477345204635231137 131952763108008903476423353)
    ·
      refine ⟨98964572331006677607317515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131952763108008903476423353 98964572331006677607317515)
      ·
        refine ⟨148446858496510016410976273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98964572331006677607317515 148446858496510016410976273)
        ·
          refine ⟨111335143872382512308232205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148446858496510016410976273 111335143872382512308232205)
          ·
            refine ⟨41750678952143442115587077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111335143872382512308232205 41750678952143442115587077)
            ·
              refine ⟨7828252303526895396672577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41750678952143442115587077 7828252303526895396672577)
              ·
                refine ⟨5871189227645171547504433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7828252303526895396672577 5871189227645171547504433)
                ·
                  refine ⟨4403391920733878660628325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5871189227645171547504433 4403391920733878660628325)
                  ·
                    refine ⟨825635985137602248867811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4403391920733878660628325 825635985137602248867811)
                    ·
                      rfl

theorem cell23_4823761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_4823761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823761 prefixEnd_4823761 := by exact prefixLift 4823761
  have htrace : WordTrace (prefixWord ++ tailWord_4823761) baseStart_4823761 baseEnd_4823761 := by
    simpa [prefixWord, tailWord_4823761, baseEnd_4823761] using wordTrace_append hprefix tailTrace_4823761
  have hstable : (prefixWord ++ tailWord_4823761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823761).length < 2 ^ (prefixWord ++ tailWord_4823761).sum := by decide
  have hdescent : baseEnd_4823761 < baseStart_4823761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823781 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4823781 : Nat := 118140960795 + 4823781 * 2 ^ 59
def prefixEnd_4823781 : Nat := 4983230072969 + 3 ^ 40 * 4823781 * 2
def baseEnd_4823781 : Nat := 2476918225025896668353341

theorem tailTrace_4823781 : CollatzResearch.WordTrace tailWord_4823781 prefixEnd_4823781 2476918225025896668353341 := by
  unfold tailWord_4823781
  simp only [CollatzResearch.WordTrace]
  refine ⟨175937746937272748050959197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117291831291515165367306131 175937746937272748050959197)
  ·
    refine ⟨65976655101477280519109699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175937746937272748050959197 65976655101477280519109699)
    ·
      refine ⟨98964982652215920778664549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65976655101477280519109699 98964982652215920778664549)
      ·
        refine ⟨18555934247290485145999603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98964982652215920778664549 18555934247290485145999603)
        ·
          refine ⟨27833901370935727718999405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18555934247290485145999603 27833901370935727718999405)
          ·
            refine ⟨10437713014100897894624777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27833901370935727718999405 10437713014100897894624777)
            ·
              refine ⟨7828284760575673420968583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10437713014100897894624777 7828284760575673420968583)
              ·
                refine ⟨11742427140863510131452875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7828284760575673420968583 11742427140863510131452875)
                ·
                  refine ⟨17613640711295265197179313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11742427140863510131452875 17613640711295265197179313)
                  ·
                    refine ⟨13210230533471448897884485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17613640711295265197179313 13210230533471448897884485)
                    ·
                      refine ⟨2476918225025896668353341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13210230533471448897884485 2476918225025896668353341)
                      ·
                        rfl

theorem cell23_4823781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4823781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823781 prefixEnd_4823781 := by exact prefixLift 4823781
  have htrace : WordTrace (prefixWord ++ tailWord_4823781) baseStart_4823781 baseEnd_4823781 := by
    simpa [prefixWord, tailWord_4823781, baseEnd_4823781] using wordTrace_append hprefix tailTrace_4823781
  have hstable : (prefixWord ++ tailWord_4823781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823781).length < 2 ^ (prefixWord ++ tailWord_4823781).sum := by decide
  have hdescent : baseEnd_4823781 < baseStart_4823781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823787 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 4, 7]
def baseStart_4823787 : Nat := 118140960795 + 4823787 * 2 ^ 59
def prefixEnd_4823787 : Nat := 4983230072969 + 3 ^ 40 * 4823787 * 2
def baseEnd_4823787 : Nat := 825640435303274548292771

theorem tailTrace_4823787 : CollatzResearch.WordTrace tailWord_4823787 prefixEnd_4823787 825640435303274548292771 := by
  unfold tailWord_4823787
  simp only [CollatzResearch.WordTrace]
  refine ⟨175937965775251011075677615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117291977183500674050451743 175937965775251011075677615)
  ·
    refine ⟨263906948662876516613516423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175937965775251011075677615 263906948662876516613516423)
    ·
      refine ⟨395860422994314774920274635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263906948662876516613516423 395860422994314774920274635)
      ·
        refine ⟨593790634491472162380411953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395860422994314774920274635 593790634491472162380411953)
        ·
          refine ⟨445342975868604121785308965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 593790634491472162380411953 445342975868604121785308965)
          ·
            refine ⟨83501807975363272834745431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 445342975868604121785308965 83501807975363272834745431)
            ·
              refine ⟨125252711963044909252118147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83501807975363272834745431 125252711963044909252118147)
              ·
                refine ⟨187879067944567363878177221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125252711963044909252118147 187879067944567363878177221)
                ·
                  refine ⟨35227325239606380727158229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187879067944567363878177221 35227325239606380727158229)
                  ·
                    refine ⟨825640435303274548292771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35227325239606380727158229 825640435303274548292771)
                    ·
                      rfl

theorem cell23_4823787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_4823787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823787 prefixEnd_4823787 := by exact prefixLift 4823787
  have htrace : WordTrace (prefixWord ++ tailWord_4823787) baseStart_4823787 baseEnd_4823787 := by
    simpa [prefixWord, tailWord_4823787, baseEnd_4823787] using wordTrace_append hprefix tailTrace_4823787
  have hstable : (prefixWord ++ tailWord_4823787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823787).length < 2 ^ (prefixWord ++ tailWord_4823787).sum := by decide
  have hdescent : baseEnd_4823787 < baseStart_4823787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823834 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_4823834 : Nat := 118140960795 + 4823834 * 2 ^ 59
def prefixEnd_4823834 : Nat := 4983230072969 + 3 ^ 40 * 4823834 * 2
def baseEnd_4823834 : Nat := 825648479833528320330199

theorem tailTrace_4823834 : CollatzResearch.WordTrace tailWord_4823834 prefixEnd_4823834 825648479833528320330199 := by
  unfold tailWord_4823834
  simp only [CollatzResearch.WordTrace]
  refine ⟨43984920001520184525659639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117293120004053825401759037 43984920001520184525659639)
  ·
    refine ⟨65977380002280276788489459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43984920001520184525659639 65977380002280276788489459)
    ·
      refine ⟨98966070003420415182734189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65977380002280276788489459 98966070003420415182734189)
      ·
        refine ⟨37112276251282655693525321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98966070003420415182734189 37112276251282655693525321)
        ·
          refine ⟨27834207188461991770143991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37112276251282655693525321 27834207188461991770143991)
          ·
            refine ⟨41751310782692987655215987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27834207188461991770143991 41751310782692987655215987)
            ·
              refine ⟨62626966174039481482823981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41751310782692987655215987 62626966174039481482823981)
              ·
                refine ⟨23485112315264805556058993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62626966174039481482823981 23485112315264805556058993)
                ·
                  refine ⟨17613834236448604167044245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23485112315264805556058993 17613834236448604167044245)
                  ·
                    refine ⟨825648479833528320330199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17613834236448604167044245 825648479833528320330199)
                    ·
                      rfl

theorem cell23_4823834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_4823834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823834 prefixEnd_4823834 := by exact prefixLift 4823834
  have htrace : WordTrace (prefixWord ++ tailWord_4823834) baseStart_4823834 baseEnd_4823834 := by
    simpa [prefixWord, tailWord_4823834, baseEnd_4823834] using wordTrace_append hprefix tailTrace_4823834
  have hstable : (prefixWord ++ tailWord_4823834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823834).length < 2 ^ (prefixWord ++ tailWord_4823834).sum := by decide
  have hdescent : baseEnd_4823834 < baseStart_4823834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823853 : List Nat := [1, 5, 3, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4823853 : Nat := 118140960795 + 4823853 * 2 ^ 59
def prefixEnd_4823853 : Nat := 4983230072969 + 3 ^ 40 * 4823853 * 2
def baseEnd_4823853 : Nat := 2476955195633020386653011

theorem tailTrace_4823853 : CollatzResearch.WordTrace tailWord_4823853 prefixEnd_4823853 2476955195633020386653011 := by
  unfold tailWord_4823853
  simp only [CollatzResearch.WordTrace]
  refine ⟨175940372993011904347580213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117293581995341269565053475 175940372993011904347580213)
  ·
    refine ⟨16494409968094866032585645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 175940372993011904347580213 16494409968094866032585645)
    ·
      refine ⟨6185403738035574762219617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16494409968094866032585645 6185403738035574762219617)
      ·
        refine ⟨4639052803526681071664713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6185403738035574762219617 4639052803526681071664713)
        ·
          refine ⟨3479289602645010803748535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4639052803526681071664713 3479289602645010803748535)
          ·
            refine ⟨5218934403967516205622803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479289602645010803748535 5218934403967516205622803)
            ·
              refine ⟨7828401605951274308434205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218934403967516205622803 7828401605951274308434205)
              ·
                refine ⟨2935650602231727865662827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7828401605951274308434205 2935650602231727865662827)
                ·
                  refine ⟨4403475903347591798494241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935650602231727865662827 4403475903347591798494241)
                  ·
                    refine ⟨3302606927510693848870681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4403475903347591798494241 3302606927510693848870681)
                    ·
                      refine ⟨2476955195633020386653011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302606927510693848870681 2476955195633020386653011)
                      ·
                        rfl

theorem cell23_4823853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4823853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823853 prefixEnd_4823853 := by exact prefixLift 4823853
  have htrace : WordTrace (prefixWord ++ tailWord_4823853) baseStart_4823853 baseEnd_4823853 := by
    simpa [prefixWord, tailWord_4823853, baseEnd_4823853] using wordTrace_append hprefix tailTrace_4823853
  have hstable : (prefixWord ++ tailWord_4823853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823853).length < 2 ^ (prefixWord ++ tailWord_4823853).sum := by decide
  have hdescent : baseEnd_4823853 < baseStart_4823853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823858 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_4823858 : Nat := 118140960795 + 4823858 * 2 ^ 59
def prefixEnd_4823858 : Nat := 4983230072969 + 3 ^ 40 * 4823858 * 2
def baseEnd_4823858 : Nat := 2476957763036292867090487

theorem tailTrace_4823858 : CollatzResearch.WordTrace tailWord_4823858 prefixEnd_4823858 2476957763036292867090487 := by
  unfold tailWord_4823858
  simp only [CollatzResearch.WordTrace]
  refine ⟨43985138839498447550378057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117293703571995860134341485 43985138839498447550378057)
  ·
    refine ⟨32988854129623835662783543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43985138839498447550378057 32988854129623835662783543)
    ·
      refine ⟨49483281194435753494175315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32988854129623835662783543 49483281194435753494175315)
      ·
        refine ⟨74224921791653630241262973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49483281194435753494175315 74224921791653630241262973)
        ·
          refine ⟨27834345671870111340473615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74224921791653630241262973 27834345671870111340473615)
          ·
            refine ⟨41751518507805167010710423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27834345671870111340473615 41751518507805167010710423)
            ·
              refine ⟨62627277761707750516065635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41751518507805167010710423 62627277761707750516065635)
              ·
                refine ⟨93940916642561625774098453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62627277761707750516065635 93940916642561625774098453)
                ·
                  refine ⟨4403480467620076208160865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 93940916642561625774098453 4403480467620076208160865)
                  ·
                    refine ⟨3302610350715057156120649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4403480467620076208160865 3302610350715057156120649)
                    ·
                      refine ⟨2476957763036292867090487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302610350715057156120649 2476957763036292867090487)
                      ·
                        rfl

theorem cell23_4823858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_4823858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823858 prefixEnd_4823858 := by exact prefixLift 4823858
  have htrace : WordTrace (prefixWord ++ tailWord_4823858) baseStart_4823858 baseEnd_4823858 := by
    simpa [prefixWord, tailWord_4823858, baseEnd_4823858] using wordTrace_append hprefix tailTrace_4823858
  have hstable : (prefixWord ++ tailWord_4823858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823858).length < 2 ^ (prefixWord ++ tailWord_4823858).sum := by decide
  have hdescent : baseEnd_4823858 < baseStart_4823858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823861 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4823861 : Nat := 118140960795 + 4823861 * 2 ^ 59
def prefixEnd_4823861 : Nat := 4983230072969 + 3 ^ 40 * 4823861 * 2
def baseEnd_4823861 : Nat := 2476959303478256355352973

theorem tailTrace_4823861 : CollatzResearch.WordTrace tailWord_4823861 prefixEnd_4823861 2476959303478256355352973 := by
  unfold tailWord_4823861
  simp only [CollatzResearch.WordTrace]
  refine ⟨175940664776982921713871437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117293776517988614475914291 175940664776982921713871437)
  ·
    refine ⟨65977749291368595642701789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175940664776982921713871437 65977749291368595642701789)
    ·
      refine ⟨24741655984263223366013171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65977749291368595642701789 24741655984263223366013171)
      ·
        refine ⟨37112483976394835049019757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24741655984263223366013171 37112483976394835049019757)
        ·
          refine ⟨13917181491148063143382409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37112483976394835049019757 13917181491148063143382409)
          ·
            refine ⟨10437886118361047357536807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13917181491148063143382409 10437886118361047357536807)
            ·
              refine ⟨15656829177541571036305211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10437886118361047357536807 15656829177541571036305211)
              ·
                refine ⟨23485243766312356554457817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15656829177541571036305211 23485243766312356554457817)
                ·
                  refine ⟨17613932824734267415843363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23485243766312356554457817 17613932824734267415843363)
                  ·
                    refine ⟨26420899237101401123765045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17613932824734267415843363 26420899237101401123765045)
                    ·
                      refine ⟨2476959303478256355352973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26420899237101401123765045 2476959303478256355352973)
                      ·
                        rfl

theorem cell23_4823861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4823861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823861 prefixEnd_4823861 := by exact prefixLift 4823861
  have htrace : WordTrace (prefixWord ++ tailWord_4823861) baseStart_4823861 baseEnd_4823861 := by
    simpa [prefixWord, tailWord_4823861, baseEnd_4823861] using wordTrace_append hprefix tailTrace_4823861
  have hstable : (prefixWord ++ tailWord_4823861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823861).length < 2 ^ (prefixWord ++ tailWord_4823861).sum := by decide
  have hdescent : baseEnd_4823861 < baseStart_4823861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823881 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 7]
def baseStart_4823881 : Nat := 118140960795 + 4823881 * 2 ^ 59
def prefixEnd_4823881 : Nat := 4983230072969 + 3 ^ 40 * 4823881 * 2
def baseEnd_4823881 : Nat := 275218841454594030789209

theorem tailTrace_4823881 : CollatzResearch.WordTrace tailWord_4823881 prefixEnd_4823881 275218841454594030789209 := by
  unfold tailWord_4823881
  simp only [CollatzResearch.WordTrace]
  refine ⟨175941394236910465129599497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117294262824606976753066331 175941394236910465129599497)
  ·
    refine ⟨131956045677682848847199623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175941394236910465129599497 131956045677682848847199623)
    ·
      refine ⟨197934068516524273270799435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131956045677682848847199623 197934068516524273270799435)
      ·
        refine ⟨296901102774786409906199153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197934068516524273270799435 296901102774786409906199153)
        ·
          refine ⟨222675827081089807429649365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296901102774786409906199153 222675827081089807429649365)
          ·
            refine ⟨5218964697213042361632407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 222675827081089807429649365 5218964697213042361632407)
            ·
              refine ⟨7828447045819563542448611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218964697213042361632407 7828447045819563542448611)
              ·
                refine ⟨11742670568729345313672917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7828447045819563542448611 11742670568729345313672917)
                ·
                  refine ⟨275218841454594030789209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11742670568729345313672917 275218841454594030789209)
                  ·
                    rfl

theorem cell23_4823881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_4823881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823881 prefixEnd_4823881 := by exact prefixLift 4823881
  have htrace : WordTrace (prefixWord ++ tailWord_4823881) baseStart_4823881 baseEnd_4823881 := by
    simpa [prefixWord, tailWord_4823881, baseEnd_4823881] using wordTrace_append hprefix tailTrace_4823881
  have hstable : (prefixWord ++ tailWord_4823881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823881).length < 2 ^ (prefixWord ++ tailWord_4823881).sum := by decide
  have hdescent : baseEnd_4823881 < baseStart_4823881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823892 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_4823892 : Nat := 118140960795 + 4823892 * 2 ^ 59
def prefixEnd_4823892 : Nat := 4983230072969 + 3 ^ 40 * 4823892 * 2
def baseEnd_4823892 : Nat := 2476975221378545734065331

theorem tailTrace_4823892 : CollatzResearch.WordTrace tailWord_4823892 prefixEnd_4823892 2476975221378545734065331 := by
  unfold tailWord_4823892
  simp only [CollatzResearch.WordTrace]
  refine ⟨87970897719935307004124965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117294530293247076005499953 87970897719935307004124965)
  ·
    refine ⟨16494543322487870063273431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87970897719935307004124965 16494543322487870063273431)
    ·
      refine ⟨24741814983731805094910147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16494543322487870063273431 24741814983731805094910147)
      ·
        refine ⟨37112722475597707642365221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24741814983731805094910147 37112722475597707642365221)
        ·
          refine ⟨6958635464174570182943479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37112722475597707642365221 6958635464174570182943479)
          ·
            refine ⟨10437953196261855274415219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6958635464174570182943479 10437953196261855274415219)
            ·
              refine ⟨15656929794392782911622829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10437953196261855274415219 15656929794392782911622829)
              ·
                refine ⟨5871348672897293591858561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15656929794392782911622829 5871348672897293591858561)
                ·
                  refine ⟨4403511504672970193893921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5871348672897293591858561 4403511504672970193893921)
                  ·
                    refine ⟨3302633628504727645420441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4403511504672970193893921 3302633628504727645420441)
                    ·
                      refine ⟨2476975221378545734065331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302633628504727645420441 2476975221378545734065331)
                      ·
                        rfl

theorem cell23_4823892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_4823892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823892 prefixEnd_4823892 := by exact prefixLift 4823892
  have htrace : WordTrace (prefixWord ++ tailWord_4823892) baseStart_4823892 baseEnd_4823892 := by
    simpa [prefixWord, tailWord_4823892, baseEnd_4823892] using wordTrace_append hprefix tailTrace_4823892
  have hstable : (prefixWord ++ tailWord_4823892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823892).length < 2 ^ (prefixWord ++ tailWord_4823892).sum := by decide
  have hdescent : baseEnd_4823892 < baseStart_4823892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823904 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_4823904 : Nat := 118140960795 + 4823904 * 2 ^ 59
def prefixEnd_4823904 : Nat := 4983230072969 + 3 ^ 40 * 4823904 * 2
def baseEnd_4823904 : Nat := 2476981383146399687115275

theorem tailTrace_4823904 : CollatzResearch.WordTrace tailWord_4823904 prefixEnd_4823904 2476981383146399687115275 := by
  unfold tailWord_4823904
  simp only [CollatzResearch.WordTrace]
  refine ⟨87971116557913570028843383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117294822077218093371791177 87971116557913570028843383)
  ·
    refine ⟨131956674836870355043265075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87971116557913570028843383 131956674836870355043265075)
    ·
      refine ⟨197935012255305532564897613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131956674836870355043265075 197935012255305532564897613)
      ·
        refine ⟨74225629595739574711836605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197935012255305532564897613 74225629595739574711836605)
        ·
          refine ⟨27834611098402340516938727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74225629595739574711836605 27834611098402340516938727)
          ·
            refine ⟨41751916647603510775408091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27834611098402340516938727 41751916647603510775408091)
            ·
              refine ⟨62627874971405266163112137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41751916647603510775408091 62627874971405266163112137)
              ·
                refine ⟨46970906228553949622334103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62627874971405266163112137 46970906228553949622334103)
                ·
                  refine ⟨70456359342830924433501155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46970906228553949622334103 70456359342830924433501155)
                  ·
                    refine ⟨105684539014246386650251733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70456359342830924433501155 105684539014246386650251733)
                    ·
                      refine ⟨2476981383146399687115275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105684539014246386650251733 2476981383146399687115275)
                      ·
                        rfl

theorem cell23_4823904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_4823904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823904 prefixEnd_4823904 := by exact prefixLift 4823904
  have htrace : WordTrace (prefixWord ++ tailWord_4823904) baseStart_4823904 baseEnd_4823904 := by
    simpa [prefixWord, tailWord_4823904, baseEnd_4823904] using wordTrace_append hprefix tailTrace_4823904
  have hstable : (prefixWord ++ tailWord_4823904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823904).length < 2 ^ (prefixWord ++ tailWord_4823904).sum := by decide
  have hdescent : baseEnd_4823904 < baseStart_4823904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823911 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 2, 5]
def baseStart_4823911 : Nat := 118140960795 + 4823911 * 2 ^ 59
def prefixEnd_4823911 : Nat := 4983230072969 + 3 ^ 40 * 4823911 * 2
def baseEnd_4823911 : Nat := 825661659170327053242581

theorem tailTrace_4823911 : CollatzResearch.WordTrace tailWord_4823911 prefixEnd_4823911 825661659170327053242581 := by
  unfold tailWord_4823911
  simp only [CollatzResearch.WordTrace]
  refine ⟨175942488426801780253191587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117294992284534520168794391 175942488426801780253191587)
  ·
    refine ⟨263913732640202670379787381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175942488426801780253191587 263913732640202670379787381)
    ·
      refine ⟨24741912435019000348105067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263913732640202670379787381 24741912435019000348105067)
      ·
        refine ⟨37112868652528500522157601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24741912435019000348105067 37112868652528500522157601)
        ·
          refine ⟨27834651489396375391618201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37112868652528500522157601 27834651489396375391618201)
          ·
            refine ⟨20875988617047281543713651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27834651489396375391618201 20875988617047281543713651)
            ·
              refine ⟨31313982925570922315570477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20875988617047281543713651 31313982925570922315570477)
              ·
                refine ⟨11742743597089095868338929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31313982925570922315570477 11742743597089095868338929)
                ·
                  refine ⟨8807057697816821901254197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11742743597089095868338929 8807057697816821901254197)
                  ·
                    refine ⟨825661659170327053242581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8807057697816821901254197 825661659170327053242581)
                    ·
                      rfl

theorem cell23_4823911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_4823911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823911 prefixEnd_4823911 := by exact prefixLift 4823911
  have htrace : WordTrace (prefixWord ++ tailWord_4823911) baseStart_4823911 baseEnd_4823911 := by
    simpa [prefixWord, tailWord_4823911, baseEnd_4823911] using wordTrace_append hprefix tailTrace_4823911
  have hstable : (prefixWord ++ tailWord_4823911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823911).length < 2 ^ (prefixWord ++ tailWord_4823911).sum := by decide
  have hdescent : baseEnd_4823911 < baseStart_4823911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823931 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 4]
def baseStart_4823931 : Nat := 118140960795 + 4823931 * 2 ^ 59
def prefixEnd_4823931 : Nat := 4983230072969 + 3 ^ 40 * 4823931 * 2
def baseEnd_4823931 : Nat := 2476995247124071081477651

theorem tailTrace_4823931 : CollatzResearch.WordTrace tailWord_4823931 prefixEnd_4823931 2476995247124071081477651 := by
  unfold tailWord_4823931
  simp only [CollatzResearch.WordTrace]
  refine ⟨175943217886729323668919647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117295478591152882445946431 175943217886729323668919647)
  ·
    refine ⟨263914826830093985503379471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175943217886729323668919647 263914826830093985503379471)
    ·
      refine ⟨395872240245140978255069207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263914826830093985503379471 395872240245140978255069207)
      ·
        refine ⟨593808360367711467382603811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395872240245140978255069207 593808360367711467382603811)
        ·
          refine ⟨890712540551567201073905717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593808360367711467382603811 890712540551567201073905717)
          ·
            refine ⟨83504300676709425100678661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 890712540551567201073905717 83504300676709425100678661)
            ·
              refine ⟨15657056376883017206377249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83504300676709425100678661 15657056376883017206377249)
              ·
                refine ⟨11742792282662262904782937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15657056376883017206377249 11742792282662262904782937)
                ·
                  refine ⟨8807094211996697178587203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11742792282662262904782937 8807094211996697178587203)
                  ·
                    refine ⟨13210641317995045767880805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8807094211996697178587203 13210641317995045767880805)
                    ·
                      refine ⟨2476995247124071081477651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13210641317995045767880805 2476995247124071081477651)
                      ·
                        rfl

theorem cell23_4823931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 4].length) (baseStart_4823931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823931 prefixEnd_4823931 := by exact prefixLift 4823931
  have htrace : WordTrace (prefixWord ++ tailWord_4823931) baseStart_4823931 baseEnd_4823931 := by
    simpa [prefixWord, tailWord_4823931, baseEnd_4823931] using wordTrace_append hprefix tailTrace_4823931
  have hstable : (prefixWord ++ tailWord_4823931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823931).length < 2 ^ (prefixWord ++ tailWord_4823931).sum := by decide
  have hdescent : baseEnd_4823931 < baseStart_4823931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4823968 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_4823968 : Nat := 118140960795 + 4823968 * 2 ^ 59
def prefixEnd_4823968 : Nat := 4983230072969 + 3 ^ 40 * 4823968 * 2
def baseEnd_4823968 : Nat := 2477014245908287436714981

theorem tailTrace_4823968 : CollatzResearch.WordTrace tailWord_4823968 prefixEnd_4823968 2477014245908287436714981 := by
  unfold tailWord_4823968
  simp only [CollatzResearch.WordTrace]
  refine ⟨87972283693797639494008279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117296378258396852658677705 87972283693797639494008279)
  ·
    refine ⟨131958425540696459241012419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87972283693797639494008279 131958425540696459241012419)
    ·
      refine ⟨197937638311044688861518629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131958425540696459241012419 197937638311044688861518629)
      ·
        refine ⟨37113307183320879161534743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197937638311044688861518629 37113307183320879161534743)
        ·
          refine ⟨55669960774981318742302115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37113307183320879161534743 55669960774981318742302115)
          ·
            refine ⟨83504941162471978113453173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55669960774981318742302115 83504941162471978113453173)
            ·
              refine ⟨7828588233981747948136235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83504941162471978113453173 7828588233981747948136235)
              ·
                refine ⟨11742882350972621922204353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7828588233981747948136235 11742882350972621922204353)
                ·
                  refine ⟨8807161763229466441653265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11742882350972621922204353 8807161763229466441653265)
                  ·
                    refine ⟨6605371322422099831239949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8807161763229466441653265 6605371322422099831239949)
                    ·
                      refine ⟨2477014245908287436714981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605371322422099831239949 2477014245908287436714981)
                      ·
                        rfl

theorem cell23_4823968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_4823968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4823968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4823968 prefixEnd_4823968 := by exact prefixLift 4823968
  have htrace : WordTrace (prefixWord ++ tailWord_4823968) baseStart_4823968 baseEnd_4823968 := by
    simpa [prefixWord, tailWord_4823968, baseEnd_4823968] using wordTrace_append hprefix tailTrace_4823968
  have hstable : (prefixWord ++ tailWord_4823968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4823968).length < 2 ^ (prefixWord ++ tailWord_4823968).sum := by decide
  have hdescent : baseEnd_4823968 < baseStart_4823968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4823968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824048 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 2, 4]
def baseStart_4824048 : Nat := 118140960795 + 4824048 * 2 ^ 59
def prefixEnd_4824048 : Nat := 4983230072969 + 3 ^ 40 * 4824048 * 2
def baseEnd_4824048 : Nat := 825685108120215707904871

theorem tailTrace_4824048 : CollatzResearch.WordTrace tailWord_4824048 prefixEnd_4824048 825685108120215707904871 := by
  unfold tailWord_4824048
  simp only [CollatzResearch.WordTrace]
  refine ⟨87973742613652726325464399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117298323484870301767285865 87973742613652726325464399)
  ·
    refine ⟨131960613920479089488196599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87973742613652726325464399 131960613920479089488196599)
    ·
      refine ⟨197940920880718634232294899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131960613920479089488196599 197940920880718634232294899)
      ·
        refine ⟨296911381321077951348442349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197940920880718634232294899 296911381321077951348442349)
        ·
          refine ⟨111341767995404231755665881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296911381321077951348442349 111341767995404231755665881)
          ·
            refine ⟨83506325996553173816749411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111341767995404231755665881 83506325996553173816749411)
            ·
              refine ⟨125259488994829760725124117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83506325996553173816749411 125259488994829760725124117)
              ·
                refine ⟨5871538546632645033990193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125259488994829760725124117 5871538546632645033990193)
                ·
                  refine ⟨4403653909974483775492645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5871538546632645033990193 4403653909974483775492645)
                  ·
                    refine ⟨825685108120215707904871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4403653909974483775492645 825685108120215707904871)
                    ·
                      rfl

theorem cell23_4824048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 4].length) (baseStart_4824048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824048 prefixEnd_4824048 := by exact prefixLift 4824048
  have htrace : WordTrace (prefixWord ++ tailWord_4824048) baseStart_4824048 baseEnd_4824048 := by
    simpa [prefixWord, tailWord_4824048, baseEnd_4824048] using wordTrace_append hprefix tailTrace_4824048
  have hstable : (prefixWord ++ tailWord_4824048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824048).length < 2 ^ (prefixWord ++ tailWord_4824048).sum := by decide
  have hdescent : baseEnd_4824048 < baseStart_4824048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824049 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 1, 1, 3]
def baseStart_4824049 : Nat := 118140960795 + 4824049 * 2 ^ 59
def prefixEnd_4824049 : Nat := 4983230072969 + 3 ^ 40 * 4824049 * 2
def baseEnd_4824049 : Nat := 2477055837841301619802109

theorem tailTrace_4824049 : CollatzResearch.WordTrace tailWord_4824049 prefixEnd_4824049 2477055837841301619802109 := by
  unfold tailWord_4824049
  simp only [CollatzResearch.WordTrace]
  refine ⟨175947521700301829821715201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117298347800201219881143467 175947521700301829821715201)
  ·
    refine ⟨131960641275226372366286401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175947521700301829821715201 131960641275226372366286401)
    ·
      refine ⟨98970480956419779274714801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131960641275226372366286401 98970480956419779274714801)
      ·
        refine ⟨74227860717314834456036101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98970480956419779274714801 74227860717314834456036101)
        ·
          refine ⟨13917723884496531460506769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74227860717314834456036101 13917723884496531460506769)
          ·
            refine ⟨10438292913372398595380077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13917723884496531460506769 10438292913372398595380077)
            ·
              refine ⟨3914359842514649473267529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10438292913372398595380077 3914359842514649473267529)
              ·
                refine ⟨2935769881885987104950647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3914359842514649473267529 2935769881885987104950647)
                ·
                  refine ⟨4403654822828980657425971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935769881885987104950647 4403654822828980657425971)
                  ·
                    refine ⟨6605482234243470986138957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4403654822828980657425971 6605482234243470986138957)
                    ·
                      refine ⟨2477055837841301619802109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605482234243470986138957 2477055837841301619802109)
                      ·
                        rfl

theorem cell23_4824049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_4824049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824049 prefixEnd_4824049 := by exact prefixLift 4824049
  have htrace : WordTrace (prefixWord ++ tailWord_4824049) baseStart_4824049 baseEnd_4824049 := by
    simpa [prefixWord, tailWord_4824049, baseEnd_4824049] using wordTrace_append hprefix tailTrace_4824049
  have hstable : (prefixWord ++ tailWord_4824049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824049).length < 2 ^ (prefixWord ++ tailWord_4824049).sum := by decide
  have hdescent : baseEnd_4824049 < baseStart_4824049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824065 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4824065 : Nat := 118140960795 + 4824065 * 2 ^ 59
def prefixEnd_4824065 : Nat := 4983230072969 + 3 ^ 40 * 4824065 * 2
def baseEnd_4824065 : Nat := 825688017843924519067345

theorem tailTrace_4824065 : CollatzResearch.WordTrace tailWord_4824065 prefixEnd_4824065 825688017843924519067345 := by
  unfold tailWord_4824065
  simp only [CollatzResearch.WordTrace]
  refine ⟨175948105268243864554297649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117298736845495909702865099 175948105268243864554297649)
  ·
    refine ⟨131961078951182898415723237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175948105268243864554297649 131961078951182898415723237)
    ·
      refine ⟨24742702303346793452948107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131961078951182898415723237 24742702303346793452948107)
      ·
        refine ⟨37114053455020190179422161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24742702303346793452948107 37114053455020190179422161)
        ·
          refine ⟨27835540091265142634566621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37114053455020190179422161 27835540091265142634566621)
          ·
            refine ⟨10438327534224428487962483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27835540091265142634566621 10438327534224428487962483)
            ·
              refine ⟨15657491301336642731943725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10438327534224428487962483 15657491301336642731943725)
              ·
                refine ⟨5871559238001241024478897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15657491301336642731943725 5871559238001241024478897)
                ·
                  refine ⟨4403669428500930768359173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5871559238001241024478897 4403669428500930768359173)
                  ·
                    refine ⟨825688017843924519067345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4403669428500930768359173 825688017843924519067345)
                    ·
                      rfl

theorem cell23_4824065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4824065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824065 prefixEnd_4824065 := by exact prefixLift 4824065
  have htrace : WordTrace (prefixWord ++ tailWord_4824065) baseStart_4824065 baseEnd_4824065 := by
    simpa [prefixWord, tailWord_4824065, baseEnd_4824065] using wordTrace_append hprefix tailTrace_4824065
  have hstable : (prefixWord ++ tailWord_4824065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824065).length < 2 ^ (prefixWord ++ tailWord_4824065).sum := by decide
  have hdescent : baseEnd_4824065 < baseStart_4824065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824075 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 3]
def baseStart_4824075 : Nat := 118140960795 + 4824075 * 2 ^ 59
def prefixEnd_4824075 : Nat := 4983230072969 + 3 ^ 40 * 4824075 * 2
def baseEnd_4824075 : Nat := 2477069188338318518076989

theorem tailTrace_4824075 : CollatzResearch.WordTrace tailWord_4824075 prefixEnd_4824075 2477069188338318518076989 := by
  unfold tailWord_4824075
  simp only [CollatzResearch.WordTrace]
  refine ⟨175948469998207636262161679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117298979998805090841441119 175948469998207636262161679)
  ·
    refine ⟨263922704997311454393242519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175948469998207636262161679 263922704997311454393242519)
    ·
      refine ⟨395884057495967181589863779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263922704997311454393242519 395884057495967181589863779)
      ·
        refine ⟨593826086243950772384795669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395884057495967181589863779 593826086243950772384795669)
        ·
          refine ⟨27835597792685192455537297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 593826086243950772384795669 27835597792685192455537297)
          ·
            refine ⟨20876698344513894341652973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27835597792685192455537297 20876698344513894341652973)
            ·
              refine ⟨7828761879192710378119865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20876698344513894341652973 7828761879192710378119865)
              ·
                refine ⟨5871571409394532783589899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7828761879192710378119865 5871571409394532783589899)
                ·
                  refine ⟨8807357114091799175384849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871571409394532783589899 8807357114091799175384849)
                  ·
                    refine ⟨6605517835568849381538637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8807357114091799175384849 6605517835568849381538637)
                    ·
                      refine ⟨2477069188338318518076989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605517835568849381538637 2477069188338318518076989)
                      ·
                        rfl

theorem cell23_4824075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 3].length) (baseStart_4824075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824075 prefixEnd_4824075 := by exact prefixLift 4824075
  have htrace : WordTrace (prefixWord ++ tailWord_4824075) baseStart_4824075 baseEnd_4824075 := by
    simpa [prefixWord, tailWord_4824075, baseEnd_4824075] using wordTrace_append hprefix tailTrace_4824075
  have hstable : (prefixWord ++ tailWord_4824075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824075).length < 2 ^ (prefixWord ++ tailWord_4824075).sum := by decide
  have hdescent : baseEnd_4824075 < baseStart_4824075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824088 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_4824088 : Nat := 118140960795 + 4824088 * 2 ^ 59
def prefixEnd_4824088 : Nat := 4983230072969 + 3 ^ 40 * 4824088 * 2
def baseEnd_4824088 : Nat := 2477075863586826967214429

theorem tailTrace_4824088 : CollatzResearch.WordTrace tailWord_4824088 prefixEnd_4824088 2477075863586826967214429 := by
  unfold tailWord_4824088
  simp only [CollatzResearch.WordTrace]
  refine ⟨87974472073580269741192459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117299296098107026321589945 87974472073580269741192459)
  ·
    refine ⟨131961708110370404611788689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87974472073580269741192459 131961708110370404611788689)
    ·
      refine ⟨98971281082777803458841517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131961708110370404611788689 98971281082777803458841517)
      ·
        refine ⟨37114230406041676297065569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98971281082777803458841517 37114230406041676297065569)
        ·
          refine ⟨27835672804531257222799177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37114230406041676297065569 27835672804531257222799177)
          ·
            refine ⟨20876754603398442917099383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27835672804531257222799177 20876754603398442917099383)
            ·
              refine ⟨31315131905097664375649075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20876754603398442917099383 31315131905097664375649075)
              ·
                refine ⟨46972697857646496563473613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31315131905097664375649075 46972697857646496563473613)
                ·
                  refine ⟨17614761696617436211302605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46972697857646496563473613 17614761696617436211302605)
                  ·
                    refine ⟨6605535636231538579238477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17614761696617436211302605 6605535636231538579238477)
                    ·
                      refine ⟨2477075863586826967214429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605535636231538579238477 2477075863586826967214429)
                      ·
                        rfl

theorem cell23_4824088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_4824088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824088 prefixEnd_4824088 := by exact prefixLift 4824088
  have htrace : WordTrace (prefixWord ++ tailWord_4824088) baseStart_4824088 baseEnd_4824088 := by
    simpa [prefixWord, tailWord_4824088, baseEnd_4824088] using wordTrace_append hprefix tailTrace_4824088
  have hstable : (prefixWord ++ tailWord_4824088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824088).length < 2 ^ (prefixWord ++ tailWord_4824088).sum := by decide
  have hdescent : baseEnd_4824088 < baseStart_4824088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824092 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_4824092 : Nat := 118140960795 + 4824092 * 2 ^ 59
def prefixEnd_4824092 : Nat := 4983230072969 + 3 ^ 40 * 4824092 * 2
def baseEnd_4824092 : Nat := 2477077917509444951564411

theorem tailTrace_4824092 : CollatzResearch.WordTrace tailWord_4824092 prefixEnd_4824092 2477077917509444951564411 := by
  unfold tailWord_4824092
  simp only [CollatzResearch.WordTrace]
  refine ⟨87974545019573024082765265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117299393359430698777020353 87974545019573024082765265)
  ·
    refine ⟨65980908764679768062073949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87974545019573024082765265 65980908764679768062073949)
    ·
      refine ⟨24742840786754913023277731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65980908764679768062073949 24742840786754913023277731)
      ·
        refine ⟨37114261180132369534916597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24742840786754913023277731 37114261180132369534916597)
        ·
          refine ⟨3479461985637409643898431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37114261180132369534916597 3479461985637409643898431)
          ·
            refine ⟨5219192978456114465847647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479461985637409643898431 5219192978456114465847647)
            ·
              refine ⟨7828789467684171698771471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219192978456114465847647 7828789467684171698771471)
              ·
                refine ⟨11743184201526257548157207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7828789467684171698771471 11743184201526257548157207)
                ·
                  refine ⟨17614776302289386322235811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11743184201526257548157207 17614776302289386322235811)
                  ·
                    refine ⟨26422164453434079483353717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17614776302289386322235811 26422164453434079483353717)
                    ·
                      refine ⟨2477077917509444951564411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26422164453434079483353717 2477077917509444951564411)
                      ·
                        rfl

theorem cell23_4824092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_4824092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824092 prefixEnd_4824092 := by exact prefixLift 4824092
  have htrace : WordTrace (prefixWord ++ tailWord_4824092) baseStart_4824092 baseEnd_4824092 := by
    simpa [prefixWord, tailWord_4824092, baseEnd_4824092] using wordTrace_append hprefix tailTrace_4824092
  have hstable : (prefixWord ++ tailWord_4824092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824092).length < 2 ^ (prefixWord ++ tailWord_4824092).sum := by decide
  have hdescent : baseEnd_4824092 < baseStart_4824092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824106 : List Nat := [3, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4824106 : Nat := 118140960795 + 4824106 * 2 ^ 59
def prefixEnd_4824106 : Nat := 4983230072969 + 3 ^ 40 * 4824106 * 2
def baseEnd_4824106 : Nat := 2477085106238607896789347

theorem tailTrace_4824106 : CollatzResearch.WordTrace tailWord_4824106 prefixEnd_4824106 2477085106238607896789347 := by
  unfold tailWord_4824106
  simp only [CollatzResearch.WordTrace]
  refine ⟨43987400165273832139135043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117299733774063552371026781 43987400165273832139135043)
  ·
    refine ⟨65981100247910748208702565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43987400165273832139135043 65981100247910748208702565)
    ·
      refine ⟨12371456296483265289131731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65981100247910748208702565 12371456296483265289131731)
      ·
        refine ⟨18557184444724897933697597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12371456296483265289131731 18557184444724897933697597)
        ·
          refine ⟨6958944166771836725136599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18557184444724897933697597 6958944166771836725136599)
          ·
            refine ⟨10438416250157755087704899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6958944166771836725136599 10438416250157755087704899)
            ·
              refine ⟨15657624375236632631557349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10438416250157755087704899 15657624375236632631557349)
              ·
                refine ⟨2935804570356868618417003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15657624375236632631557349 2935804570356868618417003)
                ·
                  refine ⟨4403706855535302927625505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935804570356868618417003 4403706855535302927625505)
                  ·
                    refine ⟨3302780141651477195719129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4403706855535302927625505 3302780141651477195719129)
                    ·
                      refine ⟨2477085106238607896789347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302780141651477195719129 2477085106238607896789347)
                      ·
                        rfl

theorem cell23_4824106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4824106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824106 prefixEnd_4824106 := by exact prefixLift 4824106
  have htrace : WordTrace (prefixWord ++ tailWord_4824106) baseStart_4824106 baseEnd_4824106 := by
    simpa [prefixWord, tailWord_4824106, baseEnd_4824106] using wordTrace_append hprefix tailTrace_4824106
  have hstable : (prefixWord ++ tailWord_4824106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824106).length < 2 ^ (prefixWord ++ tailWord_4824106).sum := by decide
  have hdescent : baseEnd_4824106 < baseStart_4824106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824145 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 1, 4, 2]
def baseStart_4824145 : Nat := 118140960795 + 4824145 * 2 ^ 59
def prefixEnd_4824145 : Nat := 4983230072969 + 3 ^ 40 * 4824145 * 2
def baseEnd_4824145 : Nat := 2477105131984133244201667

theorem tailTrace_4824145 : CollatzResearch.WordTrace tailWord_4824145 prefixEnd_4824145 2477105131984133244201667 := by
  unfold tailWord_4824145
  simp only [CollatzResearch.WordTrace]
  refine ⟨175951023107954038217209889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117300682071969358811473259 175951023107954038217209889)
  ·
    refine ⟨131963267330965528662907417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175951023107954038217209889 131963267330965528662907417)
    ·
      refine ⟨98972450498224146497180563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131963267330965528662907417 98972450498224146497180563)
      ·
        refine ⟨148458675747336219745770845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98972450498224146497180563 148458675747336219745770845)
        ·
          refine ⟨55672003405251082404664067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148458675747336219745770845 55672003405251082404664067)
          ·
            refine ⟨83508005107876623606996101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55672003405251082404664067 83508005107876623606996101)
            ·
              refine ⟨15657750957726866926311769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83508005107876623606996101 15657750957726866926311769)
              ·
                refine ⟨11743313218295150194733827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15657750957726866926311769 11743313218295150194733827)
                ·
                  refine ⟨17614969827442725292100741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11743313218295150194733827 17614969827442725292100741)
                  ·
                    refine ⟨3302806842645510992268889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17614969827442725292100741 3302806842645510992268889)
                    ·
                      refine ⟨2477105131984133244201667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302806842645510992268889 2477105131984133244201667)
                      ·
                        rfl

theorem cell23_4824145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_4824145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824145 prefixEnd_4824145 := by exact prefixLift 4824145
  have htrace : WordTrace (prefixWord ++ tailWord_4824145) baseStart_4824145 baseEnd_4824145 := by
    simpa [prefixWord, tailWord_4824145, baseEnd_4824145] using wordTrace_append hprefix tailTrace_4824145
  have hstable : (prefixWord ++ tailWord_4824145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824145).length < 2 ^ (prefixWord ++ tailWord_4824145).sum := by decide
  have hdescent : baseEnd_4824145 < baseStart_4824145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824148 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4824148 : Nat := 118140960795 + 4824148 * 2 ^ 59
def prefixEnd_4824148 : Nat := 4983230072969 + 3 ^ 40 * 4824148 * 2
def baseEnd_4824148 : Nat := 2477106672426096732464153

theorem tailTrace_4824148 : CollatzResearch.WordTrace tailWord_4824148 prefixEnd_4824148 2477106672426096732464153 := by
  unfold tailWord_4824148
  simp only [CollatzResearch.WordTrace]
  refine ⟨87975566263471584864784549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117300755017962113153046065 87975566263471584864784549)
  ·
    refine ⟨16495418674400922162147103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87975566263471584864784549 16495418674400922162147103)
    ·
      refine ⟨24743128011601383243220655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16495418674400922162147103 24743128011601383243220655)
      ·
        refine ⟨37114692017402074864830983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24743128011601383243220655 37114692017402074864830983)
        ·
          refine ⟨55672038026103112297246475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37114692017402074864830983 55672038026103112297246475)
          ·
            refine ⟨83508057039154668445869713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55672038026103112297246475 83508057039154668445869713)
            ·
              refine ⟨62631042779366001334402285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83508057039154668445869713 62631042779366001334402285)
              ·
                refine ⟨23486641042262250500400857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62631042779366001334402285 23486641042262250500400857)
                ·
                  refine ⟨17614980781696687875300643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23486641042262250500400857 17614980781696687875300643)
                  ·
                    refine ⟨26422471172545031812950965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17614980781696687875300643 26422471172545031812950965)
                    ·
                      refine ⟨2477106672426096732464153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26422471172545031812950965 2477106672426096732464153)
                      ·
                        rfl

theorem cell23_4824148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4824148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824148 prefixEnd_4824148 := by exact prefixLift 4824148
  have htrace : WordTrace (prefixWord ++ tailWord_4824148) baseStart_4824148 baseEnd_4824148 := by
    simpa [prefixWord, tailWord_4824148, baseEnd_4824148] using wordTrace_append hprefix tailTrace_4824148
  have hstable : (prefixWord ++ tailWord_4824148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824148).length < 2 ^ (prefixWord ++ tailWord_4824148).sum := by decide
  have hdescent : baseEnd_4824148 < baseStart_4824148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824151 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 11]
def baseStart_4824151 : Nat := 118140960795 + 4824151 * 2 ^ 59
def prefixEnd_4824151 : Nat := 4983230072969 + 3 ^ 40 * 4824151 * 2
def baseEnd_4824151 : Nat := 275234245874228913414071

theorem tailTrace_4824151 : CollatzResearch.WordTrace tailWord_4824151 prefixEnd_4824151 275234245874228913414071 := by
  unfold tailWord_4824151
  simp only [CollatzResearch.WordTrace]
  refine ⟨175951241945932301241928307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117300827963954867494618871 175951241945932301241928307)
  ·
    refine ⟨263926862918898451862892461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175951241945932301241928307 263926862918898451862892461)
    ·
      refine ⟨98972573594586919448584673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263926862918898451862892461 98972573594586919448584673)
      ·
        refine ⟨74229430195940189586438505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98972573594586919448584673 74229430195940189586438505)
        ·
          refine ⟨55672072646955142189828879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74229430195940189586438505 55672072646955142189828879)
          ·
            refine ⟨83508108970432713284743319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55672072646955142189828879 83508108970432713284743319)
            ·
              refine ⟨125262163455649069927114979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83508108970432713284743319 125262163455649069927114979)
              ·
                refine ⟨187893245183473604890672469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125262163455649069927114979 187893245183473604890672469)
                ·
                  refine ⟨275234245874228913414071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 187893245183473604890672469 275234245874228913414071)
                  ·
                    rfl

theorem cell23_4824151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 11].length) (baseStart_4824151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824151 prefixEnd_4824151 := by exact prefixLift 4824151
  have htrace : WordTrace (prefixWord ++ tailWord_4824151) baseStart_4824151 baseEnd_4824151 := by
    simpa [prefixWord, tailWord_4824151, baseEnd_4824151] using wordTrace_append hprefix tailTrace_4824151
  have hstable : (prefixWord ++ tailWord_4824151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824151).length < 2 ^ (prefixWord ++ tailWord_4824151).sum := by decide
  have hdescent : baseEnd_4824151 < baseStart_4824151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824215 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 2, 5]
def baseStart_4824215 : Nat := 118140960795 + 4824215 * 2 ^ 59
def prefixEnd_4824215 : Nat := 4983230072969 + 3 ^ 40 * 4824215 * 2
def baseEnd_4824215 : Nat := 825713691876649323442115

theorem tailTrace_4824215 : CollatzResearch.WordTrace tailWord_4824215 prefixEnd_4824215 825713691876649323442115 := by
  unfold tailWord_4824215
  simp only [CollatzResearch.WordTrace]
  refine ⟨175953576217700440172258099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117302384145133626781505399 175953576217700440172258099)
  ·
    refine ⟨263930364326550660258387149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175953576217700440172258099 263930364326550660258387149)
    ·
      refine ⟨98973886622456497596895181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263930364326550660258387149 98973886622456497596895181)
      ·
        refine ⟨37115207483421186598835693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98973886622456497596895181 37115207483421186598835693)
        ·
          refine ⟨13918202806282944974563385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37115207483421186598835693 13918202806282944974563385)
          ·
            refine ⟨10438652104712208730922539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13918202806282944974563385 10438652104712208730922539)
            ·
              refine ⟨15657978157068313096383809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10438652104712208730922539 15657978157068313096383809)
              ·
                refine ⟨11743483617801234822287857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15657978157068313096383809 11743483617801234822287857)
                ·
                  refine ⟨8807612713350926116715893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11743483617801234822287857 8807612713350926116715893)
                  ·
                    refine ⟨825713691876649323442115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8807612713350926116715893 825713691876649323442115)
                    ·
                      rfl

theorem cell23_4824215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_4824215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824215 prefixEnd_4824215 := by exact prefixLift 4824215
  have htrace : WordTrace (prefixWord ++ tailWord_4824215) baseStart_4824215 baseEnd_4824215 := by
    simpa [prefixWord, tailWord_4824215, baseEnd_4824215] using wordTrace_append hprefix tailTrace_4824215
  have hstable : (prefixWord ++ tailWord_4824215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824215).length < 2 ^ (prefixWord ++ tailWord_4824215).sum := by decide
  have hdescent : baseEnd_4824215 < baseStart_4824215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824252 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4824252 : Nat := 118140960795 + 4824252 * 2 ^ 59
def prefixEnd_4824252 : Nat := 4983230072969 + 3 ^ 40 * 4824252 * 2
def baseEnd_4824252 : Nat := 2477160074414164325563675

theorem tailTrace_4824252 : CollatzResearch.WordTrace tailWord_4824252 prefixEnd_4824252 2477160074414164325563675 := by
  unfold tailWord_4824252
  simp only [CollatzResearch.WordTrace]
  refine ⟨87977462859283197745677505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117303283812377596994236673 87977462859283197745677505)
  ·
    refine ⟨65983097144462398309258129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87977462859283197745677505 65983097144462398309258129)
    ·
      refine ⟨49487322858346798731943597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65983097144462398309258129 49487322858346798731943597)
      ·
        refine ⟨18557746071880049524478849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49487322858346798731943597 18557746071880049524478849)
        ·
          refine ⟨13918309553910037143359137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18557746071880049524478849 13918309553910037143359137)
          ·
            refine ⟨10438732165432527857519353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13918309553910037143359137 10438732165432527857519353)
            ·
              refine ⟨7829049124074395893139515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10438732165432527857519353 7829049124074395893139515)
              ·
                refine ⟨11743573686111593839709273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829049124074395893139515 11743573686111593839709273)
                ·
                  refine ⟨8807680264583695379781955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11743573686111593839709273 8807680264583695379781955)
                  ·
                    refine ⟨13211520396875543069672933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8807680264583695379781955 13211520396875543069672933)
                    ·
                      refine ⟨2477160074414164325563675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13211520396875543069672933 2477160074414164325563675)
                      ·
                        rfl

theorem cell23_4824252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4824252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824252 prefixEnd_4824252 := by exact prefixLift 4824252
  have htrace : WordTrace (prefixWord ++ tailWord_4824252) baseStart_4824252 baseEnd_4824252 := by
    simpa [prefixWord, tailWord_4824252, baseEnd_4824252] using wordTrace_append hprefix tailTrace_4824252
  have hstable : (prefixWord ++ tailWord_4824252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824252).length < 2 ^ (prefixWord ++ tailWord_4824252).sum := by decide
  have hdescent : baseEnd_4824252 < baseStart_4824252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824255 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_4824255 : Nat := 118140960795 + 4824255 * 2 ^ 59
def prefixEnd_4824255 : Nat := 4983230072969 + 3 ^ 40 * 4824255 * 2
def baseEnd_4824255 : Nat := 2477161614856127813826161

theorem tailTrace_4824255 : CollatzResearch.WordTrace tailWord_4824255 prefixEnd_4824255 2477161614856127813826161 := by
  unfold tailWord_4824255
  simp only [CollatzResearch.WordTrace]
  refine ⟨175955035137555527003714219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117303356758370351335809479 175955035137555527003714219)
  ·
    refine ⟨263932552706333290505571329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175955035137555527003714219 263932552706333290505571329)
    ·
      refine ⟨197949414529749967879178497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263932552706333290505571329 197949414529749967879178497)
      ·
        refine ⟨148462060897312475909383873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197949414529749967879178497 148462060897312475909383873)
        ·
          refine ⟨111346545672984356932037905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148462060897312475909383873 111346545672984356932037905)
          ·
            refine ⟨83509909254738267699028429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111346545672984356932037905 83509909254738267699028429)
            ·
              refine ⟨31316215970526850387135661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83509909254738267699028429 31316215970526850387135661)
              ·
                refine ⟨11743580988947568895175873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31316215970526850387135661 11743580988947568895175873)
                ·
                  refine ⟨8807685741710676671381905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11743580988947568895175873 8807685741710676671381905)
                  ·
                    refine ⟨6605764306283007503536429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8807685741710676671381905 6605764306283007503536429)
                    ·
                      refine ⟨2477161614856127813826161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605764306283007503536429 2477161614856127813826161)
                      ·
                        rfl

theorem cell23_4824255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_4824255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824255 prefixEnd_4824255 := by exact prefixLift 4824255
  have htrace : WordTrace (prefixWord ++ tailWord_4824255) baseStart_4824255 baseEnd_4824255 := by
    simpa [prefixWord, tailWord_4824255, baseEnd_4824255] using wordTrace_append hprefix tailTrace_4824255
  have hstable : (prefixWord ++ tailWord_4824255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824255).length < 2 ^ (prefixWord ++ tailWord_4824255).sum := by decide
  have hdescent : baseEnd_4824255 < baseStart_4824255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824279 : List Nat := [1, 1, 3, 2, 1, 2, 6, 2, 1, 4]
def baseStart_4824279 : Nat := 118140960795 + 4824279 * 2 ^ 59
def prefixEnd_4824279 : Nat := 4983230072969 + 3 ^ 40 * 4824279 * 2
def baseEnd_4824279 : Nat := 825724646130611906642017

theorem tailTrace_4824279 : CollatzResearch.WordTrace tailWord_4824279 prefixEnd_4824279 825724646130611906642017 := by
  unfold tailWord_4824279
  simp only [CollatzResearch.WordTrace]
  refine ⟨175955910489468579102587891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117303940326312386068391927 175955910489468579102587891)
  ·
    refine ⟨263933865734202868653881837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175955910489468579102587891 263933865734202868653881837)
    ·
      refine ⟨98975199650326075745205689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263933865734202868653881837 98975199650326075745205689)
      ·
        refine ⟨74231399737744556808904267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98975199650326075745205689 74231399737744556808904267)
        ·
          refine ⟨111347099606616835213356401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74231399737744556808904267 111347099606616835213356401)
          ·
            refine ⟨83510324704962626410017301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111347099606616835213356401 83510324704962626410017301)
            ·
              refine ⟨3914546470545123112969561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83510324704962626410017301 3914546470545123112969561)
              ·
                refine ⟨2935909852908842334727171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3914546470545123112969561 2935909852908842334727171)
                ·
                  refine ⟨4403864779363263502090757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935909852908842334727171 4403864779363263502090757)
                  ·
                    refine ⟨825724646130611906642017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4403864779363263502090757 825724646130611906642017)
                    ·
                      rfl

theorem cell23_4824279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_4824279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824279 prefixEnd_4824279 := by exact prefixLift 4824279
  have htrace : WordTrace (prefixWord ++ tailWord_4824279) baseStart_4824279 baseEnd_4824279 := by
    simpa [prefixWord, tailWord_4824279, baseEnd_4824279] using wordTrace_append hprefix tailTrace_4824279
  have hstable : (prefixWord ++ tailWord_4824279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824279).length < 2 ^ (prefixWord ++ tailWord_4824279).sum := by decide
  have hdescent : baseEnd_4824279 < baseStart_4824279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824302 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_4824302 : Nat := 118140960795 + 4824302 * 2 ^ 59
def prefixEnd_4824302 : Nat := 4983230072969 + 3 ^ 40 * 4824302 * 2
def baseEnd_4824302 : Nat := 2477185748446889129938445

theorem tailTrace_4824302 : CollatzResearch.WordTrace tailWord_4824302 prefixEnd_4824302 2477185748446889129938445 := by
  unfold tailWord_4824302
  simp only [CollatzResearch.WordTrace]
  refine ⟨21994593671048156753834395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117304499578923502687116773 21994593671048156753834395)
  ·
    refine ⟨32991890506572235130751593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21994593671048156753834395 32991890506572235130751593)
    ·
      refine ⟨24743917879929176348063695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32991890506572235130751593 24743917879929176348063695)
      ·
        refine ⟨37115876819893764522095543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24743917879929176348063695 37115876819893764522095543)
        ·
          refine ⟨55673815229840646783143315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37115876819893764522095543 55673815229840646783143315)
          ·
            refine ⟨83510722844760970174714973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55673815229840646783143315 83510722844760970174714973)
            ·
              refine ⟨31316521066785363815518115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83510722844760970174714973 31316521066785363815518115)
              ·
                refine ⟨46974781600178045723277173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31316521066785363815518115 46974781600178045723277173)
                ·
                  refine ⟨4403885775016691786557235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46974781600178045723277173 4403885775016691786557235)
                  ·
                    refine ⟨6605828662525037679835853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4403885775016691786557235 6605828662525037679835853)
                    ·
                      refine ⟨2477185748446889129938445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605828662525037679835853 2477185748446889129938445)
                      ·
                        rfl

theorem cell23_4824302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_4824302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824302 prefixEnd_4824302 := by exact prefixLift 4824302
  have htrace : WordTrace (prefixWord ++ tailWord_4824302) baseStart_4824302 baseEnd_4824302 := by
    simpa [prefixWord, tailWord_4824302, baseEnd_4824302] using wordTrace_append hprefix tailTrace_4824302
  have hstable : (prefixWord ++ tailWord_4824302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824302).length < 2 ^ (prefixWord ++ tailWord_4824302).sum := by decide
  have hdescent : baseEnd_4824302 < baseStart_4824302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824305 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 1, 5]
def baseStart_4824305 : Nat := 118140960795 + 4824305 * 2 ^ 59
def prefixEnd_4824305 : Nat := 4983230072969 + 3 ^ 40 * 4824305 * 2
def baseEnd_4824305 : Nat := 825729096296284206066977

theorem tailTrace_4824305 : CollatzResearch.WordTrace tailWord_4824305 prefixEnd_4824305 825729096296284206066977 := by
  unfold tailWord_4824305
  simp only [CollatzResearch.WordTrace]
  refine ⟨175956858787374385543034369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117304572524916257028689579 175956858787374385543034369)
  ·
    refine ⟨131967644090530789157275777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175956858787374385543034369 131967644090530789157275777)
    ·
      refine ⟨98975733067898091867956833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131967644090530789157275777 98975733067898091867956833)
      ·
        refine ⟨74231799800923568900967625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98975733067898091867956833 74231799800923568900967625)
        ·
          refine ⟨55673849850692676675725719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74231799800923568900967625 55673849850692676675725719)
          ·
            refine ⟨83510774776039015013588579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55673849850692676675725719 83510774776039015013588579)
            ·
              refine ⟨125266162164058522520382869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83510774776039015013588579 125266162164058522520382869)
              ·
                refine ⟨5871851351440243243142947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125266162164058522520382869 5871851351440243243142947)
                ·
                  refine ⟨8807777027160364864714421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871851351440243243142947 8807777027160364864714421)
                  ·
                    refine ⟨825729096296284206066977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8807777027160364864714421 825729096296284206066977)
                    ·
                      rfl

theorem cell23_4824305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_4824305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824305 prefixEnd_4824305 := by exact prefixLift 4824305
  have htrace : WordTrace (prefixWord ++ tailWord_4824305) baseStart_4824305 baseEnd_4824305 := by
    simpa [prefixWord, tailWord_4824305, baseEnd_4824305] using wordTrace_append hprefix tailTrace_4824305
  have hstable : (prefixWord ++ tailWord_4824305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824305).length < 2 ^ (prefixWord ++ tailWord_4824305).sum := by decide
  have hdescent : baseEnd_4824305 < baseStart_4824305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824306 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_4824306 : Nat := 118140960795 + 4824306 * 2 ^ 59
def prefixEnd_4824306 : Nat := 4983230072969 + 3 ^ 40 * 4824306 * 2
def baseEnd_4824306 : Nat := 2477187802369507114288427

theorem tailTrace_4824306 : CollatzResearch.WordTrace tailWord_4824306 prefixEnd_4824306 2477187802369507114288427 := by
  unfold tailWord_4824306
  simp only [CollatzResearch.WordTrace]
  refine ⟨43989223815092690678455193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117304596840247175142547181 43989223815092690678455193)
  ·
    refine ⟨32991917861319518008841395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43989223815092690678455193 32991917861319518008841395)
    ·
      refine ⟨49487876791979277013262093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32991917861319518008841395 49487876791979277013262093)
      ·
        refine ⟨18557953796992228879973285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49487876791979277013262093 18557953796992228879973285)
        ·
          refine ⟨3479616336936042914994991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18557953796992228879973285 3479616336936042914994991)
          ·
            refine ⟨5219424505404064372492487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479616336936042914994991 5219424505404064372492487)
            ·
              refine ⟨7829136758106096558738731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219424505404064372492487 7829136758106096558738731)
              ·
                refine ⟨11743705137159144838108097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829136758106096558738731 11743705137159144838108097)
                ·
                  refine ⟨8807778852869358628581073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11743705137159144838108097 8807778852869358628581073)
                  ·
                    refine ⟨6605834139652018971435805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8807778852869358628581073 6605834139652018971435805)
                    ·
                      refine ⟨2477187802369507114288427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605834139652018971435805 2477187802369507114288427)
                      ·
                        rfl

theorem cell23_4824306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_4824306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824306 prefixEnd_4824306 := by exact prefixLift 4824306
  have htrace : WordTrace (prefixWord ++ tailWord_4824306) baseStart_4824306 baseEnd_4824306 := by
    simpa [prefixWord, tailWord_4824306, baseEnd_4824306] using wordTrace_append hprefix tailTrace_4824306
  have hstable : (prefixWord ++ tailWord_4824306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824306).length < 2 ^ (prefixWord ++ tailWord_4824306).sum := by decide
  have hdescent : baseEnd_4824306 < baseStart_4824306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824319 : List Nat := [1, 1, 2, 2, 1, 5, 1, 5, 1, 1, 3]
def baseStart_4824319 : Nat := 118140960795 + 4824319 * 2 ^ 59
def prefixEnd_4824319 : Nat := 4983230072969 + 3 ^ 40 * 4824319 * 2
def baseEnd_4824319 : Nat := 2477194477618015563425867

theorem tailTrace_4824319 : CollatzResearch.WordTrace tailWord_4824319 prefixEnd_4824319 2477194477618015563425867 := by
  unfold tailWord_4824319
  simp only [CollatzResearch.WordTrace]
  refine ⟨175957369409323665934044011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117304912939549110622696007 175957369409323665934044011)
  ·
    refine ⟨263936054113985498901066017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175957369409323665934044011 263936054113985498901066017)
    ·
      refine ⟨197952040585489124175799513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263936054113985498901066017 197952040585489124175799513)
      ·
        refine ⟨148464030439116843131849635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197952040585489124175799513 148464030439116843131849635)
        ·
          refine ⟨222696045658675264697774453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148464030439116843131849635 222696045658675264697774453)
          ·
            refine ⟨20877754280500806065416355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222696045658675264697774453 20877754280500806065416355)
            ·
              refine ⟨31316631420751209098124533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20877754280500806065416355 31316631420751209098124533)
              ·
                refine ⟨2935934195695425852949175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31316631420751209098124533 2935934195695425852949175)
                ·
                  refine ⟨4403901293543138779423763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935934195695425852949175 4403901293543138779423763)
                  ·
                    refine ⟨6605851940314708169135645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4403901293543138779423763 6605851940314708169135645)
                    ·
                      refine ⟨2477194477618015563425867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605851940314708169135645 2477194477618015563425867)
                      ·
                        rfl

theorem cell23_4824319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_4824319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824319 prefixEnd_4824319 := by exact prefixLift 4824319
  have htrace : WordTrace (prefixWord ++ tailWord_4824319) baseStart_4824319 baseEnd_4824319 := by
    simpa [prefixWord, tailWord_4824319, baseEnd_4824319] using wordTrace_append hprefix tailTrace_4824319
  have hstable : (prefixWord ++ tailWord_4824319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824319).length < 2 ^ (prefixWord ++ tailWord_4824319).sum := by decide
  have hdescent : baseEnd_4824319 < baseStart_4824319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824355 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4824355 : Nat := 118140960795 + 4824355 * 2 ^ 59
def prefixEnd_4824355 : Nat := 4983230072969 + 3 ^ 40 * 4824355 * 2
def baseEnd_4824355 : Nat := 2477212962921577422575701

theorem tailTrace_4824355 : CollatzResearch.WordTrace tailWord_4824355 prefixEnd_4824355 2477212962921577422575701 := by
  unfold tailWord_4824355
  simp only [CollatzResearch.WordTrace]
  refine ⟨175958682437193244082354519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117305788291462162721569679 175958682437193244082354519)
  ·
    refine ⟨263938023655789866123531779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175958682437193244082354519 263938023655789866123531779)
    ·
      refine ⟨395907035483684799185297669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263938023655789866123531779 395907035483684799185297669)
      ·
        refine ⟨74232569153190899847243313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395907035483684799185297669 74232569153190899847243313)
        ·
          refine ⟨55674426864893174885432485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74232569153190899847243313 55674426864893174885432485)
          ·
            refine ⟨10438955037167470291018591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55674426864893174885432485 10438955037167470291018591)
            ·
              refine ⟨15658432555751205436527887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10438955037167470291018591 15658432555751205436527887)
              ·
                refine ⟨23487648833626808154791831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15658432555751205436527887 23487648833626808154791831)
                ·
                  refine ⟨35231473250440212232187747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23487648833626808154791831 35231473250440212232187747)
                  ·
                    refine ⟨52847209875660318348281621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35231473250440212232187747 52847209875660318348281621)
                    ·
                      refine ⟨2477212962921577422575701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52847209875660318348281621 2477212962921577422575701)
                      ·
                        rfl

theorem cell23_4824355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4824355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824355 prefixEnd_4824355 := by exact prefixLift 4824355
  have htrace : WordTrace (prefixWord ++ tailWord_4824355) baseStart_4824355 baseEnd_4824355 := by
    simpa [prefixWord, tailWord_4824355, baseEnd_4824355] using wordTrace_append hprefix tailTrace_4824355
  have hstable : (prefixWord ++ tailWord_4824355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824355).length < 2 ^ (prefixWord ++ tailWord_4824355).sum := by decide
  have hdescent : baseEnd_4824355 < baseStart_4824355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824372 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4824372 : Nat := 118140960795 + 4824372 * 2 ^ 59
def prefixEnd_4824372 : Nat := 4983230072969 + 3 ^ 40 * 4824372 * 2
def baseEnd_4824372 : Nat := 2477221692092703856063123

theorem tailTrace_4824372 : CollatzResearch.WordTrace tailWord_4824372 prefixEnd_4824372 2477221692092703856063123 := by
  unfold tailWord_4824372
  simp only [CollatzResearch.WordTrace]
  refine ⟨87979651239065827992861685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117306201652087770657148913 87979651239065827992861685)
  ·
    refine ⟨8248092303662421374330783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87979651239065827992861685 8248092303662421374330783)
    ·
      refine ⟨12372138455493632061496175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248092303662421374330783 12372138455493632061496175)
      ·
        refine ⟨18558207683240448092244263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12372138455493632061496175 18558207683240448092244263)
        ·
          refine ⟨27837311524860672138366395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18558207683240448092244263 27837311524860672138366395)
          ·
            refine ⟨41755967287291008207549593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27837311524860672138366395 41755967287291008207549593)
            ·
              refine ⟨31316975465468256155662195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41755967287291008207549593 31316975465468256155662195)
              ·
                refine ⟨46975463198202384233493293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31316975465468256155662195 46975463198202384233493293)
                ·
                  refine ⟨17615798699325894087559985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46975463198202384233493293 17615798699325894087559985)
                  ·
                    refine ⟨13211849024494420565669989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17615798699325894087559985 13211849024494420565669989)
                    ·
                      refine ⟨2477221692092703856063123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13211849024494420565669989 2477221692092703856063123)
                      ·
                        rfl

theorem cell23_4824372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4824372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824372 prefixEnd_4824372 := by exact prefixLift 4824372
  have htrace : WordTrace (prefixWord ++ tailWord_4824372) baseStart_4824372 baseEnd_4824372 := by
    simpa [prefixWord, tailWord_4824372, baseEnd_4824372] using wordTrace_append hprefix tailTrace_4824372
  have hstable : (prefixWord ++ tailWord_4824372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824372).length < 2 ^ (prefixWord ++ tailWord_4824372).sum := by decide
  have hdescent : baseEnd_4824372 < baseStart_4824372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824402 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_4824402 : Nat := 118140960795 + 4824402 * 2 ^ 59
def prefixEnd_4824402 : Nat := 4983230072969 + 3 ^ 40 * 4824402 * 2
def baseEnd_4824402 : Nat := 2477237096512338738687985

theorem tailTrace_4824402 : CollatzResearch.WordTrace tailWord_4824402 prefixEnd_4824402 2477237096512338738687985 := by
  unfold tailWord_4824402
  simp only [CollatzResearch.WordTrace]
  refine ⟨43990099167005742777328865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117306931112015314072876973 43990099167005742777328865)
  ·
    refine ⟨32992574375254307082996649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43990099167005742777328865 32992574375254307082996649)
    ·
      refine ⟨24744430781440730312247487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32992574375254307082996649 24744430781440730312247487)
      ·
        refine ⟨37116646172161095468371231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24744430781440730312247487 37116646172161095468371231)
        ·
          refine ⟨55674969258241643202556847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37116646172161095468371231 55674969258241643202556847)
          ·
            refine ⟨83512453887362464803835271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55674969258241643202556847 83512453887362464803835271)
            ·
              refine ⟨125268680831043697205752907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83512453887362464803835271 125268680831043697205752907)
              ·
                refine ⟨187903021246565545808629361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125268680831043697205752907 187903021246565545808629361)
                ·
                  refine ⟨140927265934924159356472021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187903021246565545808629361 140927265934924159356472021)
                  ·
                    refine ⟨3302982795349784984917313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 140927265934924159356472021 3302982795349784984917313)
                    ·
                      refine ⟨2477237096512338738687985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302982795349784984917313 2477237096512338738687985)
                      ·
                        rfl

theorem cell23_4824402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_4824402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824402 prefixEnd_4824402 := by exact prefixLift 4824402
  have htrace : WordTrace (prefixWord ++ tailWord_4824402) baseStart_4824402 baseEnd_4824402 := by
    simpa [prefixWord, tailWord_4824402, baseEnd_4824402] using wordTrace_append hprefix tailTrace_4824402
  have hstable : (prefixWord ++ tailWord_4824402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824402).length < 2 ^ (prefixWord ++ tailWord_4824402).sum := by decide
  have hdescent : baseEnd_4824402 < baseStart_4824402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824413 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4824413 : Nat := 118140960795 + 4824413 * 2 ^ 59
def prefixEnd_4824413 : Nat := 4983230072969 + 3 ^ 40 * 4824413 * 2
def baseEnd_4824413 : Nat := 2477242744799538195650435

theorem tailTrace_4824413 : CollatzResearch.WordTrace tailWord_4824413 prefixEnd_4824413 2477242744799538195650435 := by
  unfold tailWord_4824413
  simp only [CollatzResearch.WordTrace]
  refine ⟨175960797870983119987965893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117307198580655413325310595 175960797870983119987965893)
  ·
    refine ⟨32992649600809334997743605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175960797870983119987965893 32992649600809334997743605)
    ·
      refine ⟨3093060900075875156038463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32992649600809334997743605 3093060900075875156038463)
      ·
        refine ⟨4639591350113812734057695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093060900075875156038463 4639591350113812734057695)
        ·
          refine ⟨6959387025170719101086543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4639591350113812734057695 6959387025170719101086543)
          ·
            refine ⟨10439080537756078651629815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6959387025170719101086543 10439080537756078651629815)
            ·
              refine ⟨15658620806634117977444723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10439080537756078651629815 15658620806634117977444723)
              ·
                refine ⟨23487931209951176966167085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15658620806634117977444723 23487931209951176966167085)
                ·
                  refine ⟨8807974203731691362312657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23487931209951176966167085 8807974203731691362312657)
                  ·
                    refine ⟨6605980652798768521734493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8807974203731691362312657 6605980652798768521734493)
                    ·
                      refine ⟨2477242744799538195650435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6605980652798768521734493 2477242744799538195650435)
                      ·
                        rfl

theorem cell23_4824413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4824413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824413 prefixEnd_4824413 := by exact prefixLift 4824413
  have htrace : WordTrace (prefixWord ++ tailWord_4824413) baseStart_4824413 baseEnd_4824413 := by
    simpa [prefixWord, tailWord_4824413, baseEnd_4824413] using wordTrace_append hprefix tailTrace_4824413
  have hstable : (prefixWord ++ tailWord_4824413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824413).length < 2 ^ (prefixWord ++ tailWord_4824413).sum := by decide
  have hdescent : baseEnd_4824413 < baseStart_4824413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824419 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 3, 3, 2]
def baseStart_4824419 : Nat := 118140960795 + 4824419 * 2 ^ 59
def prefixEnd_4824419 : Nat := 4983230072969 + 3 ^ 40 * 4824419 * 2
def baseEnd_4824419 : Nat := 2477245825683465172175407

theorem tailTrace_4824419 : CollatzResearch.WordTrace tailWord_4824419 prefixEnd_4824419 2477245825683465172175407 := by
  unfold tailWord_4824419
  simp only [CollatzResearch.WordTrace]
  refine ⟨175961016708961383012684311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117307344472640922008456207 175961016708961383012684311)
  ·
    refine ⟨263941525063442074519026467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175961016708961383012684311 263941525063442074519026467)
    ·
      refine ⟨395912287595163111778539701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263941525063442074519026467 395912287595163111778539701)
      ·
        refine ⟨37116776962046541729238097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 395912287595163111778539701 37116776962046541729238097)
        ·
          refine ⟨27837582721534906296928573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37116776962046541729238097 27837582721534906296928573)
          ·
            refine ⟨10439093520575589861348215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27837582721534906296928573 10439093520575589861348215)
            ·
              refine ⟨15658640280863384792022323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10439093520575589861348215 15658640280863384792022323)
              ·
                refine ⟨23487960421295077188033485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15658640280863384792022323 23487960421295077188033485)
                ·
                  refine ⟨8807985157985653945512557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23487960421295077188033485 8807985157985653945512557)
                  ·
                    refine ⟨3302994434244620229567209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8807985157985653945512557 3302994434244620229567209)
                    ·
                      refine ⟨2477245825683465172175407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3302994434244620229567209 2477245825683465172175407)
                      ·
                        rfl

theorem cell23_4824419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_4824419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824419 prefixEnd_4824419 := by exact prefixLift 4824419
  have htrace : WordTrace (prefixWord ++ tailWord_4824419) baseStart_4824419 baseEnd_4824419 := by
    simpa [prefixWord, tailWord_4824419, baseEnd_4824419] using wordTrace_append hprefix tailTrace_4824419
  have hstable : (prefixWord ++ tailWord_4824419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824419).length < 2 ^ (prefixWord ++ tailWord_4824419).sum := by decide
  have hdescent : baseEnd_4824419 < baseStart_4824419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824435 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 3]
def baseStart_4824435 : Nat := 118140960795 + 4824435 * 2 ^ 59
def prefixEnd_4824435 : Nat := 4983230072969 + 3 ^ 40 * 4824435 * 2
def baseEnd_4824435 : Nat := 2477254041373937109575333

theorem tailTrace_4824435 : CollatzResearch.WordTrace tailWord_4824435 prefixEnd_4824435 2477254041373937109575333 := by
  unfold tailWord_4824435
  simp only [CollatzResearch.WordTrace]
  refine ⟨175961600276903417745266759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117307733517935611830177839 175961600276903417745266759)
  ·
    refine ⟨263942400415355126617900139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175961600276903417745266759 263942400415355126617900139)
    ·
      refine ⟨395913600623032689926850209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263942400415355126617900139 395913600623032689926850209)
      ·
        refine ⟨296935200467274517445137657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395913600623032689926850209 296935200467274517445137657)
        ·
          refine ⟨222701400350455888083853243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296935200467274517445137657 222701400350455888083853243)
          ·
            refine ⟨334052100525683832125779865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222701400350455888083853243 334052100525683832125779865)
            ·
              refine ⟨250539075394262874094334899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334052100525683832125779865 250539075394262874094334899)
              ·
                refine ⟨375808613091394311141502349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250539075394262874094334899 375808613091394311141502349)
                ·
                  refine ⟨140928229909272866678063381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375808613091394311141502349 140928229909272866678063381)
                  ·
                    refine ⟨6606010776997165625534221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 140928229909272866678063381 6606010776997165625534221)
                    ·
                      refine ⟨2477254041373937109575333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6606010776997165625534221 2477254041373937109575333)
                      ·
                        rfl

theorem cell23_4824435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_4824435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824435 prefixEnd_4824435 := by exact prefixLift 4824435
  have htrace : WordTrace (prefixWord ++ tailWord_4824435) baseStart_4824435 baseEnd_4824435 := by
    simpa [prefixWord, tailWord_4824435, baseEnd_4824435] using wordTrace_append hprefix tailTrace_4824435
  have hstable : (prefixWord ++ tailWord_4824435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824435).length < 2 ^ (prefixWord ++ tailWord_4824435).sum := by decide
  have hdescent : baseEnd_4824435 < baseStart_4824435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824452 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4824452 : Nat := 118140960795 + 4824452 * 2 ^ 59
def prefixEnd_4824452 : Nat := 4983230072969 + 3 ^ 40 * 4824452 * 2
def baseEnd_4824452 : Nat := 2477262770545063543062755

theorem tailTrace_4824452 : CollatzResearch.WordTrace tailWord_4824452 prefixEnd_4824452 2477262770545063543062755 := by
  unfold tailWord_4824452
  simp only [CollatzResearch.WordTrace]
  refine ⟨87981110158920914824317805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117308146878561219765757073 87981110158920914824317805)
  ·
    refine ⟨32992916309595343059119177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87981110158920914824317805 32992916309595343059119177)
    ·
      refine ⟨24744687232196507294339383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32992916309595343059119177 24744687232196507294339383)
      ·
        refine ⟨37117030848294760941509075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24744687232196507294339383 37117030848294760941509075)
        ·
          refine ⟨55675546272442141412263613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37117030848294760941509075 55675546272442141412263613)
          ·
            refine ⟨20878329852165803029598855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55675546272442141412263613 20878329852165803029598855)
            ·
              refine ⟨31317494778248704544398283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20878329852165803029598855 31317494778248704544398283)
              ·
                refine ⟨46976242167373056816597425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31317494778248704544398283 46976242167373056816597425)
                ·
                  refine ⟨35232181625529792612448069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46976242167373056816597425 35232181625529792612448069)
                  ·
                    refine ⟨6606034054786836114834013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35232181625529792612448069 6606034054786836114834013)
                    ·
                      refine ⟨2477262770545063543062755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6606034054786836114834013 2477262770545063543062755)
                      ·
                        rfl

theorem cell23_4824452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4824452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824452 prefixEnd_4824452 := by exact prefixLift 4824452
  have htrace : WordTrace (prefixWord ++ tailWord_4824452) baseStart_4824452 baseEnd_4824452 := by
    simpa [prefixWord, tailWord_4824452, baseEnd_4824452] using wordTrace_append hprefix tailTrace_4824452
  have hstable : (prefixWord ++ tailWord_4824452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824452).length < 2 ^ (prefixWord ++ tailWord_4824452).sum := by decide
  have hdescent : baseEnd_4824452 < baseStart_4824452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824495 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_4824495 : Nat := 118140960795 + 4824495 * 2 ^ 59
def prefixEnd_4824495 : Nat := 4983230072969 + 3 ^ 40 * 4824495 * 2
def baseEnd_4824495 : Nat := 2477284850213206874825057

theorem tailTrace_4824495 : CollatzResearch.WordTrace tailWord_4824495 prefixEnd_4824495 2477284850213206874825057 := by
  unfold tailWord_4824495
  simp only [CollatzResearch.WordTrace]
  refine ⟨175963788656686047992450939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117309192437790698661633959 175963788656686047992450939)
  ·
    refine ⟨263945682985029071988676409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175963788656686047992450939 263945682985029071988676409)
    ·
      refine ⟨197959262238771803991507307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263945682985029071988676409 197959262238771803991507307)
      ·
        refine ⟨296938893358157705987260961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197959262238771803991507307 296938893358157705987260961)
        ·
          refine ⟨222704170018618279490445721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296938893358157705987260961 222704170018618279490445721)
          ·
            refine ⟨167028127513963709617834291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222704170018618279490445721 167028127513963709617834291)
            ·
              refine ⟨250542191270945564426751437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167028127513963709617834291 250542191270945564426751437)
              ·
                refine ⟨93953321726604586660031789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250542191270945564426751437 93953321726604586660031789)
                ·
                  refine ⟨35232495647476719997511921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93953321726604586660031789 35232495647476719997511921)
                  ·
                    refine ⟨26424371735607539998133941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35232495647476719997511921 26424371735607539998133941)
                    ·
                      refine ⟨2477284850213206874825057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26424371735607539998133941 2477284850213206874825057)
                      ·
                        rfl

theorem cell23_4824495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_4824495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824495 prefixEnd_4824495 := by exact prefixLift 4824495
  have htrace : WordTrace (prefixWord ++ tailWord_4824495) baseStart_4824495 baseEnd_4824495 := by
    simpa [prefixWord, tailWord_4824495, baseEnd_4824495] using wordTrace_append hprefix tailTrace_4824495
  have hstable : (prefixWord ++ tailWord_4824495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824495).length < 2 ^ (prefixWord ++ tailWord_4824495).sum := by decide
  have hdescent : baseEnd_4824495 < baseStart_4824495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824522 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_4824522 : Nat := 118140960795 + 4824522 * 2 ^ 59
def prefixEnd_4824522 : Nat := 4983230072969 + 3 ^ 40 * 4824522 * 2
def baseEnd_4824522 : Nat := 2477298714190878269187433

theorem tailTrace_4824522 : CollatzResearch.WordTrace tailWord_4824522 prefixEnd_4824522 2477298714190878269187433 := by
  unfold tailWord_4824522
  simp only [CollatzResearch.WordTrace]
  refine ⟨43991193356897057900920955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117309848951725487735789213 43991193356897057900920955)
  ·
    refine ⟨65986790035345586851381433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43991193356897057900920955 65986790035345586851381433)
    ·
      refine ⟨49490092526509190138536075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65986790035345586851381433 49490092526509190138536075)
      ·
        refine ⟨74235138789763785207804113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49490092526509190138536075 74235138789763785207804113)
        ·
          refine ⟨55676354092322838905853085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74235138789763785207804113 55676354092322838905853085)
          ·
            refine ⟨20878632784621064589694907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55676354092322838905853085 20878632784621064589694907)
            ·
              refine ⟨31317949176931596884542361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20878632784621064589694907 31317949176931596884542361)
              ·
                refine ⟨23488461882698697663406771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31317949176931596884542361 23488461882698697663406771)
                ·
                  refine ⟨35232692824048046495110157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23488461882698697663406771 35232692824048046495110157)
                  ·
                    refine ⟨13212259809018017435666309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35232692824048046495110157 13212259809018017435666309)
                    ·
                      refine ⟨2477298714190878269187433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13212259809018017435666309 2477298714190878269187433)
                      ·
                        rfl

theorem cell23_4824522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_4824522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824522 prefixEnd_4824522 := by exact prefixLift 4824522
  have htrace : WordTrace (prefixWord ++ tailWord_4824522) baseStart_4824522 baseEnd_4824522 := by
    simpa [prefixWord, tailWord_4824522, baseEnd_4824522] using wordTrace_append hprefix tailTrace_4824522
  have hstable : (prefixWord ++ tailWord_4824522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824522).length < 2 ^ (prefixWord ++ tailWord_4824522).sum := by decide
  have hdescent : baseEnd_4824522 < baseStart_4824522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824566 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_4824566 : Nat := 118140960795 + 4824566 * 2 ^ 59
def prefixEnd_4824566 : Nat := 4983230072969 + 3 ^ 40 * 4824566 * 2
def baseEnd_4824566 : Nat := 825773769113225365679077

theorem tailTrace_4824566 : CollatzResearch.WordTrace tailWord_4824566 prefixEnd_4824566 825773769113225365679077 := by
  unfold tailWord_4824566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10997898639964301694892847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117310918826285884745523701 10997898639964301694892847)
  ·
    refine ⟨16496847959946452542339271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10997898639964301694892847 16496847959946452542339271)
    ·
      refine ⟨24745271939919678813508907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16496847959946452542339271 24745271939919678813508907)
      ·
        refine ⟨37117907909879518220263361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24745271939919678813508907 37117907909879518220263361)
        ·
          refine ⟨27838430932409638665197521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37117907909879518220263361 27838430932409638665197521)
          ·
            refine ⟨20878823199307228998898141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27838430932409638665197521 20878823199307228998898141)
            ·
              refine ⟨7829558699740210874586803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20878823199307228998898141 7829558699740210874586803)
              ·
                refine ⟨11744338049610316311880205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829558699740210874586803 11744338049610316311880205)
                ·
                  refine ⟨4404126768603868616955077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11744338049610316311880205 4404126768603868616955077)
                  ·
                    refine ⟨825773769113225365679077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4404126768603868616955077 825773769113225365679077)
                    ·
                      rfl

theorem cell23_4824566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_4824566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824566 prefixEnd_4824566 := by exact prefixLift 4824566
  have htrace : WordTrace (prefixWord ++ tailWord_4824566) baseStart_4824566 baseEnd_4824566 := by
    simpa [prefixWord, tailWord_4824566, baseEnd_4824566] using wordTrace_append hprefix tailTrace_4824566
  have hstable : (prefixWord ++ tailWord_4824566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824566).length < 2 ^ (prefixWord ++ tailWord_4824566).sum := by decide
  have hdescent : baseEnd_4824566 < baseStart_4824566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824629 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4824629 : Nat := 118140960795 + 4824629 * 2 ^ 59
def prefixEnd_4824629 : Nat := 4983230072969 + 3 ^ 40 * 4824629 * 2
def baseEnd_4824629 : Nat := 2477353656620909350549441

theorem tailTrace_4824629 : CollatzResearch.WordTrace tailWord_4824629 prefixEnd_4824629 2477353656620909350549441 := by
  unfold tailWord_4824629
  simp only [CollatzResearch.WordTrace]
  refine ⟨175968676038200588877828941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117312450692133725918552627 175968676038200588877828941)
  ·
    refine ⟨65988253514325220829185853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175968676038200588877828941 65988253514325220829185853)
    ·
      refine ⟨24745595067871957810944695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65988253514325220829185853 24745595067871957810944695)
      ·
        refine ⟨37118392601807936716417043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24745595067871957810944695 37118392601807936716417043)
        ·
          refine ⟨55677588902711905074625565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37118392601807936716417043 55677588902711905074625565)
          ·
            refine ⟨20879095838516964402984587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55677588902711905074625565 20879095838516964402984587)
            ·
              refine ⟨31318643757775446604476881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20879095838516964402984587 31318643757775446604476881)
              ·
                refine ⟨23488982818331584953357661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31318643757775446604476881 23488982818331584953357661)
                ·
                  refine ⟨8808368556874344357509123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23488982818331584953357661 8808368556874344357509123)
                  ·
                    refine ⟨13212552835311516536263685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8808368556874344357509123 13212552835311516536263685)
                    ·
                      refine ⟨2477353656620909350549441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13212552835311516536263685 2477353656620909350549441)
                      ·
                        rfl

theorem cell23_4824629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4824629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824629 prefixEnd_4824629 := by exact prefixLift 4824629
  have htrace : WordTrace (prefixWord ++ tailWord_4824629) baseStart_4824629 baseEnd_4824629 := by
    simpa [prefixWord, tailWord_4824629, baseEnd_4824629] using wordTrace_append hprefix tailTrace_4824629
  have hstable : (prefixWord ++ tailWord_4824629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824629).length < 2 ^ (prefixWord ++ tailWord_4824629).sum := by decide
  have hdescent : baseEnd_4824629 < baseStart_4824629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824639 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 1, 6]
def baseStart_4824639 : Nat := 118140960795 + 4824639 * 2 ^ 59
def prefixEnd_4824639 : Nat := 4983230072969 + 3 ^ 40 * 4824639 * 2
def baseEnd_4824639 : Nat := 825786263809151437141465

theorem tailTrace_4824639 : CollatzResearch.WordTrace tailWord_4824639 prefixEnd_4824639 825786263809151437141465 := by
  unfold tailWord_4824639
  simp only [CollatzResearch.WordTrace]
  refine ⟨175969040768164360585692971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117312693845442907057128647 175969040768164360585692971)
  ·
    refine ⟨263953561152246540878539457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175969040768164360585692971 263953561152246540878539457)
    ·
      refine ⟨197965170864184905658904593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263953561152246540878539457 197965170864184905658904593)
      ·
        refine ⟨148473878148138679244178445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197965170864184905658904593 148473878148138679244178445)
        ·
          refine ⟨55677704305552004716566917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148473878148138679244178445 55677704305552004716566917)
          ·
            refine ⟨10439569557291000884356297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55677704305552004716566917 10439569557291000884356297)
            ·
              refine ⟨7829677167968250663267223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10439569557291000884356297 7829677167968250663267223)
              ·
                refine ⟨11744515751952375994900835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829677167968250663267223 11744515751952375994900835)
                ·
                  refine ⟨17616773627928563992351253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11744515751952375994900835 17616773627928563992351253)
                  ·
                    refine ⟨825786263809151437141465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17616773627928563992351253 825786263809151437141465)
                    ·
                      rfl

theorem cell23_4824639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_4824639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824639 prefixEnd_4824639 := by exact prefixLift 4824639
  have htrace : WordTrace (prefixWord ++ tailWord_4824639) baseStart_4824639 baseEnd_4824639 := by
    simpa [prefixWord, tailWord_4824639, baseEnd_4824639] using wordTrace_append hprefix tailTrace_4824639
  have hstable : (prefixWord ++ tailWord_4824639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824639).length < 2 ^ (prefixWord ++ tailWord_4824639).sum := by decide
  have hdescent : baseEnd_4824639 < baseStart_4824639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824663 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 1, 1, 4]
def baseStart_4824663 : Nat := 118140960795 + 4824663 * 2 ^ 59
def prefixEnd_4824663 : Nat := 4983230072969 + 3 ^ 40 * 4824663 * 2
def baseEnd_4824663 : Nat := 2477371114963162217524285

theorem tailTrace_4824663 : CollatzResearch.WordTrace tailWord_4824663 prefixEnd_4824663 2477371114963162217524285 := by
  unfold tailWord_4824663
  simp only [CollatzResearch.WordTrace]
  refine ⟨175969916120077412684566643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117313277413384941789711095 175969916120077412684566643)
  ·
    refine ⟨263954874180116119026849965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175969916120077412684566643 263954874180116119026849965)
    ·
      refine ⟨98983077817543544635068737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263954874180116119026849965 98983077817543544635068737)
      ·
        refine ⟨74237308363157658476301553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98983077817543544635068737 74237308363157658476301553)
        ·
          refine ⟨55677981272368243857226165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74237308363157658476301553 55677981272368243857226165)
          ·
            refine ⟨5219810744284522861614953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55677981272368243857226165 5219810744284522861614953)
            ·
              refine ⟨3914858058213392146211215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5219810744284522861614953 3914858058213392146211215)
              ·
                refine ⟨5872287087320088219316823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914858058213392146211215 5872287087320088219316823)
                ·
                  refine ⟨8808430630980132328975235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5872287087320088219316823 8808430630980132328975235)
                  ·
                    refine ⟨13212645946470198493462853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8808430630980132328975235 13212645946470198493462853)
                    ·
                      refine ⟨2477371114963162217524285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13212645946470198493462853 2477371114963162217524285)
                      ·
                        rfl

theorem cell23_4824663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_4824663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824663 prefixEnd_4824663 := by exact prefixLift 4824663
  have htrace : WordTrace (prefixWord ++ tailWord_4824663) baseStart_4824663 baseEnd_4824663 := by
    simpa [prefixWord, tailWord_4824663, baseEnd_4824663] using wordTrace_append hprefix tailTrace_4824663
  have hstable : (prefixWord ++ tailWord_4824663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824663).length < 2 ^ (prefixWord ++ tailWord_4824663).sum := by decide
  have hdescent : baseEnd_4824663 < baseStart_4824663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824672 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_4824672 : Nat := 118140960795 + 4824672 * 2 ^ 59
def prefixEnd_4824672 : Nat := 4983230072969 + 3 ^ 40 * 4824672 * 2
def baseEnd_4824672 : Nat := 2477375736289052682311743

theorem tailTrace_4824672 : CollatzResearch.WordTrace tailWord_4824672 prefixEnd_4824672 2477375736289052682311743 := by
  unfold tailWord_4824672
  simp only [CollatzResearch.WordTrace]
  refine ⟨87985122188522403610822135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117313496251363204814429513 87985122188522403610822135)
  ·
    refine ⟨131977683282783605416233203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87985122188522403610822135 131977683282783605416233203)
    ·
      refine ⟨197966524924175408124349805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131977683282783605416233203 197966524924175408124349805)
      ·
        refine ⟨74237446846565778046631177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197966524924175408124349805 74237446846565778046631177)
        ·
          refine ⟨55678085134924333534973383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74237446846565778046631177 55678085134924333534973383)
          ·
            refine ⟨83517127702386500302460075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55678085134924333534973383 83517127702386500302460075)
            ·
              refine ⟨125275691553579750453690113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83517127702386500302460075 125275691553579750453690113)
              ·
                refine ⟨93956768665184812840267585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125275691553579750453690113 93956768665184812840267585)
                ·
                  refine ⟨70467576498888609630200689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93956768665184812840267585 70467576498888609630200689)
                  ·
                    refine ⟨52850682374166457222650517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70467576498888609630200689 52850682374166457222650517)
                    ·
                      refine ⟨2477375736289052682311743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52850682374166457222650517 2477375736289052682311743)
                      ·
                        rfl

theorem cell23_4824672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_4824672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824672 prefixEnd_4824672 := by exact prefixLift 4824672
  have htrace : WordTrace (prefixWord ++ tailWord_4824672) baseStart_4824672 baseEnd_4824672 := by
    simpa [prefixWord, tailWord_4824672, baseEnd_4824672] using wordTrace_append hprefix tailTrace_4824672
  have hstable : (prefixWord ++ tailWord_4824672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824672).length < 2 ^ (prefixWord ++ tailWord_4824672).sum := by decide
  have hdescent : baseEnd_4824672 < baseStart_4824672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824679 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_4824679 : Nat := 118140960795 + 4824679 * 2 ^ 59
def prefixEnd_4824679 : Nat := 4983230072969 + 3 ^ 40 * 4824679 * 2
def baseEnd_4824679 : Nat := 2477379330653634154924211

theorem tailTrace_4824679 : CollatzResearch.WordTrace tailWord_4824679 prefixEnd_4824679 2477379330653634154924211 := by
  unfold tailWord_4824679
  simp only [CollatzResearch.WordTrace]
  refine ⟨175970499688019447417149091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117313666458679631611432727 175970499688019447417149091)
  ·
    refine ⟨263955749532029171125723637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175970499688019447417149091 263955749532029171125723637)
    ·
      refine ⟨24745851518627734793036591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 263955749532029171125723637 24745851518627734793036591)
      ·
        refine ⟨37118777277941602189554887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24745851518627734793036591 37118777277941602189554887)
        ·
          refine ⟨55678165916912403284332331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37118777277941602189554887 55678165916912403284332331)
          ·
            refine ⟨83517248875368604926498497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55678165916912403284332331 83517248875368604926498497)
            ·
              refine ⟨62637936656526453694873873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83517248875368604926498497 62637936656526453694873873)
              ·
                refine ⟨46978452492394840271155405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62637936656526453694873873 46978452492394840271155405)
                ·
                  refine ⟨17616919684648065101683277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46978452492394840271155405 17616919684648065101683277)
                  ·
                    refine ⟨6606344881743024413131229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17616919684648065101683277 6606344881743024413131229)
                    ·
                      refine ⟨2477379330653634154924211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6606344881743024413131229 2477379330653634154924211)
                      ·
                        rfl

theorem cell23_4824679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_4824679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824679 prefixEnd_4824679 := by exact prefixLift 4824679
  have htrace : WordTrace (prefixWord ++ tailWord_4824679) baseStart_4824679 baseEnd_4824679 := by
    simpa [prefixWord, tailWord_4824679, baseEnd_4824679] using wordTrace_append hprefix tailTrace_4824679
  have hstable : (prefixWord ++ tailWord_4824679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824679).length < 2 ^ (prefixWord ++ tailWord_4824679).sum := by decide
  have hdescent : baseEnd_4824679 < baseStart_4824679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824680 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4824680 : Nat := 118140960795 + 4824680 * 2 ^ 59
def prefixEnd_4824680 : Nat := 4983230072969 + 3 ^ 40 * 4824680 * 2
def baseEnd_4824680 : Nat := 2477379844134288651011707

theorem tailTrace_4824680 : CollatzResearch.WordTrace tailWord_4824680 prefixEnd_4824680 2477379844134288651011707 := by
  unfold tailWord_4824680
  simp only [CollatzResearch.WordTrace]
  refine ⟨87985268080507912293967747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117313690774010549725290329 87985268080507912293967747)
  ·
    refine ⟨131977902120761868440951621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87985268080507912293967747 131977902120761868440951621)
    ·
      refine ⟨24745856647642850332678429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131977902120761868440951621 24745856647642850332678429)
      ·
        refine ⟨9279696242866068874754411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24745856647642850332678429 9279696242866068874754411)
        ·
          refine ⟨13919544364299103312131617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9279696242866068874754411 13919544364299103312131617)
          ·
            refine ⟨10439658273224327484098713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13919544364299103312131617 10439658273224327484098713)
            ·
              refine ⟨7829743704918245613074035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10439658273224327484098713 7829743704918245613074035)
              ·
                refine ⟨11744615557377368419611053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829743704918245613074035 11744615557377368419611053)
                ·
                  refine ⟨4404230834016513157354145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11744615557377368419611053 4404230834016513157354145)
                  ·
                    refine ⟨3303173125512384868015609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4404230834016513157354145 3303173125512384868015609)
                    ·
                      refine ⟨2477379844134288651011707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303173125512384868015609 2477379844134288651011707)
                      ·
                        rfl

theorem cell23_4824680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4824680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824680 prefixEnd_4824680 := by exact prefixLift 4824680
  have htrace : WordTrace (prefixWord ++ tailWord_4824680) baseStart_4824680 baseEnd_4824680 := by
    simpa [prefixWord, tailWord_4824680, baseEnd_4824680] using wordTrace_append hprefix tailTrace_4824680
  have hstable : (prefixWord ++ tailWord_4824680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824680).length < 2 ^ (prefixWord ++ tailWord_4824680).sum := by decide
  have hdescent : baseEnd_4824680 < baseStart_4824680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824693 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4824693 : Nat := 118140960795 + 4824693 * 2 ^ 59
def prefixEnd_4824693 : Nat := 4983230072969 + 3 ^ 40 * 4824693 * 2
def baseEnd_4824693 : Nat := 2477386519382797100149147

theorem tailTrace_4824693 : CollatzResearch.WordTrace tailWord_4824693 prefixEnd_4824693 2477386519382797100149147 := by
  unfold tailWord_4824693
  simp only [CollatzResearch.WordTrace]
  refine ⟨175971010309968727808158733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117314006873312485205439155 175971010309968727808158733)
  ·
    refine ⟨65989128866238272928059525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175971010309968727808158733 65989128866238272928059525)
    ·
      refine ⟨12372961662419676174011161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65989128866238272928059525 12372961662419676174011161)
      ·
        refine ⟨9279721246814757130508371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12372961662419676174011161 9279721246814757130508371)
        ·
          refine ⟨13919581870222135695762557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9279721246814757130508371 13919581870222135695762557)
          ·
            refine ⟨5219843201333300885910959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13919581870222135695762557 5219843201333300885910959)
            ·
              refine ⟨7829764801999951328866439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219843201333300885910959 7829764801999951328866439)
              ·
                refine ⟨11744647202999926993299659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829764801999951328866439 11744647202999926993299659)
                ·
                  refine ⟨17616970804499890489949489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11744647202999926993299659 17616970804499890489949489)
                  ·
                    refine ⟨13212728103374917867462117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17616970804499890489949489 13212728103374917867462117)
                    ·
                      refine ⟨2477386519382797100149147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13212728103374917867462117 2477386519382797100149147)
                      ·
                        rfl

theorem cell23_4824693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4824693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824693 prefixEnd_4824693 := by exact prefixLift 4824693
  have htrace : WordTrace (prefixWord ++ tailWord_4824693) baseStart_4824693 baseEnd_4824693 := by
    simpa [prefixWord, tailWord_4824693, baseEnd_4824693] using wordTrace_append hprefix tailTrace_4824693
  have hstable : (prefixWord ++ tailWord_4824693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824693).length < 2 ^ (prefixWord ++ tailWord_4824693).sum := by decide
  have hdescent : baseEnd_4824693 < baseStart_4824693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824739 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 3]
def baseStart_4824739 : Nat := 118140960795 + 4824739 * 2 ^ 59
def prefixEnd_4824739 : Nat := 4983230072969 + 3 ^ 40 * 4824739 * 2
def baseEnd_4824739 : Nat := 2477410139492903920173935

theorem tailTrace_4824739 : CollatzResearch.WordTrace tailWord_4824739 prefixEnd_4824739 2477410139492903920173935 := by
  unfold tailWord_4824739
  simp only [CollatzResearch.WordTrace]
  refine ⟨175972688067802077664333271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117315125378534718442888847 175972688067802077664333271)
  ·
    refine ⟨263959032101703116496499907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175972688067802077664333271 263959032101703116496499907)
    ·
      refine ⟨395938548152554674744749861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263959032101703116496499907 395938548152554674744749861)
      ·
        refine ⟨74238477778604001514640599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 395938548152554674744749861 74238477778604001514640599)
        ·
          refine ⟨111357716667906002271960899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74238477778604001514640599 111357716667906002271960899)
          ·
            refine ⟨167036575001859003407941349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111357716667906002271960899 167036575001859003407941349)
            ·
              refine ⟨31319357812848563138989003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167036575001859003407941349 31319357812848563138989003)
              ·
                refine ⟨46979036719272844708483505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31319357812848563138989003 46979036719272844708483505)
                ·
                  refine ⟨35234277539454633531362629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46979036719272844708483505 35234277539454633531362629)
                  ·
                    refine ⟨6606427038647743787130493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35234277539454633531362629 6606427038647743787130493)
                    ·
                      refine ⟨2477410139492903920173935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6606427038647743787130493 2477410139492903920173935)
                      ·
                        rfl

theorem cell23_4824739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_4824739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824739 prefixEnd_4824739 := by exact prefixLift 4824739
  have htrace : WordTrace (prefixWord ++ tailWord_4824739) baseStart_4824739 baseEnd_4824739 := by
    simpa [prefixWord, tailWord_4824739, baseEnd_4824739] using wordTrace_append hprefix tailTrace_4824739
  have hstable : (prefixWord ++ tailWord_4824739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824739).length < 2 ^ (prefixWord ++ tailWord_4824739).sum := by decide
  have hdescent : baseEnd_4824739 < baseStart_4824739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824757 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_4824757 : Nat := 118140960795 + 4824757 * 2 ^ 59
def prefixEnd_4824757 : Nat := 4983230072969 + 3 ^ 40 * 4824757 * 2
def baseEnd_4824757 : Nat := 2477419382144684849748853

theorem tailTrace_4824757 : CollatzResearch.WordTrace tailWord_4824757 prefixEnd_4824757 2477419382144684849748853 := by
  unfold tailWord_4824757
  simp only [CollatzResearch.WordTrace]
  refine ⟨175973344581736866738488525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117315563054491244492325683 175973344581736866738488525)
  ·
    refine ⟨65990004218151325026933197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175973344581736866738488525 65990004218151325026933197)
    ·
      refine ⟨24746251581806746885099949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65990004218151325026933197 24746251581806746885099949)
      ·
        refine ⟨9279844343177530081912481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24746251581806746885099949 9279844343177530081912481)
        ·
          refine ⟨6959883257383147561434361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9279844343177530081912481 6959883257383147561434361)
          ·
            refine ⟨5219912443037360671075771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6959883257383147561434361 5219912443037360671075771)
            ·
              refine ⟨7829868664556041006613657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219912443037360671075771 7829868664556041006613657)
              ·
                refine ⟨5872401498417030754960243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7829868664556041006613657 5872401498417030754960243)
                ·
                  refine ⟨8808602247625546132440365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5872401498417030754960243 8808602247625546132440365)
                  ·
                    refine ⟨3303225842859579799665137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8808602247625546132440365 3303225842859579799665137)
                    ·
                      refine ⟨2477419382144684849748853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303225842859579799665137 2477419382144684849748853)
                      ·
                        rfl

theorem cell23_4824757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_4824757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824757 prefixEnd_4824757 := by exact prefixLift 4824757
  have htrace : WordTrace (prefixWord ++ tailWord_4824757) baseStart_4824757 baseEnd_4824757 := by
    simpa [prefixWord, tailWord_4824757, baseEnd_4824757] using wordTrace_append hprefix tailTrace_4824757
  have hstable : (prefixWord ++ tailWord_4824757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824757).length < 2 ^ (prefixWord ++ tailWord_4824757).sum := by decide
  have hdescent : baseEnd_4824757 < baseStart_4824757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824776 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 5]
def baseStart_4824776 : Nat := 118140960795 + 4824776 * 2 ^ 59
def prefixEnd_4824776 : Nat := 4983230072969 + 3 ^ 40 * 4824776 * 2
def baseEnd_4824776 : Nat := 275269904253013363934585

theorem tailTrace_4824776 : CollatzResearch.WordTrace tailWord_4824776 prefixEnd_4824776 275269904253013363934585 := by
  unfold tailWord_4824776
  simp only [CollatzResearch.WordTrace]
  refine ⟨87987018784334016491715091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117316025045778688655620121 87987018784334016491715091)
  ·
    refine ⟨131980528176501024737572637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87987018784334016491715091 131980528176501024737572637)
    ·
      refine ⟨49492698066187884276589739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131980528176501024737572637 49492698066187884276589739)
      ·
        refine ⟨74239047099281826414884609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49492698066187884276589739 74239047099281826414884609)
        ·
          refine ⟨55679285324461369811163457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74239047099281826414884609 55679285324461369811163457)
          ·
            refine ⟨41759463993346027358372593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55679285324461369811163457 41759463993346027358372593)
            ·
              refine ⟨31319597995009520518779445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41759463993346027358372593 31319597995009520518779445)
              ·
                refine ⟨2936212312032142548635573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31319597995009520518779445 2936212312032142548635573)
                ·
                  refine ⟨275269904253013363934585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2936212312032142548635573 275269904253013363934585)
                  ·
                    rfl

theorem cell23_4824776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 5].length) (baseStart_4824776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824776 prefixEnd_4824776 := by exact prefixLift 4824776
  have htrace : WordTrace (prefixWord ++ tailWord_4824776) baseStart_4824776 baseEnd_4824776 := by
    simpa [prefixWord, tailWord_4824776, baseEnd_4824776] using wordTrace_append hprefix tailTrace_4824776
  have hstable : (prefixWord ++ tailWord_4824776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824776).length < 2 ^ (prefixWord ++ tailWord_4824776).sum := by decide
  have hdescent : baseEnd_4824776 < baseStart_4824776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824793 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 5]
def baseStart_4824793 : Nat := 118140960795 + 4824793 * 2 ^ 59
def prefixEnd_4824793 : Nat := 4983230072969 + 3 ^ 40 * 4824793 * 2
def baseEnd_4824793 : Nat := 275270874160916300988743

theorem tailTrace_4824793 : CollatzResearch.WordTrace tailWord_4824793 prefixEnd_4824793 275270874160916300988743 := by
  unfold tailWord_4824793
  simp only [CollatzResearch.WordTrace]
  refine ⟨175974657609606444886799033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117316438406404296591199355 175974657609606444886799033)
  ·
    refine ⟨131980993207204833665099275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175974657609606444886799033 131980993207204833665099275)
    ·
      refine ⟨197971489810807250497648913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131980993207204833665099275 197971489810807250497648913)
      ·
        refine ⟨148478617358105437873236685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197971489810807250497648913 148478617358105437873236685)
        ·
          refine ⟨55679481509289539202463757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148478617358105437873236685 55679481509289539202463757)
          ·
            refine ⟨20879805565983577200923909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55679481509289539202463757 20879805565983577200923909)
            ·
              refine ⟨3914963543621920725173233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20879805565983577200923909 3914963543621920725173233)
              ·
                refine ⟨2936222657716440543879925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3914963543621920725173233 2936222657716440543879925)
                ·
                  refine ⟨275270874160916300988743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2936222657716440543879925 275270874160916300988743)
                  ·
                    rfl

theorem cell23_4824793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 5].length) (baseStart_4824793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824793 prefixEnd_4824793 := by exact prefixLift 4824793
  have htrace : WordTrace (prefixWord ++ tailWord_4824793) baseStart_4824793 baseEnd_4824793 := by
    simpa [prefixWord, tailWord_4824793, baseEnd_4824793] using wordTrace_append hprefix tailTrace_4824793
  have hstable : (prefixWord ++ tailWord_4824793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824793).length < 2 ^ (prefixWord ++ tailWord_4824793).sum := by decide
  have hdescent : baseEnd_4824793 < baseStart_4824793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824799 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_4824799 : Nat := 118140960795 + 4824799 * 2 ^ 59
def prefixEnd_4824799 : Nat := 4983230072969 + 3 ^ 40 * 4824799 * 2
def baseEnd_4824799 : Nat := 2477440948332173685423659

theorem tailTrace_4824799 : CollatzResearch.WordTrace tailWord_4824799 prefixEnd_4824799 2477440948332173685423659 := by
  unfold tailWord_4824799
  simp only [CollatzResearch.WordTrace]
  refine ⟨175974876447584707911517451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117316584298389805274344967 175974876447584707911517451)
  ·
    refine ⟨263962314671377061867276177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175974876447584707911517451 263962314671377061867276177)
    ·
      refine ⟨197971736003532796400457133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263962314671377061867276177 197971736003532796400457133)
      ·
        refine ⟨74239401001324798650171425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197971736003532796400457133 74239401001324798650171425)
        ·
          refine ⟨55679550750993598987628569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74239401001324798650171425 55679550750993598987628569)
          ·
            refine ⟨41759663063245199240721427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55679550750993598987628569 41759663063245199240721427)
            ·
              refine ⟨62639494594867798861082141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41759663063245199240721427 62639494594867798861082141)
              ·
                refine ⟨23489810473075424572905803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62639494594867798861082141 23489810473075424572905803)
                ·
                  refine ⟨35234715709613136859358705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23489810473075424572905803 35234715709613136859358705)
                  ·
                    refine ⟨26426036782209852644519029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35234715709613136859358705 26426036782209852644519029)
                    ·
                      refine ⟨2477440948332173685423659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26426036782209852644519029 2477440948332173685423659)
                      ·
                        rfl

theorem cell23_4824799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_4824799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824799 prefixEnd_4824799 := by exact prefixLift 4824799
  have htrace : WordTrace (prefixWord ++ tailWord_4824799) baseStart_4824799 baseEnd_4824799 := by
    simpa [prefixWord, tailWord_4824799, baseEnd_4824799] using wordTrace_append hprefix tailTrace_4824799
  have hstable : (prefixWord ++ tailWord_4824799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824799).length < 2 ^ (prefixWord ++ tailWord_4824799).sum := by decide
  have hdescent : baseEnd_4824799 < baseStart_4824799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824803 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4824803 : Nat := 118140960795 + 4824803 * 2 ^ 59
def prefixEnd_4824803 : Nat := 4983230072969 + 3 ^ 40 * 4824803 * 2
def baseEnd_4824803 : Nat := 2477443002254791669773641

theorem tailTrace_4824803 : CollatzResearch.WordTrace tailWord_4824803 prefixEnd_4824803 2477443002254791669773641 := by
  unfold tailWord_4824803
  simp only [CollatzResearch.WordTrace]
  refine ⟨175975022339570216594663063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117316681559713477729775375 175975022339570216594663063)
  ·
    refine ⟨263962533509355324891994595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175975022339570216594663063 263962533509355324891994595)
    ·
      refine ⟨395943800264032987337991893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263962533509355324891994595 395943800264032987337991893)
      ·
        refine ⟨9279932818688273140734185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 395943800264032987337991893 9279932818688273140734185)
        ·
          refine ⟨6959949614016204855550639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9279932818688273140734185 6959949614016204855550639)
          ·
            refine ⟨10439924421024307283325959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6959949614016204855550639 10439924421024307283325959)
            ·
              refine ⟨15659886631536460924988939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10439924421024307283325959 15659886631536460924988939)
              ·
                refine ⟨23489829947304691387483409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15659886631536460924988939 23489829947304691387483409)
                ·
                  refine ⟨17617372460478518540612557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23489829947304691387483409 17617372460478518540612557)
                  ·
                    refine ⟨6606514672679444452729709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17617372460478518540612557 6606514672679444452729709)
                    ·
                      refine ⟨2477443002254791669773641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6606514672679444452729709 2477443002254791669773641)
                      ·
                        rfl

theorem cell23_4824803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4824803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824803 prefixEnd_4824803 := by exact prefixLift 4824803
  have htrace : WordTrace (prefixWord ++ tailWord_4824803) baseStart_4824803 baseEnd_4824803 := by
    simpa [prefixWord, tailWord_4824803, baseEnd_4824803] using wordTrace_append hprefix tailTrace_4824803
  have hstable : (prefixWord ++ tailWord_4824803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824803).length < 2 ^ (prefixWord ++ tailWord_4824803).sum := by decide
  have hdescent : baseEnd_4824803 < baseStart_4824803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824809 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_4824809 : Nat := 118140960795 + 4824809 * 2 ^ 59
def prefixEnd_4824809 : Nat := 4983230072969 + 3 ^ 40 * 4824809 * 2
def baseEnd_4824809 : Nat := 2477446083138718646298613

theorem tailTrace_4824809 : CollatzResearch.WordTrace tailWord_4824809 prefixEnd_4824809 2477446083138718646298613 := by
  unfold tailWord_4824809
  simp only [CollatzResearch.WordTrace]
  refine ⟨175975241177548479619381481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117316827451698986412920987 175975241177548479619381481)
  ·
    refine ⟨131981430883161359714536111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175975241177548479619381481 131981430883161359714536111)
    ·
      refine ⟨197972146324742039571804167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131981430883161359714536111 197972146324742039571804167)
      ·
        refine ⟨296958219487113059357706251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197972146324742039571804167 296958219487113059357706251)
        ·
          refine ⟨445437329230669589036559377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296958219487113059357706251 445437329230669589036559377)
          ·
            refine ⟨334077996923002191777419533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445437329230669589036559377 334077996923002191777419533)
            ·
              refine ⟨125279248846125821916532325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334077996923002191777419533 125279248846125821916532325)
              ·
                refine ⟨23489859158648591609349811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125279248846125821916532325 23489859158648591609349811)
                ·
                  refine ⟨35234788737972887414024717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23489859158648591609349811 35234788737972887414024717)
                  ·
                    refine ⟨13213045776739832780259269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35234788737972887414024717 13213045776739832780259269)
                    ·
                      refine ⟨2477446083138718646298613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13213045776739832780259269 2477446083138718646298613)
                      ·
                        rfl

theorem cell23_4824809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_4824809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824809 prefixEnd_4824809 := by exact prefixLift 4824809
  have htrace : WordTrace (prefixWord ++ tailWord_4824809) baseStart_4824809 baseEnd_4824809 := by
    simpa [prefixWord, tailWord_4824809, baseEnd_4824809] using wordTrace_append hprefix tailTrace_4824809
  have hstable : (prefixWord ++ tailWord_4824809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824809).length < 2 ^ (prefixWord ++ tailWord_4824809).sum := by decide
  have hdescent : baseEnd_4824809 < baseStart_4824809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824826 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2]
def baseStart_4824826 : Nat := 118140960795 + 4824826 * 2 ^ 59
def prefixEnd_4824826 : Nat := 4983230072969 + 3 ^ 40 * 4824826 * 2
def baseEnd_4824826 : Nat := 2477454812309845079786035

theorem tailTrace_4824826 : CollatzResearch.WordTrace tailWord_4824826 prefixEnd_4824826 2477454812309845079786035 := by
  unfold tailWord_4824826
  simp only [CollatzResearch.WordTrace]
  refine ⟨43993965304621722880687583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117317240812324594348500221 43993965304621722880687583)
  ·
    refine ⟨65990947956932584321031375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43993965304621722880687583 65990947956932584321031375)
    ·
      refine ⟨98986421935398876481547063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65990947956932584321031375 98986421935398876481547063)
      ·
        refine ⟨148479632903098314722320595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98986421935398876481547063 148479632903098314722320595)
        ·
          refine ⟨222719449354647472083480893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148479632903098314722320595 222719449354647472083480893)
          ·
            refine ⟨83519793507992802031305335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222719449354647472083480893 83519793507992802031305335)
            ·
              refine ⟨125279690261989203046958003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83519793507992802031305335 125279690261989203046958003)
              ·
                refine ⟨187919535392983804570437005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125279690261989203046958003 187919535392983804570437005)
                ·
                  refine ⟨70469825772368926713913877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187919535392983804570437005 70469825772368926713913877)
                  ·
                    refine ⟨3303273083079793439714713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70469825772368926713913877 3303273083079793439714713)
                    ·
                      refine ⟨2477454812309845079786035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303273083079793439714713 2477454812309845079786035)
                      ·
                        rfl

theorem cell23_4824826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_4824826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824826 prefixEnd_4824826 := by exact prefixLift 4824826
  have htrace : WordTrace (prefixWord ++ tailWord_4824826) baseStart_4824826 baseEnd_4824826 := by
    simpa [prefixWord, tailWord_4824826, baseEnd_4824826] using wordTrace_append hprefix tailTrace_4824826
  have hstable : (prefixWord ++ tailWord_4824826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824826).length < 2 ^ (prefixWord ++ tailWord_4824826).sum := by decide
  have hdescent : baseEnd_4824826 < baseStart_4824826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824829 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4824829 : Nat := 118140960795 + 4824829 * 2 ^ 59
def prefixEnd_4824829 : Nat := 4983230072969 + 3 ^ 40 * 4824829 * 2
def baseEnd_4824829 : Nat := 2477456352751808568048521

theorem tailTrace_4824829 : CollatzResearch.WordTrace tailWord_4824829 prefixEnd_4824829 2477456352751808568048521 := by
  unfold tailWord_4824829
  simp only [CollatzResearch.WordTrace]
  refine ⟨175975970637476023035109541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117317313758317348690073027 175975970637476023035109541)
  ·
    refine ⟨32995494494526754319083039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 175975970637476023035109541 32995494494526754319083039)
    ·
      refine ⟨49493241741790131478624559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32995494494526754319083039 49493241741790131478624559)
      ·
        refine ⟨74239862612685197217936839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49493241741790131478624559 74239862612685197217936839)
        ·
          refine ⟨111359793919027795826905259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74239862612685197217936839 111359793919027795826905259)
          ·
            refine ⟨167039690878541693740357889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111359793919027795826905259 167039690878541693740357889)
            ·
              refine ⟨125279768158906270305268417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167039690878541693740357889 125279768158906270305268417)
              ·
                refine ⟨93959826119179702728951313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125279768158906270305268417 93959826119179702728951313)
                ·
                  refine ⟨70469869589384777046713485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93959826119179702728951313 70469869589384777046713485)
                  ·
                    refine ⟨26426201096019291392517557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70469869589384777046713485 26426201096019291392517557)
                    ·
                      refine ⟨2477456352751808568048521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26426201096019291392517557 2477456352751808568048521)
                      ·
                        rfl

theorem cell23_4824829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4824829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824829 prefixEnd_4824829 := by exact prefixLift 4824829
  have htrace : WordTrace (prefixWord ++ tailWord_4824829) baseStart_4824829 baseEnd_4824829 := by
    simpa [prefixWord, tailWord_4824829, baseEnd_4824829] using wordTrace_append hprefix tailTrace_4824829
  have hstable : (prefixWord ++ tailWord_4824829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824829).length < 2 ^ (prefixWord ++ tailWord_4824829).sum := by decide
  have hdescent : baseEnd_4824829 < baseStart_4824829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824838 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4824838 : Nat := 118140960795 + 4824838 * 2 ^ 59
def prefixEnd_4824838 : Nat := 4983230072969 + 3 ^ 40 * 4824838 * 2
def baseEnd_4824838 : Nat := 2477460974077699032835981

theorem tailTrace_4824838 : CollatzResearch.WordTrace tailWord_4824838 prefixEnd_4824838 2477460974077699032835981 := by
  unfold tailWord_4824838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499259340451356799130849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117317532596295611714791445 5499259340451356799130849)
  ·
    refine ⟨4124444505338517599348137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5499259340451356799130849 4124444505338517599348137)
    ·
      refine ⟨3093333379003888199511103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4124444505338517599348137 3093333379003888199511103)
      ·
        refine ⟨4640000068505832299266655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093333379003888199511103 4640000068505832299266655)
        ·
          refine ⟨6960000102758748448899983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4640000068505832299266655 6960000102758748448899983)
          ·
            refine ⟨10440000154138122673349975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6960000102758748448899983 10440000154138122673349975)
            ·
              refine ⟨15660000231207184010024963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10440000154138122673349975 15660000231207184010024963)
              ·
                refine ⟨23490000346810776015037445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15660000231207184010024963 23490000346810776015037445)
                ·
                  refine ⟨4404375065027020502819521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23490000346810776015037445 4404375065027020502819521)
                  ·
                    refine ⟨3303281298770265377114641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4404375065027020502819521 3303281298770265377114641)
                    ·
                      refine ⟨2477460974077699032835981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303281298770265377114641 2477460974077699032835981)
                      ·
                        rfl

theorem cell23_4824838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4824838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824838 prefixEnd_4824838 := by exact prefixLift 4824838
  have htrace : WordTrace (prefixWord ++ tailWord_4824838) baseStart_4824838 baseEnd_4824838 := by
    simpa [prefixWord, tailWord_4824838, baseEnd_4824838] using wordTrace_append hprefix tailTrace_4824838
  have hstable : (prefixWord ++ tailWord_4824838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824838).length < 2 ^ (prefixWord ++ tailWord_4824838).sum := by decide
  have hdescent : baseEnd_4824838 < baseStart_4824838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824853 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_4824853 : Nat := 118140960795 + 4824853 * 2 ^ 59
def prefixEnd_4824853 : Nat := 4983230072969 + 3 ^ 40 * 4824853 * 2
def baseEnd_4824853 : Nat := 825822892095838824716137

theorem tailTrace_4824853 : CollatzResearch.WordTrace tailWord_4824853 prefixEnd_4824853 825822892095838824716137 := by
  unfold tailWord_4824853
  simp only [CollatzResearch.WordTrace]
  refine ⟨175976845989389075133983213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117317897326259383422655475 175976845989389075133983213)
  ·
    refine ⟨65991317246020903175243705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175976845989389075133983213 65991317246020903175243705)
    ·
      refine ⟨49493487934515677381432779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65991317246020903175243705 49493487934515677381432779)
      ·
        refine ⟨74240231901773516072149169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49493487934515677381432779 74240231901773516072149169)
        ·
          refine ⟨55680173926330137054111877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74240231901773516072149169 55680173926330137054111877)
          ·
            refine ⟨10440032611186900697645977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55680173926330137054111877 10440032611186900697645977)
            ·
              refine ⟨7830024458390175523234483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10440032611186900697645977 7830024458390175523234483)
              ·
                refine ⟨11745036687585263284851725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830024458390175523234483 11745036687585263284851725)
                ·
                  refine ⟨4404388757844473731819397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11745036687585263284851725 4404388757844473731819397)
                  ·
                    refine ⟨825822892095838824716137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4404388757844473731819397 825822892095838824716137)
                    ·
                      rfl

theorem cell23_4824853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_4824853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824853 prefixEnd_4824853 := by exact prefixLift 4824853
  have htrace : WordTrace (prefixWord ++ tailWord_4824853) baseStart_4824853 baseEnd_4824853 := by
    simpa [prefixWord, tailWord_4824853, baseEnd_4824853] using wordTrace_append hprefix tailTrace_4824853
  have hstable : (prefixWord ++ tailWord_4824853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824853).length < 2 ^ (prefixWord ++ tailWord_4824853).sum := by decide
  have hdescent : baseEnd_4824853 < baseStart_4824853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824903 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_4824903 : Nat := 118140960795 + 4824903 * 2 ^ 59
def prefixEnd_4824903 : Nat := 4983230072969 + 3 ^ 40 * 4824903 * 2
def baseEnd_4824903 : Nat := 2477494350320241278523181

theorem tailTrace_4824903 : CollatzResearch.WordTrace tailWord_4824903 prefixEnd_4824903 2477494350320241278523181 := by
  unfold tailWord_4824903
  simp only [CollatzResearch.WordTrace]
  refine ⟨175978669639207933673303363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117319113092805289115535575 175978669639207933673303363)
  ·
    refine ⟨263968004458811900509955045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175978669639207933673303363 263968004458811900509955045)
    ·
      refine ⟨49494000836027231345616571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 263968004458811900509955045 49494000836027231345616571)
      ·
        refine ⟨74241001254040847018424857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49494000836027231345616571 74241001254040847018424857)
        ·
          refine ⟨55680750940530635263818643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74241001254040847018424857 55680750940530635263818643)
          ·
            refine ⟨83521126410795952895727965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55680750940530635263818643 83521126410795952895727965)
            ·
              refine ⟨31320422404048482335897987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83521126410795952895727965 31320422404048482335897987)
              ·
                refine ⟨46980633606072723503846981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31320422404048482335897987 46980633606072723503846981)
                ·
                  refine ⟨8808868801138635656971309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46980633606072723503846981 8808868801138635656971309)
                  ·
                    refine ⟨3303325800426988371364241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8808868801138635656971309 3303325800426988371364241)
                    ·
                      refine ⟨2477494350320241278523181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303325800426988371364241 2477494350320241278523181)
                      ·
                        rfl

theorem cell23_4824903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_4824903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824903 prefixEnd_4824903 := by exact prefixLift 4824903
  have htrace : WordTrace (prefixWord ++ tailWord_4824903) baseStart_4824903 baseEnd_4824903 := by
    simpa [prefixWord, tailWord_4824903, baseEnd_4824903] using wordTrace_append hprefix tailTrace_4824903
  have hstable : (prefixWord ++ tailWord_4824903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824903).length < 2 ^ (prefixWord ++ tailWord_4824903).sum := by decide
  have hdescent : baseEnd_4824903 < baseStart_4824903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824930 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_4824930 : Nat := 118140960795 + 4824930 * 2 ^ 59
def prefixEnd_4824930 : Nat := 4983230072969 + 3 ^ 40 * 4824930 * 2
def baseEnd_4824930 : Nat := 825836071432637557628519

theorem tailTrace_4824930 : CollatzResearch.WordTrace tailWord_4824930 prefixEnd_4824930 825836071432637557628519 := by
  unfold tailWord_4824930
  simp only [CollatzResearch.WordTrace]
  refine ⟨43994913602527529321134061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117319769606740078189690829 43994913602527529321134061)
  ·
    refine ⟨16498092600947823495425273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43994913602527529321134061 16498092600947823495425273)
    ·
      refine ⟨12373569450710867621568955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16498092600947823495425273 12373569450710867621568955)
      ·
        refine ⟨18560354176066301432353433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12373569450710867621568955 18560354176066301432353433)
        ·
          refine ⟨13920265632049726074265075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18560354176066301432353433 13920265632049726074265075)
          ·
            refine ⟨20880398448074589111397613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13920265632049726074265075 20880398448074589111397613)
            ·
              refine ⟨7830149418027970916774105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20880398448074589111397613 7830149418027970916774105)
              ·
                refine ⟨5872612063520978187580579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7830149418027970916774105 5872612063520978187580579)
                ·
                  refine ⟨8808918095281467281370869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5872612063520978187580579 8808918095281467281370869)
                  ·
                    refine ⟨825836071432637557628519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8808918095281467281370869 825836071432637557628519)
                    ·
                      rfl

theorem cell23_4824930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_4824930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824930 prefixEnd_4824930 := by exact prefixLift 4824930
  have htrace : WordTrace (prefixWord ++ tailWord_4824930) baseStart_4824930 baseEnd_4824930 := by
    simpa [prefixWord, tailWord_4824930, baseEnd_4824930] using wordTrace_append hprefix tailTrace_4824930
  have hstable : (prefixWord ++ tailWord_4824930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824930).length < 2 ^ (prefixWord ++ tailWord_4824930).sum := by decide
  have hdescent : baseEnd_4824930 < baseStart_4824930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824980 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4824980 : Nat := 118140960795 + 4824980 * 2 ^ 59
def prefixEnd_4824980 : Nat := 4983230072969 + 3 ^ 40 * 4824980 * 2
def baseEnd_4824980 : Nat := 2477533888330637477260327

theorem tailTrace_4824980 : CollatzResearch.WordTrace tailWord_4824980 prefixEnd_4824980 2477533888330637477260327 := by
  unfold tailWord_4824980
  simp only [CollatzResearch.WordTrace]
  refine ⟨87990739029964487911928197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117320985373285983882570929 87990739029964487911928197)
  ·
    refine ⟨16498263568118341483486537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87990739029964487911928197 16498263568118341483486537)
    ·
      refine ⟨12373697676088756112614903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16498263568118341483486537 12373697676088756112614903)
      ·
        refine ⟨18560546514133134168922355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12373697676088756112614903 18560546514133134168922355)
        ·
          refine ⟨27840819771199701253383533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18560546514133134168922355 27840819771199701253383533)
          ·
            refine ⟨10440307414199887970018825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27840819771199701253383533 10440307414199887970018825)
            ·
              refine ⟨7830230560649915977514119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10440307414199887970018825 7830230560649915977514119)
              ·
                refine ⟨11745345840974873966271179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830230560649915977514119 11745345840974873966271179)
                ·
                  refine ⟨17618018761462310949406769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11745345840974873966271179 17618018761462310949406769)
                  ·
                    refine ⟨13213514071096733212055077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17618018761462310949406769 13213514071096733212055077)
                    ·
                      refine ⟨2477533888330637477260327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13213514071096733212055077 2477533888330637477260327)
                      ·
                        rfl

theorem cell23_4824980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4824980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824980 prefixEnd_4824980 := by exact prefixLift 4824980
  have htrace : WordTrace (prefixWord ++ tailWord_4824980) baseStart_4824980 baseEnd_4824980 := by
    simpa [prefixWord, tailWord_4824980, baseEnd_4824980] using wordTrace_append hprefix tailTrace_4824980
  have hstable : (prefixWord ++ tailWord_4824980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824980).length < 2 ^ (prefixWord ++ tailWord_4824980).sum := by decide
  have hdescent : baseEnd_4824980 < baseStart_4824980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824983 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4824983 : Nat := 118140960795 + 4824983 * 2 ^ 59
def prefixEnd_4824983 : Nat := 4983230072969 + 3 ^ 40 * 4824983 * 2
def baseEnd_4824983 : Nat := 2477535428772600965522813

theorem tailTrace_4824983 : CollatzResearch.WordTrace tailWord_4824983 prefixEnd_4824983 2477535428772600965522813 := by
  unfold tailWord_4824983
  simp only [CollatzResearch.WordTrace]
  refine ⟨175981587478918107336215603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117321058319278738224143735 175981587478918107336215603)
  ·
    refine ⟨263972381218377161004323405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175981587478918107336215603 263972381218377161004323405)
    ·
      refine ⟨98989642956891435376621277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263972381218377161004323405 98989642956891435376621277)
      ·
        refine ⟨37121116108834288266232979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98989642956891435376621277 37121116108834288266232979)
        ·
          refine ⟨55681674163251432399349469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37121116108834288266232979 55681674163251432399349469)
          ·
            refine ⟨20880627811219287149756051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55681674163251432399349469 20880627811219287149756051)
            ·
              refine ⟨31320941716828930724634077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20880627811219287149756051 31320941716828930724634077)
              ·
                refine ⟨11745353143810849021737779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31320941716828930724634077 11745353143810849021737779)
                ·
                  refine ⟨17618029715716273532606669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11745353143810849021737779 17618029715716273532606669)
                  ·
                    refine ⟨6606761143393602574727501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17618029715716273532606669 6606761143393602574727501)
                    ·
                      refine ⟨2477535428772600965522813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6606761143393602574727501 2477535428772600965522813)
                      ·
                        rfl

theorem cell23_4824983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4824983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824983 prefixEnd_4824983 := by exact prefixLift 4824983
  have htrace : WordTrace (prefixWord ++ tailWord_4824983) baseStart_4824983 baseEnd_4824983 := by
    simpa [prefixWord, tailWord_4824983, baseEnd_4824983] using wordTrace_append hprefix tailTrace_4824983
  have hstable : (prefixWord ++ tailWord_4824983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824983).length < 2 ^ (prefixWord ++ tailWord_4824983).sum := by decide
  have hdescent : baseEnd_4824983 < baseStart_4824983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4824984 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4824984 : Nat := 118140960795 + 4824984 * 2 ^ 59
def prefixEnd_4824984 : Nat := 4983230072969 + 3 ^ 40 * 4824984 * 2
def baseEnd_4824984 : Nat := 2477535942253255461610309

theorem tailTrace_4824984 : CollatzResearch.WordTrace tailWord_4824984 prefixEnd_4824984 2477535942253255461610309 := by
  unfold tailWord_4824984
  simp only [CollatzResearch.WordTrace]
  refine ⟨87990811975957242253501003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117321082634609656338001337 87990811975957242253501003)
  ·
    refine ⟨131986217963935863380251505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87990811975957242253501003 131986217963935863380251505)
    ·
      refine ⟨98989663472951897535188629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131986217963935863380251505 98989663472951897535188629)
      ·
        refine ⟨4640140475294620196961967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98989663472951897535188629 4640140475294620196961967)
        ·
          refine ⟨6960210712941930295442951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4640140475294620196961967 6960210712941930295442951)
          ·
            refine ⟨10440316069412895443164427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6960210712941930295442951 10440316069412895443164427)
            ·
              refine ⟨15660474104119343164746641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10440316069412895443164427 15660474104119343164746641)
              ·
                refine ⟨11745355578089507373559981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15660474104119343164746641 11745355578089507373559981)
                ·
                  refine ⟨4404508341783565265084993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11745355578089507373559981 4404508341783565265084993)
                  ·
                    refine ⟨3303381256337673948813745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4404508341783565265084993 3303381256337673948813745)
                    ·
                      refine ⟨2477535942253255461610309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303381256337673948813745 2477535942253255461610309)
                      ·
                        rfl

theorem cell23_4824984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4824984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4824984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4824984 prefixEnd_4824984 := by exact prefixLift 4824984
  have htrace : WordTrace (prefixWord ++ tailWord_4824984) baseStart_4824984 baseEnd_4824984 := by
    simpa [prefixWord, tailWord_4824984, baseEnd_4824984] using wordTrace_append hprefix tailTrace_4824984
  have hstable : (prefixWord ++ tailWord_4824984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4824984).length < 2 ^ (prefixWord ++ tailWord_4824984).sum := by decide
  have hdescent : baseEnd_4824984 < baseStart_4824984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4824984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825016 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 4, 6]
def baseStart_4825016 : Nat := 118140960795 + 4825016 * 2 ^ 59
def prefixEnd_4825016 : Nat := 4983230072969 + 3 ^ 40 * 4825016 * 2
def baseEnd_4825016 : Nat := 825850791211399778803387

theorem tailTrace_4825016 : CollatzResearch.WordTrace tailWord_4825016 prefixEnd_4825016 825850791211399778803387 := by
  unfold tailWord_4825016
  simp only [CollatzResearch.WordTrace]
  refine ⟨87991395543899276986083451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117321860725199035981444601 87991395543899276986083451)
  ·
    refine ⟨131987093315848915479125177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87991395543899276986083451 131987093315848915479125177)
    ·
      refine ⟨98990319986886686609343883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131987093315848915479125177 98990319986886686609343883)
      ·
        refine ⟨148485479980330029914015825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98990319986886686609343883 148485479980330029914015825)
        ·
          refine ⟨111364109985247522435511869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148485479980330029914015825 111364109985247522435511869)
          ·
            refine ⟨41761541244467820913316951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111364109985247522435511869 41761541244467820913316951)
            ·
              refine ⟨62642311866701731369975427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41761541244467820913316951 62642311866701731369975427)
              ·
                refine ⟨93963467800052597054963141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62642311866701731369975427 93963467800052597054963141)
                ·
                  refine ⟨17618150212509861947805589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93963467800052597054963141 17618150212509861947805589)
                  ·
                    refine ⟨825850791211399778803387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17618150212509861947805589 825850791211399778803387)
                    ·
                      rfl

theorem cell23_4825016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_4825016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825016 prefixEnd_4825016 := by exact prefixLift 4825016
  have htrace : WordTrace (prefixWord ++ tailWord_4825016) baseStart_4825016 baseEnd_4825016 := by
    simpa [prefixWord, tailWord_4825016, baseEnd_4825016] using wordTrace_append hprefix tailTrace_4825016
  have hstable : (prefixWord ++ tailWord_4825016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825016).length < 2 ^ (prefixWord ++ tailWord_4825016).sum := by decide
  have hdescent : baseEnd_4825016 < baseStart_4825016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825040 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 1, 4, 2]
def baseStart_4825040 : Nat := 118140960795 + 4825040 * 2 ^ 59
def prefixEnd_4825040 : Nat := 4983230072969 + 3 ^ 40 * 4825040 * 2
def baseEnd_4825040 : Nat := 2477564697169907242510051

theorem tailTrace_4825040 : CollatzResearch.WordTrace tailWord_4825040 prefixEnd_4825040 2477564697169907242510051 := by
  unfold tailWord_4825040
  simp only [CollatzResearch.WordTrace]
  refine ⟨87991833219855803035520287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117322444293141070714027049 87991833219855803035520287)
  ·
    refine ⟨131987749829783704553280431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87991833219855803035520287 131987749829783704553280431)
    ·
      refine ⟨197981624744675556829920647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131987749829783704553280431 197981624744675556829920647)
      ·
        refine ⟨296972437117013335244880971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197981624744675556829920647 296972437117013335244880971)
        ·
          refine ⟨445458655675520002867321457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296972437117013335244880971 445458655675520002867321457)
          ·
            refine ⟨334093991756640002150491093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445458655675520002867321457 334093991756640002150491093)
            ·
              refine ⟨7830327931796250050402135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 334093991756640002150491093 7830327931796250050402135)
              ·
                refine ⟨11745491897694375075603203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830327931796250050402135 11745491897694375075603203)
                ·
                  refine ⟨17618237846541562613404805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11745491897694375075603203 17618237846541562613404805)
                  ·
                    refine ⟨3303419596226542990013401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17618237846541562613404805 3303419596226542990013401)
                    ·
                      refine ⟨2477564697169907242510051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303419596226542990013401 2477564697169907242510051)
                      ·
                        rfl

theorem cell23_4825040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 4, 2].length) (baseStart_4825040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825040 prefixEnd_4825040 := by exact prefixLift 4825040
  have htrace : WordTrace (prefixWord ++ tailWord_4825040) baseStart_4825040 baseEnd_4825040 := by
    simpa [prefixWord, tailWord_4825040, baseEnd_4825040] using wordTrace_append hprefix tailTrace_4825040
  have hstable : (prefixWord ++ tailWord_4825040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825040).length < 2 ^ (prefixWord ++ tailWord_4825040).sum := by decide
  have hdescent : baseEnd_4825040 < baseStart_4825040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825052 : List Nat := [2, 2, 6, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_4825052 : Nat := 118140960795 + 4825052 * 2 ^ 59
def prefixEnd_4825052 : Nat := 4983230072969 + 3 ^ 40 * 4825052 * 2
def baseEnd_4825052 : Nat := 2477570858937761195559997

theorem tailTrace_4825052 : CollatzResearch.WordTrace tailWord_4825052 prefixEnd_4825052 2477570858937761195559997 := by
  unfold tailWord_4825052
  simp only [CollatzResearch.WordTrace]
  refine ⟨87992052057834066060238705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117322736077112088080318273 87992052057834066060238705)
  ·
    refine ⟨65994039043375549545179029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87992052057834066060238705 65994039043375549545179029)
    ·
      refine ⟨3093470580158228884930267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65994039043375549545179029 3093470580158228884930267)
      ·
        refine ⟨4640205870237343327395401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093470580158228884930267 4640205870237343327395401)
        ·
          refine ⟨3480154402678007495546551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4640205870237343327395401 3480154402678007495546551)
          ·
            refine ⟨5220231604017011243319827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480154402678007495546551 5220231604017011243319827)
            ·
              refine ⟨7830347406025516864979741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220231604017011243319827 7830347406025516864979741)
              ·
                refine ⟨2936380277259568824367403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830347406025516864979741 2936380277259568824367403)
                ·
                  refine ⟨4404570415889353236551105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936380277259568824367403 4404570415889353236551105)
                  ·
                    refine ⟨3303427811917014927413329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4404570415889353236551105 3303427811917014927413329)
                    ·
                      refine ⟨2477570858937761195559997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303427811917014927413329 2477570858937761195559997)
                      ·
                        rfl

theorem cell23_4825052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_4825052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825052 prefixEnd_4825052 := by exact prefixLift 4825052
  have htrace : WordTrace (prefixWord ++ tailWord_4825052) baseStart_4825052 baseEnd_4825052 := by
    simpa [prefixWord, tailWord_4825052, baseEnd_4825052] using wordTrace_append hprefix tailTrace_4825052
  have hstable : (prefixWord ++ tailWord_4825052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825052).length < 2 ^ (prefixWord ++ tailWord_4825052).sum := by decide
  have hdescent : baseEnd_4825052 < baseStart_4825052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825163 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 3]
def baseStart_4825163 : Nat := 118140960795 + 4825163 * 2 ^ 59
def prefixEnd_4825163 : Nat := 4983230072969 + 3 ^ 40 * 4825163 * 2
def baseEnd_4825163 : Nat := 2477627855290410261271985

theorem tailTrace_4825163 : CollatzResearch.WordTrace tailWord_4825163 prefixEnd_4825163 2477627855290410261271985 := by
  unfold tailWord_4825163
  simp only [CollatzResearch.WordTrace]
  refine ⟨175988152618265998077768143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117325435078843998718512095 175988152618265998077768143)
  ·
    refine ⟨263982228927398997116652215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175988152618265998077768143 263982228927398997116652215)
    ·
      refine ⟨395973343391098495674978323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263982228927398997116652215 395973343391098495674978323)
      ·
        refine ⟨593960015086647743512467485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395973343391098495674978323 593960015086647743512467485)
        ·
          refine ⟨222735005657492903817175307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593960015086647743512467485 222735005657492903817175307)
          ·
            refine ⟨334102508486239355725762961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222735005657492903817175307 334102508486239355725762961)
            ·
              refine ⟨250576881364679516794322221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334102508486239355725762961 250576881364679516794322221)
              ·
                refine ⟨93966330511754818797870833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250576881364679516794322221 93966330511754818797870833)
                ·
                  refine ⟨70474747883816114098403125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93966330511754818797870833 70474747883816114098403125)
                  ·
                    refine ⟨6607007614107760696725293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70474747883816114098403125 6607007614107760696725293)
                    ·
                      refine ⟨2477627855290410261271985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607007614107760696725293 2477627855290410261271985)
                      ·
                        rfl

theorem cell23_4825163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 3].length) (baseStart_4825163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825163 prefixEnd_4825163 := by exact prefixLift 4825163
  have htrace : WordTrace (prefixWord ++ tailWord_4825163) baseStart_4825163 baseEnd_4825163 := by
    simpa [prefixWord, tailWord_4825163, baseEnd_4825163] using wordTrace_append hprefix tailTrace_4825163
  have hstable : (prefixWord ++ tailWord_4825163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825163).length < 2 ^ (prefixWord ++ tailWord_4825163).sum := by decide
  have hdescent : baseEnd_4825163 < baseStart_4825163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825183 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 5, 5]
def baseStart_4825183 : Nat := 118140960795 + 4825183 * 2 ^ 59
def prefixEnd_4825183 : Nat := 4983230072969 + 3 ^ 40 * 4825183 * 2
def baseEnd_4825183 : Nat := 825879374967833394340631

theorem tailTrace_4825183 : CollatzResearch.WordTrace tailWord_4825183 prefixEnd_4825183 825879374967833394340631 := by
  unfold tailWord_4825183
  simp only [CollatzResearch.WordTrace]
  refine ⟨175988882078193541493496203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117325921385462360995664135 175988882078193541493496203)
  ·
    refine ⟨263983323117290312240244305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175988882078193541493496203 263983323117290312240244305)
    ·
      refine ⟨197987492337967734180183229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263983323117290312240244305 197987492337967734180183229)
      ·
        refine ⟨74245309626737900317568711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197987492337967734180183229 74245309626737900317568711)
        ·
          refine ⟨111367964440106850476353067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74245309626737900317568711 111367964440106850476353067)
          ·
            refine ⟨167051946660160275714529601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111367964440106850476353067 167051946660160275714529601)
            ·
              refine ⟨125288959995120206785897201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167051946660160275714529601 125288959995120206785897201)
              ·
                refine ⟨93966719996340155089422901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125288959995120206785897201 93966719996340155089422901)
                ·
                  refine ⟨8809379999656889539633397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93966719996340155089422901 8809379999656889539633397)
                  ·
                    refine ⟨825879374967833394340631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8809379999656889539633397 825879374967833394340631)
                    ·
                      rfl

theorem cell23_4825183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_4825183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825183 prefixEnd_4825183 := by exact prefixLift 4825183
  have htrace : WordTrace (prefixWord ++ tailWord_4825183) baseStart_4825183 baseEnd_4825183 := by
    simpa [prefixWord, tailWord_4825183, baseEnd_4825183] using wordTrace_append hprefix tailTrace_4825183
  have hstable : (prefixWord ++ tailWord_4825183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825183).length < 2 ^ (prefixWord ++ tailWord_4825183).sum := by decide
  have hdescent : baseEnd_4825183 < baseStart_4825183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825247 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 4, 4]
def baseStart_4825247 : Nat := 118140960795 + 4825247 * 2 ^ 59
def prefixEnd_4825247 : Nat := 4983230072969 + 3 ^ 40 * 4825247 * 2
def baseEnd_4825247 : Nat := 825890329221795977540533

theorem tailTrace_4825247 : CollatzResearch.WordTrace tailWord_4825247 prefixEnd_4825247 825890329221795977540533 := by
  unfold tailWord_4825247
  simp only [CollatzResearch.WordTrace]
  refine ⟨175991216349961680423825995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117327477566641120282550663 175991216349961680423825995)
  ·
    refine ⟨263986824524942520635738993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175991216349961680423825995 263986824524942520635738993)
    ·
      refine ⟨197990118393706890476804245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263986824524942520635738993 197990118393706890476804245)
      ·
        refine ⟨9280786799705010491100199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197990118393706890476804245 9280786799705010491100199)
        ·
          refine ⟨13921180199557515736650299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9280786799705010491100199 13921180199557515736650299)
          ·
            refine ⟨20881770299336273604975449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13921180199557515736650299 20881770299336273604975449)
            ·
              refine ⟨15661327724502205203731587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20881770299336273604975449 15661327724502205203731587)
              ·
                refine ⟨23491991586753307805597381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15661327724502205203731587 23491991586753307805597381)
                ·
                  refine ⟨4404748422516245213549509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23491991586753307805597381 4404748422516245213549509)
                  ·
                    refine ⟨825890329221795977540533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4404748422516245213549509 825890329221795977540533)
                    ·
                      rfl

theorem cell23_4825247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_4825247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825247 prefixEnd_4825247 := by exact prefixLift 4825247
  have htrace : WordTrace (prefixWord ++ tailWord_4825247) baseStart_4825247 baseEnd_4825247 := by
    simpa [prefixWord, tailWord_4825247, baseEnd_4825247] using wordTrace_append hprefix tailTrace_4825247
  have hstable : (prefixWord ++ tailWord_4825247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825247).length < 2 ^ (prefixWord ++ tailWord_4825247).sum := by decide
  have hdescent : baseEnd_4825247 < baseStart_4825247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825263 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_4825263 : Nat := 118140960795 + 4825263 * 2 ^ 59
def prefixEnd_4825263 : Nat := 4983230072969 + 3 ^ 40 * 4825263 * 2
def baseEnd_4825263 : Nat := 2477679203355859870021525

theorem tailTrace_4825263 : CollatzResearch.WordTrace tailWord_4825263 prefixEnd_4825263 2477679203355859870021525 := by
  unfold tailWord_4825263
  simp only [CollatzResearch.WordTrace]
  refine ⟨175991799917903715156408443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117327866611935810104272295 175991799917903715156408443)
  ·
    refine ⟨263987699876855572734612665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175991799917903715156408443 263987699876855572734612665)
    ·
      refine ⟨197990774907641679550959499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263987699876855572734612665 197990774907641679550959499)
      ·
        refine ⟨296986162361462519326439249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197990774907641679550959499 296986162361462519326439249)
        ·
          refine ⟨222739621771096889494829437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296986162361462519326439249 222739621771096889494829437)
          ·
            refine ⟨83527358164161333560561039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222739621771096889494829437 83527358164161333560561039)
            ·
              refine ⟨125291037246242000340841559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83527358164161333560561039 125291037246242000340841559)
              ·
                refine ⟨187936555869363000511262339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125291037246242000340841559 187936555869363000511262339)
                ·
                  refine ⟨281904833804044500766893509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187936555869363000511262339 281904833804044500766893509)
                  ·
                    refine ⟨52857156338258343893792533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281904833804044500766893509 52857156338258343893792533)
                    ·
                      refine ⟨2477679203355859870021525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52857156338258343893792533 2477679203355859870021525)
                      ·
                        rfl

theorem cell23_4825263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_4825263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825263 prefixEnd_4825263 := by exact prefixLift 4825263
  have htrace : WordTrace (prefixWord ++ tailWord_4825263) baseStart_4825263 baseEnd_4825263 := by
    simpa [prefixWord, tailWord_4825263, baseEnd_4825263] using wordTrace_append hprefix tailTrace_4825263
  have hstable : (prefixWord ++ tailWord_4825263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825263).length < 2 ^ (prefixWord ++ tailWord_4825263).sum := by decide
  have hdescent : baseEnd_4825263 < baseStart_4825263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825283 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_4825283 : Nat := 118140960795 + 4825283 * 2 ^ 59
def prefixEnd_4825283 : Nat := 4983230072969 + 3 ^ 40 * 4825283 * 2
def baseEnd_4825283 : Nat := 2477689472968949791771433

theorem tailTrace_4825283 : CollatzResearch.WordTrace tailWord_4825283 prefixEnd_4825283 2477689472968949791771433 := by
  unfold tailWord_4825283
  simp only [CollatzResearch.WordTrace]
  refine ⟨175992529377831258572136503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117328352918554172381424335 175992529377831258572136503)
  ·
    refine ⟨263988794066746887858204755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175992529377831258572136503 263988794066746887858204755)
    ·
      refine ⟨395983191100120331787307133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263988794066746887858204755 395983191100120331787307133)
      ·
        refine ⟨148493696662545124420240175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395983191100120331787307133 148493696662545124420240175)
        ·
          refine ⟨222740544993817686630360263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148493696662545124420240175 222740544993817686630360263)
          ·
            refine ⟨334110817490726529945540395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222740544993817686630360263 334110817490726529945540395)
            ·
              refine ⟨501166226236089794918310593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334110817490726529945540395 501166226236089794918310593)
              ·
                refine ⟨375874669677067346188732945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501166226236089794918310593 375874669677067346188732945)
                ·
                  refine ⟨281906002257800509641549709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375874669677067346188732945 281906002257800509641549709)
                  ·
                    refine ⟨105714750846675191115581141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281906002257800509641549709 105714750846675191115581141)
                    ·
                      refine ⟨2477689472968949791771433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 105714750846675191115581141 2477689472968949791771433)
                      ·
                        rfl

theorem cell23_4825283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_4825283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825283 prefixEnd_4825283 := by exact prefixLift 4825283
  have htrace : WordTrace (prefixWord ++ tailWord_4825283) baseStart_4825283 baseEnd_4825283 := by
    simpa [prefixWord, tailWord_4825283, baseEnd_4825283] using wordTrace_append hprefix tailTrace_4825283
  have hstable : (prefixWord ++ tailWord_4825283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825283).length < 2 ^ (prefixWord ++ tailWord_4825283).sum := by decide
  have hdescent : baseEnd_4825283 < baseStart_4825283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825304 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 2, 1, 3]
def baseStart_4825304 : Nat := 118140960795 + 4825304 * 2 ^ 59
def prefixEnd_4825304 : Nat := 4983230072969 + 3 ^ 40 * 4825304 * 2
def baseEnd_4825304 : Nat := 2477700256062694209608837

theorem tailTrace_4825304 : CollatzResearch.WordTrace tailWord_4825304 prefixEnd_4825304 2477700256062694209608837 := by
  unfold tailWord_4825304
  simp only [CollatzResearch.WordTrace]
  refine ⟨87996647655377589579325483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117328863540503452772433977 87996647655377589579325483)
  ·
    refine ⟨131994971483066384368988225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87996647655377589579325483 131994971483066384368988225)
    ·
      refine ⟨98996228612299788276741169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131994971483066384368988225 98996228612299788276741169)
      ·
        refine ⟨74247171459224841207555877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98996228612299788276741169 74247171459224841207555877)
        ·
          refine ⟨13921344648604657726416727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74247171459224841207555877 13921344648604657726416727)
          ·
            refine ⟨20882016972906986589625091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13921344648604657726416727 20882016972906986589625091)
            ·
              refine ⟨31323025459360479884437637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20882016972906986589625091 31323025459360479884437637)
              ·
                refine ⟨5873067273630089978332057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31323025459360479884437637 5873067273630089978332057)
                ·
                  refine ⟨4404800455222567483749043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873067273630089978332057 4404800455222567483749043)
                  ·
                    refine ⟨6607200682833851225623565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4404800455222567483749043 6607200682833851225623565)
                    ·
                      refine ⟨2477700256062694209608837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607200682833851225623565 2477700256062694209608837)
                      ·
                        rfl

theorem cell23_4825304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_4825304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825304 prefixEnd_4825304 := by exact prefixLift 4825304
  have htrace : WordTrace (prefixWord ++ tailWord_4825304) baseStart_4825304 baseEnd_4825304 := by
    simpa [prefixWord, tailWord_4825304, baseEnd_4825304] using wordTrace_append hprefix tailTrace_4825304
  have hstable : (prefixWord ++ tailWord_4825304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825304).length < 2 ^ (prefixWord ++ tailWord_4825304).sum := by decide
  have hdescent : baseEnd_4825304 < baseStart_4825304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825320 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4825320 : Nat := 118140960795 + 4825320 * 2 ^ 59
def prefixEnd_4825320 : Nat := 4983230072969 + 3 ^ 40 * 4825320 * 2
def baseEnd_4825320 : Nat := 825902823917722049002921

theorem tailTrace_4825320 : CollatzResearch.WordTrace tailWord_4825320 prefixEnd_4825320 825902823917722049002921 := by
  unfold tailWord_4825320
  simp only [CollatzResearch.WordTrace]
  refine ⟨87996939439348606945616707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117329252585798142594155609 87996939439348606945616707)
  ·
    refine ⟨131995409159022910418425061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87996939439348606945616707 131995409159022910418425061)
    ·
      refine ⟨24749139217316795703454699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131995409159022910418425061 24749139217316795703454699)
      ·
        refine ⟨37123708825975193555182049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24749139217316795703454699 37123708825975193555182049)
        ·
          refine ⟨27842781619481395166386537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37123708825975193555182049 27842781619481395166386537)
          ·
            refine ⟨20882086214611046374789903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27842781619481395166386537 20882086214611046374789903)
            ·
              refine ⟨31323129321916569562184855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20882086214611046374789903 31323129321916569562184855)
              ·
                refine ⟨46984693982874854343277283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31323129321916569562184855 46984693982874854343277283)
                ·
                  refine ⟨70477040974312281514915925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46984693982874854343277283 70477040974312281514915925)
                  ·
                    refine ⟨825902823917722049002921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70477040974312281514915925 825902823917722049002921)
                    ·
                      rfl

theorem cell23_4825320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4825320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825320 prefixEnd_4825320 := by exact prefixLift 4825320
  have htrace : WordTrace (prefixWord ++ tailWord_4825320) baseStart_4825320 baseEnd_4825320 := by
    simpa [prefixWord, tailWord_4825320, baseEnd_4825320] using wordTrace_append hprefix tailTrace_4825320
  have hstable : (prefixWord ++ tailWord_4825320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825320).length < 2 ^ (prefixWord ++ tailWord_4825320).sum := by decide
  have hdescent : baseEnd_4825320 < baseStart_4825320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825360 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_4825360 : Nat := 118140960795 + 4825360 * 2 ^ 59
def prefixEnd_4825360 : Nat := 4983230072969 + 3 ^ 40 * 4825360 * 2
def baseEnd_4825360 : Nat := 2477729010979345990508579

theorem tailTrace_4825360 : CollatzResearch.WordTrace tailWord_4825360 prefixEnd_4825360 2477729010979345990508579 := by
  unfold tailWord_4825360
  simp only [CollatzResearch.WordTrace]
  refine ⟨87997668899276150361344767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117330225199034867148459689 87997668899276150361344767)
  ·
    refine ⟨131996503348914225542017151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87997668899276150361344767 131996503348914225542017151)
    ·
      refine ⟨197994755023371338313025727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131996503348914225542017151 197994755023371338313025727)
      ·
        refine ⟨296992132535057007469538591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197994755023371338313025727 296992132535057007469538591)
        ·
          refine ⟨445488198802585511204307887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296992132535057007469538591 445488198802585511204307887)
          ·
            refine ⟨668232298203878266806461831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445488198802585511204307887 668232298203878266806461831)
            ·
              refine ⟨1002348447305817400209692747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668232298203878266806461831 1002348447305817400209692747)
              ·
                refine ⟨1503522670958726100314539121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002348447305817400209692747 1503522670958726100314539121)
                ·
                  refine ⟨1127642003219044575235904341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503522670958726100314539121 1127642003219044575235904341)
                  ·
                    refine ⟨6607277362611589308022877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1127642003219044575235904341 6607277362611589308022877)
                    ·
                      refine ⟨2477729010979345990508579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607277362611589308022877 2477729010979345990508579)
                      ·
                        rfl

theorem cell23_4825360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_4825360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825360 prefixEnd_4825360 := by exact prefixLift 4825360
  have htrace : WordTrace (prefixWord ++ tailWord_4825360) baseStart_4825360 baseEnd_4825360 := by
    simpa [prefixWord, tailWord_4825360, baseEnd_4825360] using wordTrace_append hprefix tailTrace_4825360
  have hstable : (prefixWord ++ tailWord_4825360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825360).length < 2 ^ (prefixWord ++ tailWord_4825360).sum := by decide
  have hdescent : baseEnd_4825360 < baseStart_4825360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825361 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 2, 2, 2]
def baseStart_4825361 : Nat := 118140960795 + 4825361 * 2 ^ 59
def prefixEnd_4825361 : Nat := 4983230072969 + 3 ^ 40 * 4825361 * 2
def baseEnd_4825361 : Nat := 2477729524460000486596075

theorem tailTrace_4825361 : CollatzResearch.WordTrace tailWord_4825361 prefixEnd_4825361 2477729524460000486596075 := by
  unfold tailWord_4825361
  simp only [CollatzResearch.WordTrace]
  refine ⟨175995374271548677893475937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117330249514365785262317291 175995374271548677893475937)
  ·
    refine ⟨131996530703661508420106953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175995374271548677893475937 131996530703661508420106953)
    ·
      refine ⟨98997398027746131315080215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131996530703661508420106953 98997398027746131315080215)
      ·
        refine ⟨148496097041619196972620323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98997398027746131315080215 148496097041619196972620323)
        ·
          refine ⟨222744145562428795458930485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148496097041619196972620323 222744145562428795458930485)
          ·
            refine ⟨20882263646477699574274733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222744145562428795458930485 20882263646477699574274733)
            ·
              refine ⟨7830848867429137340353025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20882263646477699574274733 7830848867429137340353025)
              ·
                refine ⟨5873136650571853005264769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7830848867429137340353025 5873136650571853005264769)
                ·
                  refine ⟨4404852487928889753948577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873136650571853005264769 4404852487928889753948577)
                  ·
                    refine ⟨3303639365946667315461433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4404852487928889753948577 3303639365946667315461433)
                    ·
                      refine ⟨2477729524460000486596075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303639365946667315461433 2477729524460000486596075)
                      ·
                        rfl

theorem cell23_4825361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_4825361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825361 prefixEnd_4825361 := by exact prefixLift 4825361
  have htrace : WordTrace (prefixWord ++ tailWord_4825361) baseStart_4825361 baseEnd_4825361 := by
    simpa [prefixWord, tailWord_4825361, baseEnd_4825361] using wordTrace_append hprefix tailTrace_4825361
  have hstable : (prefixWord ++ tailWord_4825361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825361).length < 2 ^ (prefixWord ++ tailWord_4825361).sum := by decide
  have hdescent : baseEnd_4825361 < baseStart_4825361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825367 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 7]
def baseStart_4825367 : Nat := 118140960795 + 4825367 * 2 ^ 59
def prefixEnd_4825367 : Nat := 4983230072969 + 3 ^ 40 * 4825367 * 2
def baseEnd_4825367 : Nat := 275303622815991940346783

theorem tailTrace_4825367 : CollatzResearch.WordTrace tailWord_4825367 prefixEnd_4825367 275303622815991940346783 := by
  unfold tailWord_4825367
  simp only [CollatzResearch.WordTrace]
  refine ⟨175995593109526940918194355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117330395406351293945462903 175995593109526940918194355)
  ·
    refine ⟨263993389664290411377291533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175995593109526940918194355 263993389664290411377291533)
    ·
      refine ⟨98997521124108904266484325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 263993389664290411377291533 98997521124108904266484325)
      ·
        refine ⟨18562035210770419549965811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98997521124108904266484325 18562035210770419549965811)
        ·
          refine ⟨27843052816155629324948717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562035210770419549965811 27843052816155629324948717)
          ·
            refine ⟨10441144806058360996855769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27843052816155629324948717 10441144806058360996855769)
            ·
              refine ⟨7830858604543770747641827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10441144806058360996855769 7830858604543770747641827)
              ·
                refine ⟨11746287906815656121462741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830858604543770747641827 11746287906815656121462741)
                ·
                  refine ⟨275303622815991940346783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11746287906815656121462741 275303622815991940346783)
                  ·
                    rfl

theorem cell23_4825367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 7].length) (baseStart_4825367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825367 prefixEnd_4825367 := by exact prefixLift 4825367
  have htrace : WordTrace (prefixWord ++ tailWord_4825367) baseStart_4825367 baseEnd_4825367 := by
    simpa [prefixWord, tailWord_4825367, baseEnd_4825367] using wordTrace_append hprefix tailTrace_4825367
  have hstable : (prefixWord ++ tailWord_4825367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825367).length < 2 ^ (prefixWord ++ tailWord_4825367).sum := by decide
  have hdescent : baseEnd_4825367 < baseStart_4825367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825377 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_4825377 : Nat := 118140960795 + 4825377 * 2 ^ 59
def prefixEnd_4825377 : Nat := 4983230072969 + 3 ^ 40 * 4825377 * 2
def baseEnd_4825377 : Nat := 2477737740150472423996001

theorem tailTrace_4825377 : CollatzResearch.WordTrace tailWord_4825377 prefixEnd_4825377 2477737740150472423996001 := by
  unfold tailWord_4825377
  simp only [CollatzResearch.WordTrace]
  refine ⟨175995957839490712626058385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117330638559660475084038923 175995957839490712626058385)
  ·
    refine ⟨131996968379618034469543789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175995957839490712626058385 131996968379618034469543789)
    ·
      refine ⟨49498863142356762926078921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131996968379618034469543789 49498863142356762926078921)
      ·
        refine ⟨37124147356767572194559191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49498863142356762926078921 37124147356767572194559191)
        ·
          refine ⟨55686221035151358291838787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37124147356767572194559191 55686221035151358291838787)
          ·
            refine ⟨83529331552727037437758181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55686221035151358291838787 83529331552727037437758181)
            ·
              refine ⟨15661749666136319519579659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83529331552727037437758181 15661749666136319519579659)
              ·
                refine ⟨23492624499204479279369489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15661749666136319519579659 23492624499204479279369489)
                ·
                  refine ⟨17619468374403359459527117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23492624499204479279369489 17619468374403359459527117)
                  ·
                    refine ⟨6607300640401259797322669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17619468374403359459527117 6607300640401259797322669)
                    ·
                      refine ⟨2477737740150472423996001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607300640401259797322669 2477737740150472423996001)
                      ·
                        rfl

theorem cell23_4825377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_4825377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825377 prefixEnd_4825377 := by exact prefixLift 4825377
  have htrace : WordTrace (prefixWord ++ tailWord_4825377) baseStart_4825377 baseEnd_4825377 := by
    simpa [prefixWord, tailWord_4825377, baseEnd_4825377] using wordTrace_append hprefix tailTrace_4825377
  have hstable : (prefixWord ++ tailWord_4825377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825377).length < 2 ^ (prefixWord ++ tailWord_4825377).sum := by decide
  have hdescent : baseEnd_4825377 < baseStart_4825377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825397 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_4825397 : Nat := 118140960795 + 4825397 * 2 ^ 59
def prefixEnd_4825397 : Nat := 4983230072969 + 3 ^ 40 * 4825397 * 2
def baseEnd_4825397 : Nat := 825916003254520781915303

theorem tailTrace_4825397 : CollatzResearch.WordTrace tailWord_4825397 prefixEnd_4825397 825916003254520781915303 := by
  unfold tailWord_4825397
  simp only [CollatzResearch.WordTrace]
  refine ⟨175996687299418256041786445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117331124866278837361190963 175996687299418256041786445)
  ·
    refine ⟨65998757737281846015669917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 175996687299418256041786445 65998757737281846015669917)
    ·
      refine ⟨24749534151480692255876219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65998757737281846015669917 24749534151480692255876219)
      ·
        refine ⟨37124301227221038383814329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24749534151480692255876219 37124301227221038383814329)
        ·
          refine ⟨27843225920415778787860747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37124301227221038383814329 27843225920415778787860747)
          ·
            refine ⟨41764838880623668181791121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27843225920415778787860747 41764838880623668181791121)
            ·
              refine ⟨31323629160467751136343341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41764838880623668181791121 31323629160467751136343341)
              ·
                refine ⟨11746360935175406676128753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31323629160467751136343341 11746360935175406676128753)
                ·
                  refine ⟨8809770701381555007096565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11746360935175406676128753 8809770701381555007096565)
                  ·
                    refine ⟨825916003254520781915303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8809770701381555007096565 825916003254520781915303)
                    ·
                      rfl

theorem cell23_4825397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_4825397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825397 prefixEnd_4825397 := by exact prefixLift 4825397
  have htrace : WordTrace (prefixWord ++ tailWord_4825397) baseStart_4825397 baseEnd_4825397 := by
    simpa [prefixWord, tailWord_4825397, baseEnd_4825397] using wordTrace_append hprefix tailTrace_4825397
  have hstable : (prefixWord ++ tailWord_4825397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825397).length < 2 ^ (prefixWord ++ tailWord_4825397).sum := by decide
  have hdescent : baseEnd_4825397 < baseStart_4825397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825401 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 5]
def baseStart_4825401 : Nat := 118140960795 + 4825401 * 2 ^ 59
def prefixEnd_4825401 : Nat := 4983230072969 + 3 ^ 40 * 4825401 * 2
def baseEnd_4825401 : Nat := 275305562631797814455099

theorem tailTrace_4825401 : CollatzResearch.WordTrace tailWord_4825401 prefixEnd_4825401 275305562631797814455099 := by
  unfold tailWord_4825401
  simp only [CollatzResearch.WordTrace]
  refine ⟨175996833191403764724932057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117331222127602509816621371 175996833191403764724932057)
  ·
    refine ⟨131997624893552823543699043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175996833191403764724932057 131997624893552823543699043)
    ·
      refine ⟨197996437340329235315548565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131997624893552823543699043 197996437340329235315548565)
      ·
        refine ⟨9281083000327932905416339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 197996437340329235315548565 9281083000327932905416339)
        ·
          refine ⟨13921624500491899358124509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9281083000327932905416339 13921624500491899358124509)
          ·
            refine ⟨5220609187684462259296691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13921624500491899358124509 5220609187684462259296691)
            ·
              refine ⟨7830913781526693388945037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220609187684462259296691 7830913781526693388945037)
              ·
                refine ⟨2936592668072510020854389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830913781526693388945037 2936592668072510020854389)
                ·
                  refine ⟨275305562631797814455099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2936592668072510020854389 275305562631797814455099)
                  ·
                    rfl

theorem cell23_4825401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 5].length) (baseStart_4825401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825401 prefixEnd_4825401 := by exact prefixLift 4825401
  have htrace : WordTrace (prefixWord ++ tailWord_4825401) baseStart_4825401 baseEnd_4825401 := by
    simpa [prefixWord, tailWord_4825401, baseEnd_4825401] using wordTrace_append hprefix tailTrace_4825401
  have hstable : (prefixWord ++ tailWord_4825401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825401).length < 2 ^ (prefixWord ++ tailWord_4825401).sum := by decide
  have hdescent : baseEnd_4825401 < baseStart_4825401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825427 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 3, 4]
def baseStart_4825427 : Nat := 118140960795 + 4825427 * 2 ^ 59
def prefixEnd_4825427 : Nat := 4983230072969 + 3 ^ 40 * 4825427 * 2
def baseEnd_4825427 : Nat := 825921138061065742790257

theorem tailTrace_4825427 : CollatzResearch.WordTrace tailWord_4825427 prefixEnd_4825427 825921138061065742790257 := by
  unfold tailWord_4825427
  simp only [CollatzResearch.WordTrace]
  refine ⟨175997781489309571165378535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117331854326206380776919023 175997781489309571165378535)
  ·
    refine ⟨263996672233964356748067803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 175997781489309571165378535 263996672233964356748067803)
    ·
      refine ⟨395995008350946535122101705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263996672233964356748067803 395995008350946535122101705)
      ·
        refine ⟨296996256263209901341576279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395995008350946535122101705 296996256263209901341576279)
        ·
          refine ⟨445494384394814852012364419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296996256263209901341576279 445494384394814852012364419)
          ·
            refine ⟨668241576592222278018546629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445494384394814852012364419 668241576592222278018546629)
            ·
              refine ⟨125295295611041677128477493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 668241576592222278018546629 125295295611041677128477493)
              ·
                refine ⟨11746433963535157230794765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125295295611041677128477493 11746433963535157230794765)
                ·
                  refine ⟨4404912736325683961548037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11746433963535157230794765 4404912736325683961548037)
                  ·
                    refine ⟨825921138061065742790257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4404912736325683961548037 825921138061065742790257)
                    ·
                      rfl

theorem cell23_4825427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 4].length) (baseStart_4825427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825427 prefixEnd_4825427 := by exact prefixLift 4825427
  have htrace : WordTrace (prefixWord ++ tailWord_4825427) baseStart_4825427 baseEnd_4825427 := by
    simpa [prefixWord, tailWord_4825427, baseEnd_4825427] using wordTrace_append hprefix tailTrace_4825427
  have hstable : (prefixWord ++ tailWord_4825427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825427).length < 2 ^ (prefixWord ++ tailWord_4825427).sum := by decide
  have hdescent : baseEnd_4825427 < baseStart_4825427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825505 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4825505 : Nat := 118140960795 + 4825505 * 2 ^ 59
def prefixEnd_4825505 : Nat := 4983230072969 + 3 ^ 40 * 4825505 * 2
def baseEnd_4825505 : Nat := 2477803465674247923195413

theorem tailTrace_4825505 : CollatzResearch.WordTrace tailWord_4825505 prefixEnd_4825505 2477803465674247923195413 := by
  unfold tailWord_4825505
  simp only [CollatzResearch.WordTrace]
  refine ⟨176000626383026990486717969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117333750922017993657811979 176000626383026990486717969)
  ·
    refine ⟨132000469787270242865038477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176000626383026990486717969 132000469787270242865038477)
    ·
      refine ⟨49500176170226341074389429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132000469787270242865038477 49500176170226341074389429)
      ·
        refine ⟨4640641515958719475724009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49500176170226341074389429 4640641515958719475724009)
        ·
          refine ⟨3480481136969039606793007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4640641515958719475724009 3480481136969039606793007)
          ·
            refine ⟨5220721705453559410189511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480481136969039606793007 5220721705453559410189511)
            ·
              refine ⟨7831082558180339115284267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220721705453559410189511 7831082558180339115284267)
              ·
                refine ⟨11746623837270508672926401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7831082558180339115284267 11746623837270508672926401)
                ·
                  refine ⟨8809967877952881504694801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11746623837270508672926401 8809967877952881504694801)
                  ·
                    refine ⟨6607475908464661128521101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8809967877952881504694801 6607475908464661128521101)
                    ·
                      refine ⟨2477803465674247923195413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607475908464661128521101 2477803465674247923195413)
                      ·
                        rfl

theorem cell23_4825505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4825505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825505 prefixEnd_4825505 := by exact prefixLift 4825505
  have htrace : WordTrace (prefixWord ++ tailWord_4825505) baseStart_4825505 baseEnd_4825505 := by
    simpa [prefixWord, tailWord_4825505, baseEnd_4825505] using wordTrace_append hprefix tailTrace_4825505
  have hstable : (prefixWord ++ tailWord_4825505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825505).length < 2 ^ (prefixWord ++ tailWord_4825505).sum := by decide
  have hdescent : baseEnd_4825505 < baseStart_4825505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825511 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4825511 : Nat := 118140960795 + 4825511 * 2 ^ 59
def prefixEnd_4825511 : Nat := 4983230072969 + 3 ^ 40 * 4825511 * 2
def baseEnd_4825511 : Nat := 2477806546558174899720385

theorem tailTrace_4825511 : CollatzResearch.WordTrace tailWord_4825511 prefixEnd_4825511 2477806546558174899720385 := by
  unfold tailWord_4825511
  simp only [CollatzResearch.WordTrace]
  refine ⟨176000845221005253511436387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117333896814003502340957591 176000845221005253511436387)
  ·
    refine ⟨264001267831507880267154581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176000845221005253511436387 264001267831507880267154581)
    ·
      refine ⟨12375059429601931887522871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264001267831507880267154581 12375059429601931887522871)
      ·
        refine ⟨18562589144402897831284307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375059429601931887522871 18562589144402897831284307)
        ·
          refine ⟨27843883716604346746926461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562589144402897831284307 27843883716604346746926461)
          ·
            refine ⟨10441456393726630030097423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27843883716604346746926461 10441456393726630030097423)
            ·
              refine ⟨15662184590589945045146135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10441456393726630030097423 15662184590589945045146135)
              ·
                refine ⟨23493276885884917567719203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15662184590589945045146135 23493276885884917567719203)
                ·
                  refine ⟨35239915328827376351578805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23493276885884917567719203 35239915328827376351578805)
                  ·
                    refine ⟨3303742062077566532960513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35239915328827376351578805 3303742062077566532960513)
                    ·
                      refine ⟨2477806546558174899720385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303742062077566532960513 2477806546558174899720385)
                      ·
                        rfl

theorem cell23_4825511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4825511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825511 prefixEnd_4825511 := by exact prefixLift 4825511
  have htrace : WordTrace (prefixWord ++ tailWord_4825511) baseStart_4825511 baseEnd_4825511 := by
    simpa [prefixWord, tailWord_4825511, baseEnd_4825511] using wordTrace_append hprefix tailTrace_4825511
  have hstable : (prefixWord ++ tailWord_4825511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825511).length < 2 ^ (prefixWord ++ tailWord_4825511).sum := by decide
  have hdescent : baseEnd_4825511 < baseStart_4825511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825521 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 1, 5]
def baseStart_4825521 : Nat := 118140960795 + 4825521 * 2 ^ 59
def prefixEnd_4825521 : Nat := 4983230072969 + 3 ^ 40 * 4825521 * 2
def baseEnd_4825521 : Nat := 825937227121573286865113

theorem tailTrace_4825521 : CollatzResearch.WordTrace tailWord_4825521 prefixEnd_4825521 825937227121573286865113 := by
  unfold tailWord_4825521
  simp only [CollatzResearch.WordTrace]
  refine ⟨176001209950969025219300417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117334139967312683479533611 176001209950969025219300417)
  ·
    refine ⟨132000907463226768914475313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176001209950969025219300417 132000907463226768914475313)
    ·
      refine ⟨99000680597420076685856485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132000907463226768914475313 99000680597420076685856485)
      ·
        refine ⟨18562627612016264378598091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99000680597420076685856485 18562627612016264378598091)
        ·
          refine ⟨27843941418024396567897137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562627612016264378598091 27843941418024396567897137)
          ·
            refine ⟨20882956063518297425922853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27843941418024396567897137 20882956063518297425922853)
            ·
              refine ⟨3915554261909680767360535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20882956063518297425922853 3915554261909680767360535)
              ·
                refine ⟨5873331392864521151040803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915554261909680767360535 5873331392864521151040803)
                ·
                  refine ⟨8809997089296781726561205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873331392864521151040803 8809997089296781726561205)
                  ·
                    refine ⟨825937227121573286865113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8809997089296781726561205 825937227121573286865113)
                    ·
                      rfl

theorem cell23_4825521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_4825521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825521 prefixEnd_4825521 := by exact prefixLift 4825521
  have htrace : WordTrace (prefixWord ++ tailWord_4825521) baseStart_4825521 baseEnd_4825521 := by
    simpa [prefixWord, tailWord_4825521, baseEnd_4825521] using wordTrace_append hprefix tailTrace_4825521
  have hstable : (prefixWord ++ tailWord_4825521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825521).length < 2 ^ (prefixWord ++ tailWord_4825521).sum := by decide
  have hdescent : baseEnd_4825521 < baseStart_4825521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825544 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_4825544 : Nat := 118140960795 + 4825544 * 2 ^ 59
def prefixEnd_4825544 : Nat := 4983230072969 + 3 ^ 40 * 4825544 * 2
def baseEnd_4825544 : Nat := 2477823491419773270607733

theorem tailTrace_4825544 : CollatzResearch.WordTrace tailWord_4825544 prefixEnd_4825544 2477823491419773270607733 := by
  unfold tailWord_4825544
  simp only [CollatzResearch.WordTrace]
  refine ⟨88001024414942850073693843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117334699219923800098258457 88001024414942850073693843)
  ·
    refine ⟨132001536622414275110540765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88001024414942850073693843 132001536622414275110540765)
    ·
      refine ⟨49500576233405353166452787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132001536622414275110540765 49500576233405353166452787)
      ·
        refine ⟨74250864350108029749679181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49500576233405353166452787 74250864350108029749679181)
        ·
          refine ⟨27844074131290511156129693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74250864350108029749679181 27844074131290511156129693)
          ·
            refine ⟨10441527799233941683548635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27844074131290511156129693 10441527799233941683548635)
            ·
              refine ⟨15662291698850912525322953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10441527799233941683548635 15662291698850912525322953)
              ·
                refine ⟨11746718774138184393992215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15662291698850912525322953 11746718774138184393992215)
                ·
                  refine ⟨17620078161207276590988323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11746718774138184393992215 17620078161207276590988323)
                  ·
                    refine ⟨26430117241810914886482485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17620078161207276590988323 26430117241810914886482485)
                    ·
                      refine ⟨2477823491419773270607733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26430117241810914886482485 2477823491419773270607733)
                      ·
                        rfl

theorem cell23_4825544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_4825544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825544 prefixEnd_4825544 := by exact prefixLift 4825544
  have htrace : WordTrace (prefixWord ++ tailWord_4825544) baseStart_4825544 baseEnd_4825544 := by
    simpa [prefixWord, tailWord_4825544, baseEnd_4825544] using wordTrace_append hprefix tailTrace_4825544
  have hstable : (prefixWord ++ tailWord_4825544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825544).length < 2 ^ (prefixWord ++ tailWord_4825544).sum := by decide
  have hdescent : baseEnd_4825544 < baseStart_4825544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825558 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4825558 : Nat := 118140960795 + 4825558 * 2 ^ 59
def prefixEnd_4825558 : Nat := 4983230072969 + 3 ^ 40 * 4825558 * 2
def baseEnd_4825558 : Nat := 2477830680148936215832669

theorem tailTrace_4825558 : CollatzResearch.WordTrace tailWord_4825558 prefixEnd_4825558 2477830680148936215832669 := by
  unfold tailWord_4825558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11000159965739686283649833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117335039634556653692264885 11000159965739686283649833)
  ·
    refine ⟨8250119974304764712737375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11000159965739686283649833 8250119974304764712737375)
    ·
      refine ⟨12375179961457147069106063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250119974304764712737375 12375179961457147069106063)
      ·
        refine ⟨18562769942185720603659095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375179961457147069106063 18562769942185720603659095)
        ·
          refine ⟨27844154913278580905488643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18562769942185720603659095 27844154913278580905488643)
          ·
            refine ⟨41766232369917871358232965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27844154913278580905488643 41766232369917871358232965)
            ·
              refine ⟨7831168569359600879668681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41766232369917871358232965 7831168569359600879668681)
              ·
                refine ⟨5873376427019700659751511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7831168569359600879668681 5873376427019700659751511)
                ·
                  refine ⟨8810064640529550989627267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873376427019700659751511 8810064640529550989627267)
                  ·
                    refine ⟨13215096960794326484440901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8810064640529550989627267 13215096960794326484440901)
                    ·
                      refine ⟨2477830680148936215832669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13215096960794326484440901 2477830680148936215832669)
                      ·
                        rfl

theorem cell23_4825558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4825558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825558 prefixEnd_4825558 := by exact prefixLift 4825558
  have htrace : WordTrace (prefixWord ++ tailWord_4825558) baseStart_4825558 baseEnd_4825558 := by
    simpa [prefixWord, tailWord_4825558, baseEnd_4825558] using wordTrace_append hprefix tailTrace_4825558
  have hstable : (prefixWord ++ tailWord_4825558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825558).length < 2 ^ (prefixWord ++ tailWord_4825558).sum := by decide
  have hdescent : baseEnd_4825558 < baseStart_4825558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825561 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 3]
def baseStart_4825561 : Nat := 118140960795 + 4825561 * 2 ^ 59
def prefixEnd_4825561 : Nat := 4983230072969 + 3 ^ 40 * 4825561 * 2
def baseEnd_4825561 : Nat := 2477832220590899704095155

theorem tailTrace_4825561 : CollatzResearch.WordTrace tailWord_4825561 prefixEnd_4825561 2477832220590899704095155 := by
  unfold tailWord_4825561
  simp only [CollatzResearch.WordTrace]
  refine ⟨176002668870824112050756537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117335112580549408033837691 176002668870824112050756537)
  ·
    refine ⟨132002001653118084038067403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176002668870824112050756537 132002001653118084038067403)
    ·
      refine ⟨198003002479677126057101105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132002001653118084038067403 198003002479677126057101105)
      ·
        refine ⟨148502251859757844542825829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198003002479677126057101105 148502251859757844542825829)
        ·
          refine ⟨27844172223704595851779843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148502251859757844542825829 27844172223704595851779843)
          ·
            refine ⟨41766258335556893777669765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27844172223704595851779843 41766258335556893777669765)
            ·
              refine ⟨7831173437916917583313081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41766258335556893777669765 7831173437916917583313081)
              ·
                refine ⟨5873380078437688187484811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7831173437916917583313081 5873380078437688187484811)
                ·
                  refine ⟨8810070117656532281227217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873380078437688187484811 8810070117656532281227217)
                  ·
                    refine ⟨6607552588242399210920413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8810070117656532281227217 6607552588242399210920413)
                    ·
                      refine ⟨2477832220590899704095155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607552588242399210920413 2477832220590899704095155)
                      ·
                        rfl

theorem cell23_4825561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_4825561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825561 prefixEnd_4825561 := by exact prefixLift 4825561
  have htrace : WordTrace (prefixWord ++ tailWord_4825561) baseStart_4825561 baseEnd_4825561 := by
    simpa [prefixWord, tailWord_4825561, baseEnd_4825561] using wordTrace_append hprefix tailTrace_4825561
  have hstable : (prefixWord ++ tailWord_4825561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825561).length < 2 ^ (prefixWord ++ tailWord_4825561).sum := by decide
  have hdescent : baseEnd_4825561 < baseStart_4825561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825587 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_4825587 : Nat := 118140960795 + 4825587 * 2 ^ 59
def prefixEnd_4825587 : Nat := 4983230072969 + 3 ^ 40 * 4825587 * 2
def baseEnd_4825587 : Nat := 2477845571087916602370035

theorem tailTrace_4825587 : CollatzResearch.WordTrace tailWord_4825587 prefixEnd_4825587 2477845571087916602370035 := by
  unfold tailWord_4825587
  simp only [CollatzResearch.WordTrace]
  refine ⟨176003617168729918491203015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117335744779153278994135343 176003617168729918491203015)
  ·
    refine ⟨264005425753094877736804523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176003617168729918491203015 264005425753094877736804523)
    ·
      refine ⟨396008138629642316605206785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264005425753094877736804523 396008138629642316605206785)
      ·
        refine ⟨297006103972231737453905089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396008138629642316605206785 297006103972231737453905089)
        ·
          refine ⟨222754577979173803090428817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297006103972231737453905089 222754577979173803090428817)
          ·
            refine ⟨167065933484380352317821613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222754577979173803090428817 167065933484380352317821613)
            ·
              refine ⟨62649725056642632119183105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167065933484380352317821613 62649725056642632119183105)
              ·
                refine ⟨46987293792481974089387329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62649725056642632119183105 46987293792481974089387329)
                ·
                  refine ⟨35240470344361480567040497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46987293792481974089387329 35240470344361480567040497)
                  ·
                    refine ⟨26430352758271110425280373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35240470344361480567040497 26430352758271110425280373)
                    ·
                      refine ⟨2477845571087916602370035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26430352758271110425280373 2477845571087916602370035)
                      ·
                        rfl

theorem cell23_4825587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_4825587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825587 prefixEnd_4825587 := by exact prefixLift 4825587
  have htrace : WordTrace (prefixWord ++ tailWord_4825587) baseStart_4825587 baseEnd_4825587 := by
    simpa [prefixWord, tailWord_4825587, baseEnd_4825587] using wordTrace_append hprefix tailTrace_4825587
  have hstable : (prefixWord ++ tailWord_4825587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825587).length < 2 ^ (prefixWord ++ tailWord_4825587).sum := by decide
  have hdescent : baseEnd_4825587 < baseStart_4825587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825602 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_4825602 : Nat := 118140960795 + 4825602 * 2 ^ 59
def prefixEnd_4825602 : Nat := 4983230072969 + 3 ^ 40 * 4825602 * 2
def baseEnd_4825602 : Nat := 825951091099244681227489

theorem tailTrace_4825602 : CollatzResearch.WordTrace tailWord_4825602 prefixEnd_4825602 825951091099244681227489 := by
  unfold tailWord_4825602
  simp only [CollatzResearch.WordTrace]
  refine ⟨44001041065918894013249765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117336109509117050701999373 44001041065918894013249765)
  ·
    refine ⟨8250195199859792627484331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44001041065918894013249765 8250195199859792627484331)
    ·
      refine ⟨12375292799789688941226497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250195199859792627484331 12375292799789688941226497)
      ·
        refine ⟨9281469599842266705919873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12375292799789688941226497 9281469599842266705919873)
        ·
          refine ⟨6961102199881700029439905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9281469599842266705919873 6961102199881700029439905)
          ·
            refine ⟨5220826649911275022079929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6961102199881700029439905 5220826649911275022079929)
            ·
              refine ⟨3915619987433456266559947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5220826649911275022079929 3915619987433456266559947)
              ·
                refine ⟨5873429981150184399839921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915619987433456266559947 5873429981150184399839921)
                ·
                  refine ⟨4405072485862638299879941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873429981150184399839921 4405072485862638299879941)
                  ·
                    refine ⟨825951091099244681227489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405072485862638299879941 825951091099244681227489)
                    ·
                      rfl

theorem cell23_4825602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_4825602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825602 prefixEnd_4825602 := by exact prefixLift 4825602
  have htrace : WordTrace (prefixWord ++ tailWord_4825602) baseStart_4825602 baseEnd_4825602 := by
    simpa [prefixWord, tailWord_4825602, baseEnd_4825602] using wordTrace_append hprefix tailTrace_4825602
  have hstable : (prefixWord ++ tailWord_4825602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825602).length < 2 ^ (prefixWord ++ tailWord_4825602).sum := by decide
  have hdescent : baseEnd_4825602 < baseStart_4825602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825635 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 1, 3, 2]
def baseStart_4825635 : Nat := 118140960795 + 4825635 * 2 ^ 59
def prefixEnd_4825635 : Nat := 4983230072969 + 3 ^ 40 * 4825635 * 2
def baseEnd_4825635 : Nat := 2477870218159332414569815

theorem tailTrace_4825635 : CollatzResearch.WordTrace tailWord_4825635 prefixEnd_4825635 2477870218159332414569815 := by
  unfold tailWord_4825635
  simp only [CollatzResearch.WordTrace]
  refine ⟨176005367872556022688950359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117336911915037348459300239 176005367872556022688950359)
  ·
    refine ⟨264008051808834034033425539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176005367872556022688950359 264008051808834034033425539)
    ·
      refine ⟨396012077713251051050138309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264008051808834034033425539 396012077713251051050138309)
      ·
        refine ⟨74252264571234572071900933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 396012077713251051050138309 74252264571234572071900933)
        ·
          refine ⟨13922299607106482263481425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74252264571234572071900933 13922299607106482263481425)
          ·
            refine ⟨10441724705329861697611069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13922299607106482263481425 10441724705329861697611069)
            ·
              refine ⟨3915646764498698136604151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10441724705329861697611069 3915646764498698136604151)
              ·
                refine ⟨5873470146748047204906227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915646764498698136604151 5873470146748047204906227)
                ·
                  refine ⟨8810205220122070807359341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873470146748047204906227 8810205220122070807359341)
                  ·
                    refine ⟨3303826957545776552759753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8810205220122070807359341 3303826957545776552759753)
                    ·
                      refine ⟨2477870218159332414569815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303826957545776552759753 2477870218159332414569815)
                      ·
                        rfl

theorem cell23_4825635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_4825635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825635 prefixEnd_4825635 := by exact prefixLift 4825635
  have htrace : WordTrace (prefixWord ++ tailWord_4825635) baseStart_4825635 baseEnd_4825635 := by
    simpa [prefixWord, tailWord_4825635, baseEnd_4825635] using wordTrace_append hprefix tailTrace_4825635
  have hstable : (prefixWord ++ tailWord_4825635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825635).length < 2 ^ (prefixWord ++ tailWord_4825635).sum := by decide
  have hdescent : baseEnd_4825635 < baseStart_4825635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825648 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 2, 2, 2]
def baseStart_4825648 : Nat := 118140960795 + 4825648 * 2 ^ 59
def prefixEnd_4825648 : Nat := 4983230072969 + 3 ^ 40 * 4825648 * 2
def baseEnd_4825648 : Nat := 2477876893407840863707255

theorem tailTrace_4825648 : CollatzResearch.WordTrace tailWord_4825648 prefixEnd_4825648 2477876893407840863707255 := by
  unfold tailWord_4825648
  simp only [CollatzResearch.WordTrace]
  refine ⟨88002921010754462954586799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117337228014339283939449065 88002921010754462954586799)
  ·
    refine ⟨132004381516131694431880199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88002921010754462954586799 132004381516131694431880199)
    ·
      refine ⟨198006572274197541647820299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132004381516131694431880199 198006572274197541647820299)
      ·
        refine ⟨297009858411296312471730449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198006572274197541647820299 297009858411296312471730449)
        ·
          refine ⟨222757393808472234353797837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297009858411296312471730449 222757393808472234353797837)
          ·
            refine ⟨83534022678177087882674189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222757393808472234353797837 83534022678177087882674189)
            ·
              refine ⟨31325258504316407956002821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83534022678177087882674189 31325258504316407956002821)
              ·
                refine ⟨5873485969559326491750529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31325258504316407956002821 5873485969559326491750529)
                ·
                  refine ⟨4405114477169494868812897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873485969559326491750529 4405114477169494868812897)
                  ·
                    refine ⟨3303835857877121151609673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4405114477169494868812897 3303835857877121151609673)
                    ·
                      refine ⟨2477876893407840863707255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303835857877121151609673 2477876893407840863707255)
                      ·
                        rfl

theorem cell23_4825648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 2, 2].length) (baseStart_4825648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825648 prefixEnd_4825648 := by exact prefixLift 4825648
  have htrace : WordTrace (prefixWord ++ tailWord_4825648) baseStart_4825648 baseEnd_4825648 := by
    simpa [prefixWord, tailWord_4825648, baseEnd_4825648] using wordTrace_append hprefix tailTrace_4825648
  have hstable : (prefixWord ++ tailWord_4825648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825648).length < 2 ^ (prefixWord ++ tailWord_4825648).sum := by decide
  have hdescent : baseEnd_4825648 < baseStart_4825648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825661 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4825661 : Nat := 118140960795 + 4825661 * 2 ^ 59
def prefixEnd_4825661 : Nat := 4983230072969 + 3 ^ 40 * 4825661 * 2
def baseEnd_4825661 : Nat := 2477883568656349312844695

theorem tailTrace_4825661 : CollatzResearch.WordTrace tailWord_4825661 prefixEnd_4825661 2477883568656349312844695 := by
  unfold tailWord_4825661
  simp only [CollatzResearch.WordTrace]
  refine ⟨176006316170461829129396837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117337544113641219419597891 176006316170461829129396837)
  ·
    refine ⟨33001184281961592961761907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176006316170461829129396837 33001184281961592961761907)
    ·
      refine ⟨49501776422942389442642861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33001184281961592961761907 49501776422942389442642861)
      ·
        refine ⟨18563166158603396040991073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49501776422942389442642861 18563166158603396040991073)
        ·
          refine ⟨13922374618952547030743305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18563166158603396040991073 13922374618952547030743305)
          ·
            refine ⟨10441780964214410273057479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13922374618952547030743305 10441780964214410273057479)
            ·
              refine ⟨15662671446321615409586219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10441780964214410273057479 15662671446321615409586219)
              ·
                refine ⟨23494007169482423114379329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15662671446321615409586219 23494007169482423114379329)
                ·
                  refine ⟨17620505377111817335784497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23494007169482423114379329 17620505377111817335784497)
                  ·
                    refine ⟨13215379032833863001838373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17620505377111817335784497 13215379032833863001838373)
                    ·
                      refine ⟨2477883568656349312844695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13215379032833863001838373 2477883568656349312844695)
                      ·
                        rfl

theorem cell23_4825661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4825661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825661 prefixEnd_4825661 := by exact prefixLift 4825661
  have htrace : WordTrace (prefixWord ++ tailWord_4825661) baseStart_4825661 baseEnd_4825661 := by
    simpa [prefixWord, tailWord_4825661, baseEnd_4825661] using wordTrace_append hprefix tailTrace_4825661
  have hstable : (prefixWord ++ tailWord_4825661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825661).length < 2 ^ (prefixWord ++ tailWord_4825661).sum := by decide
  have hdescent : baseEnd_4825661 < baseStart_4825661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825664 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_4825664 : Nat := 118140960795 + 4825664 * 2 ^ 59
def prefixEnd_4825664 : Nat := 4983230072969 + 3 ^ 40 * 4825664 * 2
def baseEnd_4825664 : Nat := 2477885109098312801107181

theorem tailTrace_4825664 : CollatzResearch.WordTrace tailWord_4825664 prefixEnd_4825664 2477885109098312801107181 := by
  unfold tailWord_4825664
  simp only [CollatzResearch.WordTrace]
  refine ⟨88003212794725480320878023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117337617059633973761170697 88003212794725480320878023)
  ·
    refine ⟨132004819192088220481317035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88003212794725480320878023 132004819192088220481317035)
    ·
      refine ⟨198007228788132330721975553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132004819192088220481317035 198007228788132330721975553)
      ·
        refine ⟨148505421591099248041481665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198007228788132330721975553 148505421591099248041481665)
        ·
          refine ⟨111379066193324436031111249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148505421591099248041481665 111379066193324436031111249)
          ·
            refine ⟨83534299644993327023333437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111379066193324436031111249 83534299644993327023333437)
            ·
              refine ⟨31325362366872497633750039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83534299644993327023333437 31325362366872497633750039)
              ·
                refine ⟨46988043550308746450625059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31325362366872497633750039 46988043550308746450625059)
                ·
                  refine ⟨70482065325463119675937589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46988043550308746450625059 70482065325463119675937589)
                  ·
                    refine ⟨6607693624262167469619149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70482065325463119675937589 6607693624262167469619149)
                    ·
                      refine ⟨2477885109098312801107181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607693624262167469619149 2477885109098312801107181)
                      ·
                        rfl

theorem cell23_4825664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_4825664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825664 prefixEnd_4825664 := by exact prefixLift 4825664
  have htrace : WordTrace (prefixWord ++ tailWord_4825664) baseStart_4825664 baseEnd_4825664 := by
    simpa [prefixWord, tailWord_4825664, baseEnd_4825664] using wordTrace_append hprefix tailTrace_4825664
  have hstable : (prefixWord ++ tailWord_4825664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825664).length < 2 ^ (prefixWord ++ tailWord_4825664).sum := by decide
  have hdescent : baseEnd_4825664 < baseStart_4825664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825665 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_4825665 : Nat := 118140960795 + 4825665 * 2 ^ 59
def prefixEnd_4825665 : Nat := 4983230072969 + 3 ^ 40 * 4825665 * 2
def baseEnd_4825665 : Nat := 2477885622578967297194677

theorem tailTrace_4825665 : CollatzResearch.WordTrace tailWord_4825665 prefixEnd_4825665 2477885622578967297194677 := by
  unfold tailWord_4825665
  simp only [CollatzResearch.WordTrace]
  refine ⟨176006462062447337812542449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117337641374964891875028299 176006462062447337812542449)
  ·
    refine ⟨132004846546835503359406837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176006462062447337812542449 132004846546835503359406837)
    ·
      refine ⟨12375454363765828439944391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132004846546835503359406837 12375454363765828439944391)
      ·
        refine ⟨18563181545648742659916587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12375454363765828439944391 18563181545648742659916587)
        ·
          refine ⟨27844772318473113989874881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18563181545648742659916587 27844772318473113989874881)
          ·
            refine ⟨20883579238854835492406161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27844772318473113989874881 20883579238854835492406161)
            ·
              refine ⟨15662684429141126619304621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20883579238854835492406161 15662684429141126619304621)
              ·
                refine ⟨5873506660927922482239233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15662684429141126619304621 5873506660927922482239233)
                ·
                  refine ⟨4405129995695941861679425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873506660927922482239233 4405129995695941861679425)
                  ·
                    refine ⟨3303847496771956396259569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4405129995695941861679425 3303847496771956396259569)
                    ·
                      refine ⟨2477885622578967297194677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3303847496771956396259569 2477885622578967297194677)
                      ·
                        rfl

theorem cell23_4825665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_4825665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825665 prefixEnd_4825665 := by exact prefixLift 4825665
  have htrace : WordTrace (prefixWord ++ tailWord_4825665) baseStart_4825665 baseEnd_4825665 := by
    simpa [prefixWord, tailWord_4825665, baseEnd_4825665] using wordTrace_append hprefix tailTrace_4825665
  have hstable : (prefixWord ++ tailWord_4825665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825665).length < 2 ^ (prefixWord ++ tailWord_4825665).sum := by decide
  have hdescent : baseEnd_4825665 < baseStart_4825665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825731 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 3, 4]
def baseStart_4825731 : Nat := 118140960795 + 4825731 * 2 ^ 59
def prefixEnd_4825731 : Nat := 4983230072969 + 3 ^ 40 * 4825731 * 2
def baseEnd_4825731 : Nat := 825973170767388012989791

theorem tailTrace_4825731 : CollatzResearch.WordTrace tailWord_4825731 prefixEnd_4825731 825973170767388012989791 := by
  unfold tailWord_4825731
  simp only [CollatzResearch.WordTrace]
  refine ⟨176008869280208231084445047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117339246186805487389630031 176008869280208231084445047)
  ·
    refine ⟨264013303920312346626667571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176008869280208231084445047 264013303920312346626667571)
    ·
      refine ⟨396019955880468519940001357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264013303920312346626667571 396019955880468519940001357)
      ·
        refine ⟨148507483455175694977500509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396019955880468519940001357 148507483455175694977500509)
        ·
          refine ⟨55690306295690885616562691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148507483455175694977500509 55690306295690885616562691)
          ·
            refine ⟨83535459443536328424844037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55690306295690885616562691 83535459443536328424844037)
            ·
              refine ⟨15662898645663061579658257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83535459443536328424844037 15662898645663061579658257)
              ·
                refine ⟨11747173984247296184743693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15662898645663061579658257 11747173984247296184743693)
                ·
                  refine ⟨4405190244092736069278885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11747173984247296184743693 4405190244092736069278885)
                  ·
                    refine ⟨825973170767388012989791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4405190244092736069278885 825973170767388012989791)
                    ·
                      rfl

theorem cell23_4825731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 4].length) (baseStart_4825731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825731 prefixEnd_4825731 := by exact prefixLift 4825731
  have htrace : WordTrace (prefixWord ++ tailWord_4825731) baseStart_4825731 baseEnd_4825731 := by
    simpa [prefixWord, tailWord_4825731, baseEnd_4825731] using wordTrace_append hprefix tailTrace_4825731
  have hstable : (prefixWord ++ tailWord_4825731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825731).length < 2 ^ (prefixWord ++ tailWord_4825731).sum := by decide
  have hdescent : baseEnd_4825731 < baseStart_4825731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825788 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4825788 : Nat := 118140960795 + 4825788 * 2 ^ 59
def prefixEnd_4825788 : Nat := 4983230072969 + 3 ^ 40 * 4825788 * 2
def baseEnd_4825788 : Nat := 2477948780699470315956611

theorem tailTrace_4825788 : CollatzResearch.WordTrace tailWord_4825788 prefixEnd_4825788 2477948780699470315956611 := by
  unfold tailWord_4825788
  simp only [CollatzResearch.WordTrace]
  refine ⟨88005474120500864909635009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117340632160667819879513345 88005474120500864909635009)
  ·
    refine ⟨66004105590375648682226257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88005474120500864909635009 66004105590375648682226257)
    ·
      refine ⟨49503079192781736511669693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66004105590375648682226257 49503079192781736511669693)
      ·
        refine ⟨18563654697293151191876135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49503079192781736511669693 18563654697293151191876135)
        ·
          refine ⟨27845482045939726787814203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18563654697293151191876135 27845482045939726787814203)
          ·
            refine ⟨41768223068909590181721305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27845482045939726787814203 41768223068909590181721305)
            ·
              refine ⟨31326167301682192636290979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41768223068909590181721305 31326167301682192636290979)
              ·
                refine ⟨46989250952523288954436469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31326167301682192636290979 46989250952523288954436469)
                ·
                  refine ⟨4405242276799058339478419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46989250952523288954436469 4405242276799058339478419)
                  ·
                    refine ⟨6607863415198587509217629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4405242276799058339478419 6607863415198587509217629)
                    ·
                      refine ⟨2477948780699470315956611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607863415198587509217629 2477948780699470315956611)
                      ·
                        rfl

theorem cell23_4825788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4825788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825788 prefixEnd_4825788 := by exact prefixLift 4825788
  have htrace : WordTrace (prefixWord ++ tailWord_4825788) baseStart_4825788 baseEnd_4825788 := by
    simpa [prefixWord, tailWord_4825788, baseEnd_4825788] using wordTrace_append hprefix tailTrace_4825788
  have hstable : (prefixWord ++ tailWord_4825788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825788).length < 2 ^ (prefixWord ++ tailWord_4825788).sum := by decide
  have hdescent : baseEnd_4825788 < baseStart_4825788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825791 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 3, 5]
def baseStart_4825791 : Nat := 118140960795 + 4825791 * 2 ^ 59
def prefixEnd_4825791 : Nat := 4983230072969 + 3 ^ 40 * 4825791 * 2
def baseEnd_4825791 : Nat := 825983440380477934739699

theorem tailTrace_4825791 : CollatzResearch.WordTrace tailWord_4825791 prefixEnd_4825791 825983440380477934739699 := by
  unfold tailWord_4825791
  simp only [CollatzResearch.WordTrace]
  refine ⟨176011057659990861331629227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117340705106660574221086151 176011057659990861331629227)
  ·
    refine ⟨264016586489986291997443841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176011057659990861331629227 264016586489986291997443841)
    ·
      refine ⟨198012439867489718998082881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264016586489986291997443841 198012439867489718998082881)
      ·
        refine ⟨148509329900617289248562161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198012439867489718998082881 148509329900617289248562161)
        ·
          refine ⟨111381997425462966936421621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148509329900617289248562161 111381997425462966936421621)
          ·
            refine ⟨10442062258637153150289527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111381997425462966936421621 10442062258637153150289527)
            ·
              refine ⟨15663093387955729725434291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10442062258637153150289527 15663093387955729725434291)
              ·
                refine ⟨23494640081933594588151437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15663093387955729725434291 23494640081933594588151437)
                ·
                  refine ⟨8810490030725097970556789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23494640081933594588151437 8810490030725097970556789)
                  ·
                    refine ⟨825983440380477934739699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8810490030725097970556789 825983440380477934739699)
                    ·
                      rfl

theorem cell23_4825791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_4825791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825791 prefixEnd_4825791 := by exact prefixLift 4825791
  have htrace : WordTrace (prefixWord ++ tailWord_4825791) baseStart_4825791 baseEnd_4825791 := by
    simpa [prefixWord, tailWord_4825791, baseEnd_4825791] using wordTrace_append hprefix tailTrace_4825791
  have hstable : (prefixWord ++ tailWord_4825791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825791).length < 2 ^ (prefixWord ++ tailWord_4825791).sum := by decide
  have hdescent : baseEnd_4825791 < baseStart_4825791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825838 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_4825838 : Nat := 118140960795 + 4825838 * 2 ^ 59
def prefixEnd_4825838 : Nat := 4983230072969 + 3 ^ 40 * 4825838 * 2
def baseEnd_4825838 : Nat := 825991484910731706777127

theorem tailTrace_4825838 : CollatzResearch.WordTrace tailWord_4825838 prefixEnd_4825838 825991484910731706777127 := by
  unfold tailWord_4825838
  simp only [CollatzResearch.WordTrace]
  refine ⟨22001596486352573544823771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117341847927213725572393445 22001596486352573544823771)
  ·
    refine ⟨33002394729528860317235657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22001596486352573544823771 33002394729528860317235657)
    ·
      refine ⟨24751796047146645237926743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33002394729528860317235657 24751796047146645237926743)
      ·
        refine ⟨37127694070719967856890115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24751796047146645237926743 37127694070719967856890115)
        ·
          refine ⟨55691541106079951785335173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37127694070719967856890115 55691541106079951785335173)
          ·
            refine ⟨10442163957389990959750345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55691541106079951785335173 10442163957389990959750345)
            ·
              refine ⟨7831622968042493219812759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10442163957389990959750345 7831622968042493219812759)
              ·
                refine ⟨11747434452063739829719139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7831622968042493219812759 11747434452063739829719139)
                ·
                  refine ⟨17621151678095609744578709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11747434452063739829719139 17621151678095609744578709)
                  ·
                    refine ⟨825991484910731706777127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17621151678095609744578709 825991484910731706777127)
                    ·
                      rfl

theorem cell23_4825838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_4825838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825838 prefixEnd_4825838 := by exact prefixLift 4825838
  have htrace : WordTrace (prefixWord ++ tailWord_4825838) baseStart_4825838 baseEnd_4825838 := by
    simpa [prefixWord, tailWord_4825838, baseEnd_4825838] using wordTrace_append hprefix tailTrace_4825838
  have hstable : (prefixWord ++ tailWord_4825838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825838).length < 2 ^ (prefixWord ++ tailWord_4825838).sum := by decide
  have hdescent : baseEnd_4825838 < baseStart_4825838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825848 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 1, 2, 3]
def baseStart_4825848 : Nat := 118140960795 + 4825848 * 2 ^ 59
def prefixEnd_4825848 : Nat := 4983230072969 + 3 ^ 40 * 4825848 * 2
def baseEnd_4825848 : Nat := 2477979589538740081206335

theorem tailTrace_4825848 : CollatzResearch.WordTrace tailWord_4825848 prefixEnd_4825848 2477979589538740081206335 := by
  unfold tailWord_4825848
  simp only [CollatzResearch.WordTrace]
  refine ⟨88006568310392180033227099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117342091080522906710969465 88006568310392180033227099)
  ·
    refine ⟨132009852465588270049840649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88006568310392180033227099 132009852465588270049840649)
    ·
      refine ⟨99007389349191202537380487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132009852465588270049840649 99007389349191202537380487)
      ·
        refine ⟨148511084023786803806070731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99007389349191202537380487 148511084023786803806070731)
        ·
          refine ⟨222766626035680205709106097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148511084023786803806070731 222766626035680205709106097)
          ·
            refine ⟨167074969526760154281829573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222766626035680205709106097 167074969526760154281829573)
            ·
              refine ⟨31326556786267528927843045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167074969526760154281829573 31326556786267528927843045)
              ·
                refine ⟨5873729397425161673970571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31326556786267528927843045 5873729397425161673970571)
                ·
                  refine ⟨8810594096137742510955857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873729397425161673970571 8810594096137742510955857)
                  ·
                    refine ⟨6607945572103306883216893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8810594096137742510955857 6607945572103306883216893)
                    ·
                      refine ⟨2477979589538740081206335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607945572103306883216893 2477979589538740081206335)
                      ·
                        rfl

theorem cell23_4825848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_4825848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825848 prefixEnd_4825848 := by exact prefixLift 4825848
  have htrace : WordTrace (prefixWord ++ tailWord_4825848) baseStart_4825848 baseEnd_4825848 := by
    simpa [prefixWord, tailWord_4825848, baseEnd_4825848] using wordTrace_append hprefix tailTrace_4825848
  have hstable : (prefixWord ++ tailWord_4825848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825848).length < 2 ^ (prefixWord ++ tailWord_4825848).sum := by decide
  have hdescent : baseEnd_4825848 < baseStart_4825848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825865 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 1, 2, 3]
def baseStart_4825865 : Nat := 118140960795 + 4825865 * 2 ^ 59
def prefixEnd_4825865 : Nat := 4983230072969 + 3 ^ 40 * 4825865 * 2
def baseEnd_4825865 : Nat := 2477988318709866514693757

theorem tailTrace_4825865 : CollatzResearch.WordTrace tailWord_4825865 prefixEnd_4825865 2477988318709866514693757 := by
  unfold tailWord_4825865
  simp only [CollatzResearch.WordTrace]
  refine ⟨176013756661722771969823049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117342504441148514646548699 176013756661722771969823049)
  ·
    refine ⟨132010317496292078977367287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176013756661722771969823049 132010317496292078977367287)
    ·
      refine ⟨198015476244438118466050931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132010317496292078977367287 198015476244438118466050931)
      ·
        refine ⟨297023214366657177699076397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198015476244438118466050931 297023214366657177699076397)
        ·
          refine ⟨111383705387496441637153649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297023214366657177699076397 111383705387496441637153649)
          ·
            refine ⟨83537779040622331227865237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111383705387496441637153649 83537779040622331227865237)
            ·
              refine ⟨3915833392529171776306183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83537779040622331227865237 3915833392529171776306183)
              ·
                refine ⟨5873750088793757664459275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915833392529171776306183 5873750088793757664459275)
                ·
                  refine ⟨8810625133190636496688913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5873750088793757664459275 8810625133190636496688913)
                  ·
                    refine ⟨6607968849892977372516685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8810625133190636496688913 6607968849892977372516685)
                    ·
                      refine ⟨2477988318709866514693757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6607968849892977372516685 2477988318709866514693757)
                      ·
                        rfl

theorem cell23_4825865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 2, 3].length) (baseStart_4825865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825865 prefixEnd_4825865 := by exact prefixLift 4825865
  have htrace : WordTrace (prefixWord ++ tailWord_4825865) baseStart_4825865 baseEnd_4825865 := by
    simpa [prefixWord, tailWord_4825865, baseEnd_4825865] using wordTrace_append hprefix tailTrace_4825865
  have hstable : (prefixWord ++ tailWord_4825865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825865).length < 2 ^ (prefixWord ++ tailWord_4825865).sum := by decide
  have hdescent : baseEnd_4825865 < baseStart_4825865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825892 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_4825892 : Nat := 118140960795 + 4825892 * 2 ^ 59
def prefixEnd_4825892 : Nat := 4983230072969 + 3 ^ 40 * 4825892 * 2
def baseEnd_4825892 : Nat := 2478002182687537909056133

theorem tailTrace_4825892 : CollatzResearch.WordTrace tailWord_4825892 prefixEnd_4825892 2478002182687537909056133 := by
  unfold tailWord_4825892
  simp only [CollatzResearch.WordTrace]
  refine ⟨88007370716312477790527965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117343160955083303720703953 88007370716312477790527965)
  ·
    refine ⟨33002764018617179171447987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88007370716312477790527965 33002764018617179171447987)
    ·
      refine ⟨49504146027925768757171981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33002764018617179171447987 49504146027925768757171981)
      ·
        refine ⟨18564054760472163283939493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49504146027925768757171981 18564054760472163283939493)
        ·
          refine ⟨3480760267588530615738655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18564054760472163283939493 3480760267588530615738655)
          ·
            refine ⟨5221140401382795923607983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480760267588530615738655 5221140401382795923607983)
            ·
              refine ⟨7831710602074193885411975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221140401382795923607983 7831710602074193885411975)
              ·
                refine ⟨11747565903111290828117963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7831710602074193885411975 11747565903111290828117963)
                ·
                  refine ⟨17621348854666936242176945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11747565903111290828117963 17621348854666936242176945)
                  ·
                    refine ⟨13216011641000202181632709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17621348854666936242176945 13216011641000202181632709)
                    ·
                      refine ⟨2478002182687537909056133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13216011641000202181632709 2478002182687537909056133)
                      ·
                        rfl

theorem cell23_4825892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_4825892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825892 prefixEnd_4825892 := by exact prefixLift 4825892
  have htrace : WordTrace (prefixWord ++ tailWord_4825892) baseStart_4825892 baseEnd_4825892 := by
    simpa [prefixWord, tailWord_4825892, baseEnd_4825892] using wordTrace_append hprefix tailTrace_4825892
  have hstable : (prefixWord ++ tailWord_4825892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825892).length < 2 ^ (prefixWord ++ tailWord_4825892).sum := by decide
  have hdescent : baseEnd_4825892 < baseStart_4825892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825938 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_4825938 : Nat := 118140960795 + 4825938 * 2 ^ 59
def prefixEnd_4825938 : Nat := 4983230072969 + 3 ^ 40 * 4825938 * 2
def baseEnd_4825938 : Nat := 2478025802797644729080921

theorem tailTrace_4825938 : CollatzResearch.WordTrace tailWord_4825938 prefixEnd_4825938 2478025802797644729080921 := by
  unfold tailWord_4825938
  simp only [CollatzResearch.WordTrace]
  refine ⟨44004104797614576359307617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117344279460305536958153645 44004104797614576359307617)
  ·
    refine ⟨33003078598210932269480713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44004104797614576359307617 33003078598210932269480713)
    ·
      refine ⟨24752308948658199202110535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33003078598210932269480713 24752308948658199202110535)
      ·
        refine ⟨37128463422987298803165803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24752308948658199202110535 37128463422987298803165803)
        ·
          refine ⟨55692695134480948204748705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37128463422987298803165803 55692695134480948204748705)
          ·
            refine ⟨41769521350860711153561529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55692695134480948204748705 41769521350860711153561529)
            ·
              refine ⟨31327141013145533365171147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41769521350860711153561529 31327141013145533365171147)
              ·
                refine ⟨46990711519718300047756721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31327141013145533365171147 46990711519718300047756721)
                ·
                  refine ⟨35243033639788725035817541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46990711519718300047756721 35243033639788725035817541)
                  ·
                    refine ⟨6608068807460385944215789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35243033639788725035817541 6608068807460385944215789)
                    ·
                      refine ⟨2478025802797644729080921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608068807460385944215789 2478025802797644729080921)
                      ·
                        rfl

theorem cell23_4825938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_4825938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825938 prefixEnd_4825938 := by exact prefixLift 4825938
  have htrace : WordTrace (prefixWord ++ tailWord_4825938) baseStart_4825938 baseEnd_4825938 := by
    simpa [prefixWord, tailWord_4825938, baseEnd_4825938] using wordTrace_append hprefix tailTrace_4825938
  have hstable : (prefixWord ++ tailWord_4825938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825938).length < 2 ^ (prefixWord ++ tailWord_4825938).sum := by decide
  have hdescent : baseEnd_4825938 < baseStart_4825938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825952 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 2, 2, 2]
def baseStart_4825952 : Nat := 118140960795 + 4825952 * 2 ^ 59
def prefixEnd_4825952 : Nat := 4983230072969 + 3 ^ 40 * 4825952 * 2
def baseEnd_4825952 : Nat := 2478032991526807674305857

theorem tailTrace_4825952 : CollatzResearch.WordTrace tailWord_4825952 prefixEnd_4825952 2478032991526807674305857 := by
  unfold tailWord_4825952
  simp only [CollatzResearch.WordTrace]
  refine ⟨88008464906203792914120055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117344619874938390552160073 88008464906203792914120055)
  ·
    refine ⟨132012697359305689371180083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88008464906203792914120055 132012697359305689371180083)
    ·
      refine ⟨198019046038958534056770125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132012697359305689371180083 198019046038958534056770125)
      ·
        refine ⟨74257142264609450271288797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198019046038958534056770125 74257142264609450271288797)
        ·
          refine ⟨27846428349228543851733299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74257142264609450271288797 27846428349228543851733299)
          ·
            refine ⟨41769642523842815777599949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27846428349228543851733299 41769642523842815777599949)
            ·
              refine ⟨15663615946441055916599981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41769642523842815777599949 15663615946441055916599981)
              ·
                refine ⟨5873855979915395968724993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15663615946441055916599981 5873855979915395968724993)
                ·
                  refine ⟨4405391984936546976543745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5873855979915395968724993 4405391984936546976543745)
                  ·
                    refine ⟨3304043988702410232407809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4405391984936546976543745 3304043988702410232407809)
                    ·
                      refine ⟨2478032991526807674305857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304043988702410232407809 2478032991526807674305857)
                      ·
                        rfl

theorem cell23_4825952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_4825952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825952 prefixEnd_4825952 := by exact prefixLift 4825952
  have htrace : WordTrace (prefixWord ++ tailWord_4825952) baseStart_4825952 baseEnd_4825952 := by
    simpa [prefixWord, tailWord_4825952, baseEnd_4825952] using wordTrace_append hprefix tailTrace_4825952
  have hstable : (prefixWord ++ tailWord_4825952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825952).length < 2 ^ (prefixWord ++ tailWord_4825952).sum := by decide
  have hdescent : baseEnd_4825952 < baseStart_4825952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825971 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 1, 7]
def baseStart_4825971 : Nat := 118140960795 + 4825971 * 2 ^ 59
def prefixEnd_4825971 : Nat := 4983230072969 + 3 ^ 40 * 4825971 * 2
def baseEnd_4825971 : Nat := 826014249219747699989423

theorem tailTrace_4825971 : CollatzResearch.WordTrace tailWord_4825971 prefixEnd_4825971 826014249219747699989423 := by
  unfold tailWord_4825971
  simp only [CollatzResearch.WordTrace]
  refine ⟨176017622799338752073181767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117345081866225834715454511 176017622799338752073181767)
  ·
    refine ⟨264026434199008128109772651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176017622799338752073181767 264026434199008128109772651)
    ·
      refine ⟨396039651298512192164658977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264026434199008128109772651 396039651298512192164658977)
      ·
        refine ⟨297029738473884144123494233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396039651298512192164658977 297029738473884144123494233)
        ·
          refine ⟨222772303855413108092620675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297029738473884144123494233 222772303855413108092620675)
          ·
            refine ⟨334158455783119662138931013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222772303855413108092620675 334158455783119662138931013)
            ·
              refine ⟨62654710459334936651049565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 334158455783119662138931013 62654710459334936651049565)
              ·
                refine ⟨23495516422250601244143587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62654710459334936651049565 23495516422250601244143587)
                ·
                  refine ⟨35243274633375901866215381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23495516422250601244143587 35243274633375901866215381)
                  ·
                    refine ⟨826014249219747699989423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35243274633375901866215381 826014249219747699989423)
                    ·
                      rfl

theorem cell23_4825971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 7].length) (baseStart_4825971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825971 prefixEnd_4825971 := by exact prefixLift 4825971
  have htrace : WordTrace (prefixWord ++ tailWord_4825971) baseStart_4825971 baseEnd_4825971 := by
    simpa [prefixWord, tailWord_4825971, baseEnd_4825971] using wordTrace_append hprefix tailTrace_4825971
  have hstable : (prefixWord ++ tailWord_4825971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825971).length < 2 ^ (prefixWord ++ tailWord_4825971).sum := by decide
  have hdescent : baseEnd_4825971 < baseStart_4825971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4825992 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 5]
def baseStart_4825992 : Nat := 118140960795 + 4825992 * 2 ^ 59
def prefixEnd_4825992 : Nat := 4983230072969 + 3 ^ 40 * 4825992 * 2
def baseEnd_4825992 : Nat := 275339281194776390867297

theorem tailTrace_4825992 : CollatzResearch.WordTrace tailWord_4825992 prefixEnd_4825992 275339281194776390867297 := by
  unfold tailWord_4825992
  simp only [CollatzResearch.WordTrace]
  refine ⟨88009194366131336329848115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117345592488175115106464153 88009194366131336329848115)
  ·
    refine ⟨132013791549197004494772173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88009194366131336329848115 132013791549197004494772173)
    ·
      refine ⟨49505171830948876685539565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132013791549197004494772173 49505171830948876685539565)
      ·
        refine ⟨18564439436605828757077337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49505171830948876685539565 18564439436605828757077337)
        ·
          refine ⟨13923329577454371567808003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18564439436605828757077337 13923329577454371567808003)
          ·
            refine ⟨20884994366181557351712005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13923329577454371567808003 20884994366181557351712005)
            ·
              refine ⟨3915936443659042003446001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20884994366181557351712005 3915936443659042003446001)
              ·
                refine ⟨2936952332744281502584501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3915936443659042003446001 2936952332744281502584501)
                ·
                  refine ⟨275339281194776390867297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2936952332744281502584501 275339281194776390867297)
                  ·
                    rfl

theorem cell23_4825992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 5].length) (baseStart_4825992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4825992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4825992 prefixEnd_4825992 := by exact prefixLift 4825992
  have htrace : WordTrace (prefixWord ++ tailWord_4825992) baseStart_4825992 baseEnd_4825992 := by
    simpa [prefixWord, tailWord_4825992, baseEnd_4825992] using wordTrace_append hprefix tailTrace_4825992
  have hstable : (prefixWord ++ tailWord_4825992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4825992).length < 2 ^ (prefixWord ++ tailWord_4825992).sum := by decide
  have hdescent : baseEnd_4825992 < baseStart_4825992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4825992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826001 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_4826001 : Nat := 118140960795 + 4826001 * 2 ^ 59
def prefixEnd_4826001 : Nat := 4983230072969 + 3 ^ 40 * 4826001 * 2
def baseEnd_4826001 : Nat := 826019384026292660864377

theorem tailTrace_4826001 : CollatzResearch.WordTrace tailWord_4826001 prefixEnd_4826001 826019384026292660864377 := by
  unfold tailWord_4826001
  simp only [CollatzResearch.WordTrace]
  refine ⟨176018716989230067196773857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117345811326153378131182571 176018716989230067196773857)
  ·
    refine ⟨132014037741922550397580393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176018716989230067196773857 132014037741922550397580393)
    ·
      refine ⟨99010528306441912798185295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132014037741922550397580393 99010528306441912798185295)
      ·
        refine ⟨148515792459662869197277943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99010528306441912798185295 148515792459662869197277943)
        ·
          refine ⟨222773688689494303795916915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148515792459662869197277943 222773688689494303795916915)
          ·
            refine ⟨334160533034241455693875373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222773688689494303795916915 334160533034241455693875373)
            ·
              refine ⟨125310199887840545885203265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334160533034241455693875373 125310199887840545885203265)
              ·
                refine ⟨93982649915880409413902449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125310199887840545885203265 93982649915880409413902449)
                ·
                  refine ⟨70486987436910307060426837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93982649915880409413902449 70486987436910307060426837)
                  ·
                    refine ⟨826019384026292660864377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70486987436910307060426837 826019384026292660864377)
                    ·
                      rfl

theorem cell23_4826001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_4826001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826001 prefixEnd_4826001 := by exact prefixLift 4826001
  have htrace : WordTrace (prefixWord ++ tailWord_4826001) baseStart_4826001 baseEnd_4826001 := by
    simpa [prefixWord, tailWord_4826001, baseEnd_4826001] using wordTrace_append hprefix tailTrace_4826001
  have hstable : (prefixWord ++ tailWord_4826001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826001).length < 2 ^ (prefixWord ++ tailWord_4826001).sum := by decide
  have hdescent : baseEnd_4826001 < baseStart_4826001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826002 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4826002 : Nat := 118140960795 + 4826002 * 2 ^ 59
def prefixEnd_4826002 : Nat := 4983230072969 + 3 ^ 40 * 4826002 * 2
def baseEnd_4826002 : Nat := 2478058665559532478680627

theorem tailTrace_4826002 : CollatzResearch.WordTrace tailWord_4826002 prefixEnd_4826002 2478058665559532478680627 := by
  unfold tailWord_4826002
  simp only [CollatzResearch.WordTrace]
  refine ⟨44004688365556611091890065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117345835641484296245040173 44004688365556611091890065)
  ·
    refine ⟨33003516274167458318917549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44004688365556611091890065 33003516274167458318917549)
    ·
      refine ⟨12376318602812796869594081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33003516274167458318917549 12376318602812796869594081)
      ·
        refine ⟨9282238952109597652195561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12376318602812796869594081 9282238952109597652195561)
        ·
          refine ⟨6961679214082198239146671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9282238952109597652195561 6961679214082198239146671)
          ·
            refine ⟨10442518821123297358720007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6961679214082198239146671 10442518821123297358720007)
            ·
              refine ⟨15663778231684946038080011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10442518821123297358720007 15663778231684946038080011)
              ·
                refine ⟨23495667347527419057120017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15663778231684946038080011 23495667347527419057120017)
                ·
                  refine ⟨17621750510645564292840013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23495667347527419057120017 17621750510645564292840013)
                  ·
                    refine ⟨6608156441492086609815005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17621750510645564292840013 6608156441492086609815005)
                    ·
                      refine ⟨2478058665559532478680627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608156441492086609815005 2478058665559532478680627)
                      ·
                        rfl

theorem cell23_4826002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4826002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826002 prefixEnd_4826002 := by exact prefixLift 4826002
  have htrace : WordTrace (prefixWord ++ tailWord_4826002) baseStart_4826002 baseEnd_4826002 := by
    simpa [prefixWord, tailWord_4826002, baseEnd_4826002] using wordTrace_append hprefix tailTrace_4826002
  have hstable : (prefixWord ++ tailWord_4826002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826002).length < 2 ^ (prefixWord ++ tailWord_4826002).sum := by decide
  have hdescent : baseEnd_4826002 < baseStart_4826002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826028 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_4826028 : Nat := 118140960795 + 4826028 * 2 ^ 59
def prefixEnd_4826028 : Nat := 4983230072969 + 3 ^ 40 * 4826028 * 2
def baseEnd_4826028 : Nat := 2478072016056549376955507

theorem tailTrace_4826028 : CollatzResearch.WordTrace tailWord_4826028 prefixEnd_4826028 2478072016056549376955507 := by
  unfold tailWord_4826028
  simp only [CollatzResearch.WordTrace]
  refine ⟨88009850880066125404003369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117346467840088167205337825 88009850880066125404003369)
  ·
    refine ⟨66007388160049594053002527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88009850880066125404003369 66007388160049594053002527)
    ·
      refine ⟨99011082240074391079503791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66007388160049594053002527 99011082240074391079503791)
      ·
        refine ⟨148516623360111586619255687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99011082240074391079503791 148516623360111586619255687)
        ·
          refine ⟨222774935040167379928883531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148516623360111586619255687 222774935040167379928883531)
          ·
            refine ⟨334162402560251069893325297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222774935040167379928883531 334162402560251069893325297)
            ·
              refine ⟨250621801920188302419993973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334162402560251069893325297 250621801920188302419993973)
              ·
                refine ⟨23495793930017653351874435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250621801920188302419993973 23495793930017653351874435)
                ·
                  refine ⟨35243690895026480027811653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23495793930017653351874435 35243690895026480027811653)
                  ·
                    refine ⟨6608192042817465005214685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35243690895026480027811653 6608192042817465005214685)
                    ·
                      refine ⟨2478072016056549376955507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608192042817465005214685 2478072016056549376955507)
                      ·
                        rfl

theorem cell23_4826028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_4826028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826028 prefixEnd_4826028 := by exact prefixLift 4826028
  have htrace : WordTrace (prefixWord ++ tailWord_4826028) baseStart_4826028 baseEnd_4826028 := by
    simpa [prefixWord, tailWord_4826028, baseEnd_4826028] using wordTrace_append hprefix tailTrace_4826028
  have hstable : (prefixWord ++ tailWord_4826028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826028).length < 2 ^ (prefixWord ++ tailWord_4826028).sum := by decide
  have hdescent : baseEnd_4826028 < baseStart_4826028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826048 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 8]
def baseStart_4826048 : Nat := 118140960795 + 4826048 * 2 ^ 59
def prefixEnd_4826048 : Nat := 4983230072969 + 3 ^ 40 * 4826048 * 2
def baseEnd_4826048 : Nat := 275342476185515477633935

theorem tailTrace_4826048 : CollatzResearch.WordTrace tailWord_4826048 prefixEnd_4826048 275342476185515477633935 := by
  unfold tailWord_4826048
  simp only [CollatzResearch.WordTrace]
  refine ⟨88010215610029897111867399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117346954146706529482489865 88010215610029897111867399)
  ·
    refine ⟨132015323415044845667801099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88010215610029897111867399 132015323415044845667801099)
    ·
      refine ⟨198022985122567268501701649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132015323415044845667801099 198022985122567268501701649)
      ·
        refine ⟨148517238841925451376276237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198022985122567268501701649 148517238841925451376276237)
        ·
          refine ⟨55693964565722044266103589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148517238841925451376276237 55693964565722044266103589)
          ·
            refine ⟨10442618356072883299894423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55693964565722044266103589 10442618356072883299894423)
            ·
              refine ⟨15663927534109324949841635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10442618356072883299894423 15663927534109324949841635)
              ·
                refine ⟨23495891301163987424762453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15663927534109324949841635 23495891301163987424762453)
                ·
                  refine ⟨275342476185515477633935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23495891301163987424762453 275342476185515477633935)
                  ·
                    rfl

theorem cell23_4826048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 8].length) (baseStart_4826048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826048 prefixEnd_4826048 := by exact prefixLift 4826048
  have htrace : WordTrace (prefixWord ++ tailWord_4826048) baseStart_4826048 baseEnd_4826048 := by
    simpa [prefixWord, tailWord_4826048, baseEnd_4826048] using wordTrace_append hprefix tailTrace_4826048
  have hstable : (prefixWord ++ tailWord_4826048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826048).length < 2 ^ (prefixWord ++ tailWord_4826048).sum := by decide
  have hdescent : baseEnd_4826048 < baseStart_4826048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826065 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 6]
def baseStart_4826065 : Nat := 118140960795 + 4826065 * 2 ^ 59
def prefixEnd_4826065 : Nat := 4983230072969 + 3 ^ 40 * 4826065 * 2
def baseEnd_4826065 : Nat := 275343446093418414688093

theorem tailTrace_4826065 : CollatzResearch.WordTrace tailWord_4826065 prefixEnd_4826065 275343446093418414688093 := by
  unfold tailWord_4826065
  simp only [CollatzResearch.WordTrace]
  refine ⟨176021051260998206127103649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117347367507332137418069099 176021051260998206127103649)
  ·
    refine ⟨132015788445748654595327737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176021051260998206127103649 132015788445748654595327737)
    ·
      refine ⟨99011841334311490946495803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132015788445748654595327737 99011841334311490946495803)
      ·
        refine ⟨148517762001467236419743705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99011841334311490946495803 148517762001467236419743705)
        ·
          refine ⟨111388321501100427314807779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148517762001467236419743705 111388321501100427314807779)
          ·
            refine ⟨167082482251650640972211669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111388321501100427314807779 167082482251650640972211669)
            ·
              refine ⟨3915995677773061897786211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167082482251650640972211669 3915995677773061897786211)
              ·
                refine ⟨5873993516659592846679317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915995677773061897786211 5873993516659592846679317)
                ·
                  refine ⟨275343446093418414688093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5873993516659592846679317 275343446093418414688093)
                  ·
                    rfl

theorem cell23_4826065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 6].length) (baseStart_4826065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826065 prefixEnd_4826065 := by exact prefixLift 4826065
  have htrace : WordTrace (prefixWord ++ tailWord_4826065) baseStart_4826065 baseEnd_4826065 := by
    simpa [prefixWord, tailWord_4826065, baseEnd_4826065] using wordTrace_append hprefix tailTrace_4826065
  have hstable : (prefixWord ++ tailWord_4826065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826065).length < 2 ^ (prefixWord ++ tailWord_4826065).sum := by decide
  have hdescent : baseEnd_4826065 < baseStart_4826065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826095 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 1, 5]
def baseStart_4826095 : Nat := 118140960795 + 4826095 * 2 ^ 59
def prefixEnd_4826095 : Nat := 4983230072969 + 3 ^ 40 * 4826095 * 2
def baseEnd_4826095 : Nat := 826035473086800204939233

theorem tailTrace_4826095 : CollatzResearch.WordTrace tailWord_4826095 prefixEnd_4826095 826035473086800204939233 := by
  unfold tailWord_4826095
  simp only [CollatzResearch.WordTrace]
  refine ⟨176022145450889521250695739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117348096967259680833797159 176022145450889521250695739)
  ·
    refine ⟨264033218176334281876043609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176022145450889521250695739 264033218176334281876043609)
    ·
      refine ⟨198024913632250711407032707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264033218176334281876043609 198024913632250711407032707)
      ·
        refine ⟨297037370448376067110549061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198024913632250711407032707 297037370448376067110549061)
        ·
          refine ⟨55694506959070512583227949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 297037370448376067110549061 55694506959070512583227949)
          ·
            refine ⟨20885440109651442218710481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55694506959070512583227949 20885440109651442218710481)
            ·
              refine ⟨15664080082238581664032861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20885440109651442218710481 15664080082238581664032861)
              ·
                refine ⟨5874030030839468124012323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15664080082238581664032861 5874030030839468124012323)
                ·
                  refine ⟨8811045046259202186018485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874030030839468124012323 8811045046259202186018485)
                  ·
                    refine ⟨826035473086800204939233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8811045046259202186018485 826035473086800204939233)
                    ·
                      rfl

theorem cell23_4826095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_4826095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826095 prefixEnd_4826095 := by exact prefixLift 4826095
  have htrace : WordTrace (prefixWord ++ tailWord_4826095) baseStart_4826095 baseEnd_4826095 := by
    simpa [prefixWord, tailWord_4826095, baseEnd_4826095] using wordTrace_append hprefix tailTrace_4826095
  have hstable : (prefixWord ++ tailWord_4826095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826095).length < 2 ^ (prefixWord ++ tailWord_4826095).sum := by decide
  have hdescent : baseEnd_4826095 < baseStart_4826095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826138 : List Nat := [3, 1, 1, 3, 1, 2, 1, 11]
def baseStart_4826138 : Nat := 118140960795 + 4826138 * 2 ^ 59
def prefixEnd_4826138 : Nat := 4983230072969 + 3 ^ 40 * 4826138 * 2
def baseEnd_4826138 : Nat := 91782536997353479502963

theorem tailTrace_4826138 : CollatzResearch.WordTrace tailWord_4826138 prefixEnd_4826138 91782536997353479502963 := by
  unfold tailWord_4826138
  simp only [CollatzResearch.WordTrace]
  refine ⟨44005928447433434898627767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117349142526489159729674045 44005928447433434898627767)
  ·
    refine ⟨66008892671150152347941651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44005928447433434898627767 66008892671150152347941651)
    ·
      refine ⟨99013339006725228521912477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66008892671150152347941651 99013339006725228521912477)
      ·
        refine ⟨37130002127521960695717179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99013339006725228521912477 37130002127521960695717179)
        ·
          refine ⟨55695003191282941043575769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37130002127521960695717179 55695003191282941043575769)
          ·
            refine ⟨41771252393462205782681827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55695003191282941043575769 41771252393462205782681827)
            ·
              refine ⟨62656878590193308674022741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41771252393462205782681827 62656878590193308674022741)
              ·
                refine ⟨91782536997353479502963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 62656878590193308674022741 91782536997353479502963)
                ·
                  rfl

theorem cell23_4826138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_4826138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826138 prefixEnd_4826138 := by exact prefixLift 4826138
  have htrace : WordTrace (prefixWord ++ tailWord_4826138) baseStart_4826138 baseEnd_4826138 := by
    simpa [prefixWord, tailWord_4826138, baseEnd_4826138] using wordTrace_append hprefix tailTrace_4826138
  have hstable : (prefixWord ++ tailWord_4826138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826138).length < 2 ^ (prefixWord ++ tailWord_4826138).sum := by decide
  have hdescent : baseEnd_4826138 < baseStart_4826138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826145 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4826145 : Nat := 118140960795 + 4826145 * 2 ^ 59
def prefixEnd_4826145 : Nat := 4983230072969 + 3 ^ 40 * 4826145 * 2
def baseEnd_4826145 : Nat := 2478132093293125419192469

theorem tailTrace_4826145 : CollatzResearch.WordTrace tailWord_4826145 prefixEnd_4826145 2478132093293125419192469 := by
  unfold tailWord_4826145
  simp only [CollatzResearch.WordTrace]
  refine ⟨176023969100708379790015889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117349312733805586526677259 176023969100708379790015889)
  ·
    refine ⟨132017976825531284842511917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176023969100708379790015889 132017976825531284842511917)
    ·
      refine ⟨49506741309574231815941969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132017976825531284842511917 49506741309574231815941969)
      ·
        refine ⟨37130055982180673861956477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49506741309574231815941969 37130055982180673861956477)
        ·
          refine ⟨13923770993317752698233679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37130055982180673861956477 13923770993317752698233679)
          ·
            refine ⟨20885656489976629047350519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13923770993317752698233679 20885656489976629047350519)
            ·
              refine ⟨31328484734964943571025779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20885656489976629047350519 31328484734964943571025779)
              ·
                refine ⟨46992727102447415356538669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31328484734964943571025779 46992727102447415356538669)
                ·
                  refine ⟨17622272663417780758702001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46992727102447415356538669 17622272663417780758702001)
                  ·
                    refine ⟨13216704497563335569026501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17622272663417780758702001 13216704497563335569026501)
                    ·
                      refine ⟨2478132093293125419192469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13216704497563335569026501 2478132093293125419192469)
                      ·
                        rfl

theorem cell23_4826145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4826145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826145 prefixEnd_4826145 := by exact prefixLift 4826145
  have htrace : WordTrace (prefixWord ++ tailWord_4826145) baseStart_4826145 baseEnd_4826145 := by
    simpa [prefixWord, tailWord_4826145, baseEnd_4826145] using wordTrace_append hprefix tailTrace_4826145
  have hstable : (prefixWord ++ tailWord_4826145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826145).length < 2 ^ (prefixWord ++ tailWord_4826145).sum := by decide
  have hdescent : baseEnd_4826145 < baseStart_4826145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826165 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_4826165 : Nat := 118140960795 + 4826165 * 2 ^ 59
def prefixEnd_4826165 : Nat := 4983230072969 + 3 ^ 40 * 4826165 * 2
def baseEnd_4826165 : Nat := 2478142362906215340942377

theorem tailTrace_4826165 : CollatzResearch.WordTrace tailWord_4826165 prefixEnd_4826165 2478142362906215340942377 := by
  unfold tailWord_4826165
  simp only [CollatzResearch.WordTrace]
  refine ⟨176024698560635923205743949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117349799040423948803829299 176024698560635923205743949)
  ·
    refine ⟨66009261960238471202153981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176024698560635923205743949 66009261960238471202153981)
    ·
      refine ⟨24753473235089426700807743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66009261960238471202153981 24753473235089426700807743)
      ·
        refine ⟨37130209852634140051211615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24753473235089426700807743 37130209852634140051211615)
        ·
          refine ⟨55695314778951210076817423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37130209852634140051211615 55695314778951210076817423)
          ·
            refine ⟨83542972168426815115226135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55695314778951210076817423 83542972168426815115226135)
            ·
              refine ⟨125314458252640222672839203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83542972168426815115226135 125314458252640222672839203)
              ·
                refine ⟨187971687378960334009258805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125314458252640222672839203 187971687378960334009258805)
                ·
                  refine ⟨17622345691777531313368013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187971687378960334009258805 17622345691777531313368013)
                  ·
                    refine ⟨6608379634416574242513005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17622345691777531313368013 6608379634416574242513005)
                    ·
                      refine ⟨2478142362906215340942377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608379634416574242513005 2478142362906215340942377)
                      ·
                        rfl

theorem cell23_4826165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_4826165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826165 prefixEnd_4826165 := by exact prefixLift 4826165
  have htrace : WordTrace (prefixWord ++ tailWord_4826165) baseStart_4826165 baseEnd_4826165 := by
    simpa [prefixWord, tailWord_4826165, baseEnd_4826165] using wordTrace_append hprefix tailTrace_4826165
  have hstable : (prefixWord ++ tailWord_4826165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826165).length < 2 ^ (prefixWord ++ tailWord_4826165).sum := by decide
  have hdescent : baseEnd_4826165 < baseStart_4826165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826215 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 2, 6]
def baseStart_4826215 : Nat := 118140960795 + 4826215 * 2 ^ 59
def prefixEnd_4826215 : Nat := 4983230072969 + 3 ^ 40 * 4826215 * 2
def baseEnd_4826215 : Nat := 826056012312980048439049

theorem tailTrace_4826215 : CollatzResearch.WordTrace tailWord_4826215 prefixEnd_4826215 826056012312980048439049 := by
  unfold tailWord_4826215
  simp only [CollatzResearch.WordTrace]
  refine ⟨176026522210454781745064099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117351014806969854496709399 176026522210454781745064099)
  ·
    refine ⟨264039783315682172617596149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176026522210454781745064099 264039783315682172617596149)
    ·
      refine ⟨24753729685845203682899639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 264039783315682172617596149 24753729685845203682899639)
      ·
        refine ⟨37130594528767805524349459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24753729685845203682899639 37130594528767805524349459)
        ·
          refine ⟨55695891793151708286524189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37130594528767805524349459 55695891793151708286524189)
          ·
            refine ⟨20885959422431890607446571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55695891793151708286524189 20885959422431890607446571)
            ·
              refine ⟨31328939133647835911169857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20885959422431890607446571 31328939133647835911169857)
              ·
                refine ⟨23496704350235876933377393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31328939133647835911169857 23496704350235876933377393)
                ·
                  refine ⟨17622528262676907700033045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23496704350235876933377393 17622528262676907700033045)
                  ·
                    refine ⟨826056012312980048439049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17622528262676907700033045 826056012312980048439049)
                    ·
                      rfl

theorem cell23_4826215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_4826215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826215 prefixEnd_4826215 := by exact prefixLift 4826215
  have htrace : WordTrace (prefixWord ++ tailWord_4826215) baseStart_4826215 baseEnd_4826215 := by
    simpa [prefixWord, tailWord_4826215, baseEnd_4826215] using wordTrace_append hprefix tailTrace_4826215
  have hstable : (prefixWord ++ tailWord_4826215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826215).length < 2 ^ (prefixWord ++ tailWord_4826215).sum := by decide
  have hdescent : baseEnd_4826215 < baseStart_4826215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826216 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4826216 : Nat := 118140960795 + 4826216 * 2 ^ 59
def prefixEnd_4826216 : Nat := 4983230072969 + 3 ^ 40 * 4826216 * 2
def baseEnd_4826216 : Nat := 2478168550419594641404643

theorem tailTrace_4826216 : CollatzResearch.WordTrace tailWord_4826216 prefixEnd_4826216 2478168550419594641404643 := by
  unfold tailWord_4826216
  simp only [CollatzResearch.WordTrace]
  refine ⟨88013279341725579457925251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117351039122300772610567001 88013279341725579457925251)
  ·
    refine ⟨132019919012588369186887877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88013279341725579457925251 132019919012588369186887877)
    ·
      refine ⟨24753734814860319222541477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132019919012588369186887877 24753734814860319222541477)
      ·
        refine ⟨4641325277786309854226527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24753734814860319222541477 4641325277786309854226527)
        ·
          refine ⟨6961987916679464781339791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641325277786309854226527 6961987916679464781339791)
          ·
            refine ⟨10442981875019197172009687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6961987916679464781339791 10442981875019197172009687)
            ·
              refine ⟨15664472812528795758014531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10442981875019197172009687 15664472812528795758014531)
              ·
                refine ⟨23496709218793193637021797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15664472812528795758014531 23496709218793193637021797)
                ·
                  refine ⟨4405632978523723806941587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23496709218793193637021797 4405632978523723806941587)
                  ·
                    refine ⟨6608449467785585710412381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4405632978523723806941587 6608449467785585710412381)
                    ·
                      refine ⟨2478168550419594641404643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608449467785585710412381 2478168550419594641404643)
                      ·
                        rfl

theorem cell23_4826216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4826216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826216 prefixEnd_4826216 := by exact prefixLift 4826216
  have htrace : WordTrace (prefixWord ++ tailWord_4826216) baseStart_4826216 baseEnd_4826216 := by
    simpa [prefixWord, tailWord_4826216, baseEnd_4826216] using wordTrace_append hprefix tailTrace_4826216
  have hstable : (prefixWord ++ tailWord_4826216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826216).length < 2 ^ (prefixWord ++ tailWord_4826216).sum := by decide
  have hdescent : baseEnd_4826216 < baseStart_4826216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826225 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_4826225 : Nat := 118140960795 + 4826225 * 2 ^ 59
def prefixEnd_4826225 : Nat := 4983230072969 + 3 ^ 40 * 4826225 * 2
def baseEnd_4826225 : Nat := 2478173171745485106192101

theorem tailTrace_4826225 : CollatzResearch.WordTrace tailWord_4826225 prefixEnd_4826225 2478173171745485106192101 := by
  unfold tailWord_4826225
  simp only [CollatzResearch.WordTrace]
  refine ⟨176026886940418553452928129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117351257960279035635285419 176026886940418553452928129)
  ·
    refine ⟨132020165205313915089696097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176026886940418553452928129 132020165205313915089696097)
    ·
      refine ⟨99015123903985436317272073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132020165205313915089696097 99015123903985436317272073)
      ·
        refine ⟨74261342927989077237954055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99015123903985436317272073 74261342927989077237954055)
        ·
          refine ⟨111392014391983615856931083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74261342927989077237954055 111392014391983615856931083)
          ·
            refine ⟨167088021587975423785396625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111392014391983615856931083 167088021587975423785396625)
            ·
              refine ⟨125316016190981567839047469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167088021587975423785396625 125316016190981567839047469)
              ·
                refine ⟨46993506071618087939642801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125316016190981567839047469 46993506071618087939642801)
                ·
                  refine ⟨35245129553713565954732101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46993506071618087939642801 35245129553713565954732101)
                  ·
                    refine ⟨6608461791321293616512269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35245129553713565954732101 6608461791321293616512269)
                    ·
                      refine ⟨2478173171745485106192101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608461791321293616512269 2478173171745485106192101)
                      ·
                        rfl

theorem cell23_4826225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_4826225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826225 prefixEnd_4826225 := by exact prefixLift 4826225
  have htrace : WordTrace (prefixWord ++ tailWord_4826225) baseStart_4826225 baseEnd_4826225 := by
    simpa [prefixWord, tailWord_4826225, baseEnd_4826225] using wordTrace_append hprefix tailTrace_4826225
  have hstable : (prefixWord ++ tailWord_4826225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826225).length < 2 ^ (prefixWord ++ tailWord_4826225).sum := by decide
  have hdescent : baseEnd_4826225 < baseStart_4826225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826279 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 7]
def baseStart_4826279 : Nat := 118140960795 + 4826279 * 2 ^ 59
def prefixEnd_4826279 : Nat := 4983230072969 + 3 ^ 40 * 4826279 * 2
def baseEnd_4826279 : Nat := 275355655522314210546317

theorem tailTrace_4826279 : CollatzResearch.WordTrace tailWord_4826279 prefixEnd_4826279 275355655522314210546317 := by
  unfold tailWord_4826279
  simp only [CollatzResearch.WordTrace]
  refine ⟨176028856482222920675393891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117352570988148613783595927 176028856482222920675393891)
  ·
    refine ⟨264043284723334381013090837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176028856482222920675393891 264043284723334381013090837)
    ·
      refine ⟨12377028971406299109988633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264043284723334381013090837 12377028971406299109988633)
      ·
        refine ⟨9282771728554724332491475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12377028971406299109988633 9282771728554724332491475)
        ·
          refine ⟨13924157592832086498737213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9282771728554724332491475 13924157592832086498737213)
          ·
            refine ⟨5221559097312032437026455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13924157592832086498737213 5221559097312032437026455)
            ·
              refine ⟨7832338645968048655539683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221559097312032437026455 7832338645968048655539683)
              ·
                refine ⟨11748507968952072983309525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7832338645968048655539683 11748507968952072983309525)
                ·
                  refine ⟨275355655522314210546317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11748507968952072983309525 275355655522314210546317)
                  ·
                    rfl

theorem cell23_4826279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 7].length) (baseStart_4826279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826279 prefixEnd_4826279 := by exact prefixLift 4826279
  have htrace : WordTrace (prefixWord ++ tailWord_4826279) baseStart_4826279 baseEnd_4826279 := by
    simpa [prefixWord, tailWord_4826279, baseEnd_4826279] using wordTrace_append hprefix tailTrace_4826279
  have hstable : (prefixWord ++ tailWord_4826279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826279).length < 2 ^ (prefixWord ++ tailWord_4826279).sum := by decide
  have hdescent : baseEnd_4826279 < baseStart_4826279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826312 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_4826312 : Nat := 118140960795 + 4826312 * 2 ^ 59
def prefixEnd_4826312 : Nat := 4983230072969 + 3 ^ 40 * 4826312 * 2
def baseEnd_4826312 : Nat := 2478217844562426265804201

theorem tailTrace_4826312 : CollatzResearch.WordTrace tailWord_4826312 prefixEnd_4826312 2478217844562426265804201 := by
  unfold tailWord_4826312
  simp only [CollatzResearch.WordTrace]
  refine ⟨88015030045551683655672595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117353373394068911540896793 88015030045551683655672595)
  ·
    refine ⟨132022545068327525483508893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88015030045551683655672595 132022545068327525483508893)
    ·
      refine ⟨49508454400622822056315835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132022545068327525483508893 49508454400622822056315835)
      ·
        refine ⟨74262681600934233084473753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49508454400622822056315835 74262681600934233084473753)
        ·
          refine ⟨55697011200700674813355315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74262681600934233084473753 55697011200700674813355315)
          ·
            refine ⟨83545516801051012220032973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55697011200700674813355315 83545516801051012220032973)
            ·
              refine ⟨31329568800394129582512365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83545516801051012220032973 31329568800394129582512365)
              ·
                refine ⟨11748588300147798593442137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31329568800394129582512365 11748588300147798593442137)
                ·
                  refine ⟨8811441225110848945081603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11748588300147798593442137 8811441225110848945081603)
                  ·
                    refine ⟨13217161837666273417622405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8811441225110848945081603 13217161837666273417622405)
                    ·
                      refine ⟨2478217844562426265804201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13217161837666273417622405 2478217844562426265804201)
                      ·
                        rfl

theorem cell23_4826312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_4826312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826312 prefixEnd_4826312 := by exact prefixLift 4826312
  have htrace : WordTrace (prefixWord ++ tailWord_4826312) baseStart_4826312 baseEnd_4826312 := by
    simpa [prefixWord, tailWord_4826312, baseEnd_4826312] using wordTrace_append hprefix tailTrace_4826312
  have hstable : (prefixWord ++ tailWord_4826312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826312).length < 2 ^ (prefixWord ++ tailWord_4826312).sum := by decide
  have hdescent : baseEnd_4826312 < baseStart_4826312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826335 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 8]
def baseStart_4826335 : Nat := 118140960795 + 4826335 * 2 ^ 59
def prefixEnd_4826335 : Nat := 4983230072969 + 3 ^ 40 * 4826335 * 2
def baseEnd_4826335 : Nat := 275358850513053297312955

theorem tailTrace_4826335 : CollatzResearch.WordTrace tailWord_4826335 prefixEnd_4826335 275358850513053297312955 := by
  unfold tailWord_4826335
  simp only [CollatzResearch.WordTrace]
  refine ⟨176030898970020042239432459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117353932646680028159621639 176030898970020042239432459)
  ·
    refine ⟨264046348455030063359148689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176030898970020042239432459 264046348455030063359148689)
    ·
      refine ⟨198034761341272547519361517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264046348455030063359148689 198034761341272547519361517)
      ·
        refine ⟨74263035502977205319760569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198034761341272547519361517 74263035502977205319760569)
        ·
          refine ⟨55697276627232903989820427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74263035502977205319760569 55697276627232903989820427)
          ·
            refine ⟨83545914940849355984730641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55697276627232903989820427 83545914940849355984730641)
            ·
              refine ⟨62659436205637016988547981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83545914940849355984730641 62659436205637016988547981)
              ·
                refine ⟨23497288577113881370705493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62659436205637016988547981 23497288577113881370705493)
                ·
                  refine ⟨275358850513053297312955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23497288577113881370705493 275358850513053297312955)
                  ·
                    rfl

theorem cell23_4826335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 8].length) (baseStart_4826335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826335 prefixEnd_4826335 := by exact prefixLift 4826335
  have htrace : WordTrace (prefixWord ++ tailWord_4826335) baseStart_4826335 baseEnd_4826335 := by
    simpa [prefixWord, tailWord_4826335, baseEnd_4826335] using wordTrace_append hprefix tailTrace_4826335
  have hstable : (prefixWord ++ tailWord_4826335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826335).length < 2 ^ (prefixWord ++ tailWord_4826335).sum := by decide
  have hdescent : baseEnd_4826335 < baseStart_4826335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826366 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4826366 : Nat := 118140960795 + 4826366 * 2 ^ 59
def prefixEnd_4826366 : Nat := 4983230072969 + 3 ^ 40 * 4826366 * 2
def baseEnd_4826366 : Nat := 2478245572517769054528953

theorem tailTrace_4826366 : CollatzResearch.WordTrace tailWord_4826366 prefixEnd_4826366 2478245572517769054528953 := by
  unfold tailWord_4826366
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004003704113466816726369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117354686421938489689207301 22004003704113466816726369)
  ·
    refine ⟨16503002778085100112544777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22004003704113466816726369 16503002778085100112544777)
    ·
      refine ⟨12377252083563825084408583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16503002778085100112544777 12377252083563825084408583)
      ·
        refine ⟨18565878125345737626612875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12377252083563825084408583 18565878125345737626612875)
        ·
          refine ⟨27848817188018606439919313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18565878125345737626612875 27848817188018606439919313)
          ·
            refine ⟨20886612891013954829939485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27848817188018606439919313 20886612891013954829939485)
            ·
              refine ⟨7832479834130233061227307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20886612891013954829939485 7832479834130233061227307)
              ·
                refine ⟨11748719751195349591840961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7832479834130233061227307 11748719751195349591840961)
                ·
                  refine ⟨8811539813396512193880721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11748719751195349591840961 8811539813396512193880721)
                  ·
                    refine ⟨6608654860047384145410541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8811539813396512193880721 6608654860047384145410541)
                    ·
                      refine ⟨2478245572517769054528953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608654860047384145410541 2478245572517769054528953)
                      ·
                        rfl

theorem cell23_4826366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4826366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826366 prefixEnd_4826366 := by exact prefixLift 4826366
  have htrace : WordTrace (prefixWord ++ tailWord_4826366) baseStart_4826366 baseEnd_4826366 := by
    simpa [prefixWord, tailWord_4826366, baseEnd_4826366] using wordTrace_append hprefix tailTrace_4826366
  have hstable : (prefixWord ++ tailWord_4826366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826366).length < 2 ^ (prefixWord ++ tailWord_4826366).sum := by decide
  have hdescent : baseEnd_4826366 < baseStart_4826366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826386 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 8]
def baseStart_4826386 : Nat := 118140960795 + 4826386 * 2 ^ 59
def prefixEnd_4826386 : Nat := 4983230072969 + 3 ^ 40 * 4826386 * 2
def baseEnd_4826386 : Nat := 275361760236762108475429

theorem tailTrace_4826386 : CollatzResearch.WordTrace tailWord_4826386 prefixEnd_4826386 275361760236762108475429 := by
  unfold tailWord_4826386
  simp only [CollatzResearch.WordTrace]
  refine ⟨44008189773208819487384753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117355172728556851966359341 44008189773208819487384753)
  ·
    refine ⟨33006142329906614615538565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44008189773208819487384753 33006142329906614615538565)
    ·
      refine ⟨6188651686857490240413481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33006142329906614615538565 6188651686857490240413481)
      ·
        refine ⟨4641488765143117680310111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6188651686857490240413481 4641488765143117680310111)
        ·
          refine ⟨6962233147714676520465167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641488765143117680310111 6962233147714676520465167)
          ·
            refine ⟨10443349721572014780697751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962233147714676520465167 10443349721572014780697751)
            ·
              refine ⟨15665024582358022171046627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443349721572014780697751 15665024582358022171046627)
              ·
                refine ⟨23497536873537033256569941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15665024582358022171046627 23497536873537033256569941)
                ·
                  refine ⟨275361760236762108475429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23497536873537033256569941 275361760236762108475429)
                  ·
                    rfl

theorem cell23_4826386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_4826386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826386 prefixEnd_4826386 := by exact prefixLift 4826386
  have htrace : WordTrace (prefixWord ++ tailWord_4826386) baseStart_4826386 baseEnd_4826386 := by
    simpa [prefixWord, tailWord_4826386, baseEnd_4826386] using wordTrace_append hprefix tailTrace_4826386
  have hstable : (prefixWord ++ tailWord_4826386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826386).length < 2 ^ (prefixWord ++ tailWord_4826386).sum := by decide
  have hdescent : baseEnd_4826386 < baseStart_4826386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826389 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_4826389 : Nat := 118140960795 + 4826389 * 2 ^ 59
def prefixEnd_4826389 : Nat := 4983230072969 + 3 ^ 40 * 4826389 * 2
def baseEnd_4826389 : Nat := 2478257382572822464541347

theorem tailTrace_4826389 : CollatzResearch.WordTrace tailWord_4826389 prefixEnd_4826389 2478257382572822464541347 := by
  unfold tailWord_4826389
  simp only [CollatzResearch.WordTrace]
  refine ⟨176032868511824409461898221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117355245674549606307932147 176032868511824409461898221)
  ·
    refine ⟨66012325691934153548211833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176032868511824409461898221 66012325691934153548211833)
    ·
      refine ⟨49509244268950615161158875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66012325691934153548211833 49509244268950615161158875)
      ·
        refine ⟨74263866403425922741738313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49509244268950615161158875 74263866403425922741738313)
        ·
          refine ⟨55697899802569442056303735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74263866403425922741738313 55697899802569442056303735)
          ·
            refine ⟨83546849703854163084455603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55697899802569442056303735 83546849703854163084455603)
            ·
              refine ⟨125320274555781244626683405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83546849703854163084455603 125320274555781244626683405)
              ·
                refine ⟨46995102958417966735006277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125320274555781244626683405 46995102958417966735006277)
                ·
                  refine ⟨8811581804703368762813677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46995102958417966735006277 8811581804703368762813677)
                  ·
                    refine ⟨3304343176763763286055129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8811581804703368762813677 3304343176763763286055129)
                    ·
                      refine ⟨2478257382572822464541347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304343176763763286055129 2478257382572822464541347)
                      ·
                        rfl

theorem cell23_4826389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_4826389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826389 prefixEnd_4826389 := by exact prefixLift 4826389
  have htrace : WordTrace (prefixWord ++ tailWord_4826389) baseStart_4826389 baseEnd_4826389 := by
    simpa [prefixWord, tailWord_4826389, baseEnd_4826389] using wordTrace_append hprefix tailTrace_4826389
  have hstable : (prefixWord ++ tailWord_4826389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826389).length < 2 ^ (prefixWord ++ tailWord_4826389).sum := by decide
  have hdescent : baseEnd_4826389 < baseStart_4826389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826413 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4826413 : Nat := 118140960795 + 4826413 * 2 ^ 59
def prefixEnd_4826413 : Nat := 4983230072969 + 3 ^ 40 * 4826413 * 2
def baseEnd_4826413 : Nat := 2478269706108530370641237

theorem tailTrace_4826413 : CollatzResearch.WordTrace tailWord_4826413 prefixEnd_4826413 2478269706108530370641237 := by
  unfold tailWord_4826413
  simp only [CollatzResearch.WordTrace]
  refine ⟨176033743863737461560771893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117355829242491641040514595 176033743863737461560771893)
  ·
    refine ⟨16503163487225387021322365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176033743863737461560771893 16503163487225387021322365)
    ·
      refine ⟨6188686307709520132995887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16503163487225387021322365 6188686307709520132995887)
      ·
        refine ⟨9283029461564280199493831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188686307709520132995887 9283029461564280199493831)
        ·
          refine ⟨13924544192346420299240747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9283029461564280199493831 13924544192346420299240747)
          ·
            refine ⟨20886816288519630448861121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13924544192346420299240747 20886816288519630448861121)
            ·
              refine ⟨15665112216389722836645841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20886816288519630448861121 15665112216389722836645841)
              ·
                refine ⟨11748834162292292127484381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15665112216389722836645841 11748834162292292127484381)
                ·
                  refine ⟨4405812810859609547806643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11748834162292292127484381 4405812810859609547806643)
                  ·
                    refine ⟨6608719216289414321709965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4405812810859609547806643 6608719216289414321709965)
                    ·
                      refine ⟨2478269706108530370641237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608719216289414321709965 2478269706108530370641237)
                      ·
                        rfl

theorem cell23_4826413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4826413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826413 prefixEnd_4826413 := by exact prefixLift 4826413
  have htrace : WordTrace (prefixWord ++ tailWord_4826413) baseStart_4826413 baseEnd_4826413 := by
    simpa [prefixWord, tailWord_4826413, baseEnd_4826413] using wordTrace_append hprefix tailTrace_4826413
  have hstable : (prefixWord ++ tailWord_4826413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826413).length < 2 ^ (prefixWord ++ tailWord_4826413).sum := by decide
  have hdescent : baseEnd_4826413 < baseStart_4826413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826419 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 4]
def baseStart_4826419 : Nat := 118140960795 + 4826419 * 2 ^ 59
def prefixEnd_4826419 : Nat := 4983230072969 + 3 ^ 40 * 4826419 * 2
def baseEnd_4826419 : Nat := 2478272786992457347166209

theorem tailTrace_4826419 : CollatzResearch.WordTrace tailWord_4826419 prefixEnd_4826419 2478272786992457347166209 := by
  unfold tailWord_4826419
  simp only [CollatzResearch.WordTrace]
  refine ⟨176033962701715724585490311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117355975134477149723660207 176033962701715724585490311)
  ·
    refine ⟨264050944052573586878235467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176033962701715724585490311 264050944052573586878235467)
    ·
      refine ⟨396076416078860380317353201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264050944052573586878235467 396076416078860380317353201)
      ·
        refine ⟨297057312059145285238014901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396076416078860380317353201 297057312059145285238014901)
        ·
          refine ⟨27849123005544870491063897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 297057312059145285238014901 27849123005544870491063897)
          ·
            refine ⟨20886842254158652868297923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27849123005544870491063897 20886842254158652868297923)
            ·
              refine ⟨31330263381237979302446885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20886842254158652868297923 31330263381237979302446885)
              ·
                refine ⟨5874424383982121119208791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31330263381237979302446885 5874424383982121119208791)
                ·
                  refine ⟨8811636575973181678813187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874424383982121119208791 8811636575973181678813187)
                  ·
                    refine ⟨13217454863959772518219781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8811636575973181678813187 13217454863959772518219781)
                    ·
                      refine ⟨2478272786992457347166209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13217454863959772518219781 2478272786992457347166209)
                      ·
                        rfl

theorem cell23_4826419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_4826419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826419 prefixEnd_4826419 := by exact prefixLift 4826419
  have htrace : WordTrace (prefixWord ++ tailWord_4826419) baseStart_4826419 baseEnd_4826419 := by
    simpa [prefixWord, tailWord_4826419, baseEnd_4826419] using wordTrace_append hprefix tailTrace_4826419
  have hstable : (prefixWord ++ tailWord_4826419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826419).length < 2 ^ (prefixWord ++ tailWord_4826419).sum := by decide
  have hdescent : baseEnd_4826419 < baseStart_4826419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826432 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_4826432 : Nat := 118140960795 + 4826432 * 2 ^ 59
def prefixEnd_4826432 : Nat := 4983230072969 + 3 ^ 40 * 4826432 * 2
def baseEnd_4826432 : Nat := 2478279462240965796303649

theorem tailTrace_4826432 : CollatzResearch.WordTrace tailWord_4826432 prefixEnd_4826432 2478279462240965796303649 := by
  unfold tailWord_4826432
  simp only [CollatzResearch.WordTrace]
  refine ⟨88017218425334313902856775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117356291233779085203809033 88017218425334313902856775)
  ·
    refine ⟨132025827638001470854285163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88017218425334313902856775 132025827638001470854285163)
    ·
      refine ⟨198038741457002206281427745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132025827638001470854285163 198038741457002206281427745)
      ·
        refine ⟨148529056092751654711070809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198038741457002206281427745 148529056092751654711070809)
        ·
          refine ⟨111396792069563741033303107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148529056092751654711070809 111396792069563741033303107)
          ·
            refine ⟨167095188104345611549954661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111396792069563741033303107 167095188104345611549954661)
            ·
              refine ⟨31330347769564802165616499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167095188104345611549954661 31330347769564802165616499)
              ·
                refine ⟨46995521654347203248424749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31330347769564802165616499 46995521654347203248424749)
                ·
                  refine ⟨17623320620380201218159281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46995521654347203248424749 17623320620380201218159281)
                  ·
                    refine ⟨13217490465285150913619461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17623320620380201218159281 13217490465285150913619461)
                    ·
                      refine ⟨2478279462240965796303649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13217490465285150913619461 2478279462240965796303649)
                      ·
                        rfl

theorem cell23_4826432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_4826432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826432 prefixEnd_4826432 := by exact prefixLift 4826432
  have htrace : WordTrace (prefixWord ++ tailWord_4826432) baseStart_4826432 baseEnd_4826432 := by
    simpa [prefixWord, tailWord_4826432, baseEnd_4826432] using wordTrace_append hprefix tailTrace_4826432
  have hstable : (prefixWord ++ tailWord_4826432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826432).length < 2 ^ (prefixWord ++ tailWord_4826432).sum := by decide
  have hdescent : baseEnd_4826432 < baseStart_4826432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826439 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_4826439 : Nat := 118140960795 + 4826439 * 2 ^ 59
def prefixEnd_4826439 : Nat := 4983230072969 + 3 ^ 40 * 4826439 * 2
def baseEnd_4826439 : Nat := 2478283056605547268916117

theorem tailTrace_4826439 : CollatzResearch.WordTrace tailWord_4826439 prefixEnd_4826439 2478283056605547268916117 := by
  unfold tailWord_4826439
  simp only [CollatzResearch.WordTrace]
  refine ⟨176034692161643268001218371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117356461441095512000812247 176034692161643268001218371)
  ·
    refine ⟨264052038242464902001827557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176034692161643268001218371 264052038242464902001827557)
    ·
      refine ⟨49509757170462169125342667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264052038242464902001827557 49509757170462169125342667)
      ·
        refine ⟨74264635755693253688014001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49509757170462169125342667 74264635755693253688014001)
        ·
          refine ⟨55698476816769940266010501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74264635755693253688014001 55698476816769940266010501)
          ·
            refine ⟨10443464403144363799876969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55698476816769940266010501 10443464403144363799876969)
            ·
              refine ⟨7832598302358272849907727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10443464403144363799876969 7832598302358272849907727)
              ·
                refine ⟨11748897453537409274861591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7832598302358272849907727 11748897453537409274861591)
                ·
                  refine ⟨17623346180306113912292387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11748897453537409274861591 17623346180306113912292387)
                  ·
                    refine ⟨26435019270459170868438581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17623346180306113912292387 26435019270459170868438581)
                    ·
                      refine ⟨2478283056605547268916117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26435019270459170868438581 2478283056605547268916117)
                      ·
                        rfl

theorem cell23_4826439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_4826439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826439 prefixEnd_4826439 := by exact prefixLift 4826439
  have htrace : WordTrace (prefixWord ++ tailWord_4826439) baseStart_4826439 baseEnd_4826439 := by
    simpa [prefixWord, tailWord_4826439, baseEnd_4826439] using wordTrace_append hprefix tailTrace_4826439
  have hstable : (prefixWord ++ tailWord_4826439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826439).length < 2 ^ (prefixWord ++ tailWord_4826439).sum := by decide
  have hdescent : baseEnd_4826439 < baseStart_4826439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826453 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4826453 : Nat := 118140960795 + 4826453 * 2 ^ 59
def prefixEnd_4826453 : Nat := 4983230072969 + 3 ^ 40 * 4826453 * 2
def baseEnd_4826453 : Nat := 2478290245334710214141053

theorem tailTrace_4826453 : CollatzResearch.WordTrace tailWord_4826453 prefixEnd_4826453 2478290245334710214141053 := by
  unfold tailWord_4826453
  simp only [CollatzResearch.WordTrace]
  refine ⟨176035202783592548392228013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117356801855728365594818675 176035202783592548392228013)
  ·
    refine ⟨66013201043847205647085505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176035202783592548392228013 66013201043847205647085505)
    ·
      refine ⟨49509900782885404235314129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66013201043847205647085505 49509900782885404235314129)
      ·
        refine ⟨37132425587164053176485597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49509900782885404235314129 37132425587164053176485597)
        ·
          refine ⟨13924659595186519941182099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37132425587164053176485597 13924659595186519941182099)
          ·
            refine ⟨20886989392779779911773149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13924659595186519941182099 20886989392779779911773149)
            ·
              refine ⟨7832621022292417466914931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20886989392779779911773149 7832621022292417466914931)
              ·
                refine ⟨11748931533438626200372397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7832621022292417466914931 11748931533438626200372397)
                ·
                  refine ⟨4405849325039484825139649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11748931533438626200372397 4405849325039484825139649)
                  ·
                    refine ⟨3304386993779613618854737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4405849325039484825139649 3304386993779613618854737)
                    ·
                      refine ⟨2478290245334710214141053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304386993779613618854737 2478290245334710214141053)
                      ·
                        rfl

theorem cell23_4826453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4826453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826453 prefixEnd_4826453 := by exact prefixLift 4826453
  have htrace : WordTrace (prefixWord ++ tailWord_4826453) baseStart_4826453 baseEnd_4826453 := by
    simpa [prefixWord, tailWord_4826453, baseEnd_4826453] using wordTrace_append hprefix tailTrace_4826453
  have hstable : (prefixWord ++ tailWord_4826453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826453).length < 2 ^ (prefixWord ++ tailWord_4826453).sum := by decide
  have hdescent : baseEnd_4826453 < baseStart_4826453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826454 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4826454 : Nat := 118140960795 + 4826454 * 2 ^ 59
def prefixEnd_4826454 : Nat := 4983230072969 + 3 ^ 40 * 4826454 * 2
def baseEnd_4826454 : Nat := 275365639868373856692061

theorem tailTrace_4826454 : CollatzResearch.WordTrace tailWord_4826454 prefixEnd_4826454 275365639868373856692061 := by
  unfold tailWord_4826454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11002202453536807847688401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117356826171059283708676277 11002202453536807847688401)
  ·
    refine ⟨8251651840152605885766301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11002202453536807847688401 8251651840152605885766301)
    ·
      refine ⟨3094369440057227207162363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8251651840152605885766301 3094369440057227207162363)
      ·
        refine ⟨4641554160085840810743545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094369440057227207162363 4641554160085840810743545)
        ·
          refine ⟨3481165620064380608057659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4641554160085840810743545 3481165620064380608057659)
          ·
            refine ⟨5221748430096570912086489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481165620064380608057659 5221748430096570912086489)
            ·
              refine ⟨3916311322572428184064867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5221748430096570912086489 3916311322572428184064867)
              ·
                refine ⟨5874466983858642276097301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916311322572428184064867 5874466983858642276097301)
                ·
                  refine ⟨275365639868373856692061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5874466983858642276097301 275365639868373856692061)
                  ·
                    rfl

theorem cell23_4826454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4826454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826454 prefixEnd_4826454 := by exact prefixLift 4826454
  have htrace : WordTrace (prefixWord ++ tailWord_4826454) baseStart_4826454 baseEnd_4826454 := by
    simpa [prefixWord, tailWord_4826454, baseEnd_4826454] using wordTrace_append hprefix tailTrace_4826454
  have hstable : (prefixWord ++ tailWord_4826454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826454).length < 2 ^ (prefixWord ++ tailWord_4826454).sum := by decide
  have hdescent : baseEnd_4826454 < baseStart_4826454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826469 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_4826469 : Nat := 118140960795 + 4826469 * 2 ^ 59
def prefixEnd_4826469 : Nat := 4983230072969 + 3 ^ 40 * 4826469 * 2
def baseEnd_4826469 : Nat := 2478298461025182151540979

theorem tailTrace_4826469 : CollatzResearch.WordTrace tailWord_4826469 prefixEnd_4826469 2478298461025182151540979 := by
  unfold tailWord_4826469
  simp only [CollatzResearch.WordTrace]
  refine ⟨176035786351534583124810461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117357190901023055416540307 176035786351534583124810461)
  ·
    refine ⟨66013419881825468671803923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176035786351534583124810461 66013419881825468671803923)
    ·
      refine ⟨99020129822738203007705885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66013419881825468671803923 99020129822738203007705885)
      ·
        refine ⟨37132548683526826127889707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99020129822738203007705885 37132548683526826127889707)
        ·
          refine ⟨55698823025290239191834561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37132548683526826127889707 55698823025290239191834561)
          ·
            refine ⟨41774117268967679393875921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55698823025290239191834561 41774117268967679393875921)
            ·
              refine ⟨31330587951725759545406941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41774117268967679393875921 31330587951725759545406941)
              ·
                refine ⟨11748970481897159829527603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31330587951725759545406941 11748970481897159829527603)
                ·
                  refine ⟨17623455722845739744291405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11748970481897159829527603 17623455722845739744291405)
                  ·
                    refine ⟨6608795896067152404109277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17623455722845739744291405 6608795896067152404109277)
                    ·
                      refine ⟨2478298461025182151540979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608795896067152404109277 2478298461025182151540979)
                      ·
                        rfl

theorem cell23_4826469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_4826469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826469 prefixEnd_4826469 := by exact prefixLift 4826469
  have htrace : WordTrace (prefixWord ++ tailWord_4826469) baseStart_4826469 baseEnd_4826469 := by
    simpa [prefixWord, tailWord_4826469, baseEnd_4826469] using wordTrace_append hprefix tailTrace_4826469
  have hstable : (prefixWord ++ tailWord_4826469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826469).length < 2 ^ (prefixWord ++ tailWord_4826469).sum := by decide
  have hdescent : baseEnd_4826469 < baseStart_4826469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826496 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 1, 3, 2]
def baseStart_4826496 : Nat := 118140960795 + 4826496 * 2 ^ 59
def prefixEnd_4826496 : Nat := 4983230072969 + 3 ^ 40 * 4826496 * 2
def baseEnd_4826496 : Nat := 2478312325002853545903355

theorem tailTrace_4826496 : CollatzResearch.WordTrace tailWord_4826496 prefixEnd_4826496 2478312325002853545903355 := by
  unfold tailWord_4826496
  simp only [CollatzResearch.WordTrace]
  refine ⟨88018385561218383368021671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117357847414957844490695561 88018385561218383368021671)
  ·
    refine ⟨132027578341827575052032507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88018385561218383368021671 132027578341827575052032507)
    ·
      refine ⟨198041367512741362578048761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132027578341827575052032507 198041367512741362578048761)
      ·
        refine ⟨148531025634556021933536571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198041367512741362578048761 148531025634556021933536571)
        ·
          refine ⟨222796538451834032900304857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148531025634556021933536571 222796538451834032900304857)
          ·
            refine ⟨167097403838875524675228643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222796538451834032900304857 167097403838875524675228643)
            ·
              refine ⟨250646105758313287012842965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167097403838875524675228643 250646105758313287012842965)
              ·
                refine ⟨5874518103710467664363507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 250646105758313287012842965 5874518103710467664363507)
                ·
                  refine ⟨8811777155565701496545261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874518103710467664363507 8811777155565701496545261)
                  ·
                    refine ⟨3304416433337138061204473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8811777155565701496545261 3304416433337138061204473)
                    ·
                      refine ⟨2478312325002853545903355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304416433337138061204473 2478312325002853545903355)
                      ·
                        rfl

theorem cell23_4826496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 3, 2].length) (baseStart_4826496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826496 prefixEnd_4826496 := by exact prefixLift 4826496
  have htrace : WordTrace (prefixWord ++ tailWord_4826496) baseStart_4826496 baseEnd_4826496 := by
    simpa [prefixWord, tailWord_4826496, baseEnd_4826496] using wordTrace_append hprefix tailTrace_4826496
  have hstable : (prefixWord ++ tailWord_4826496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826496).length < 2 ^ (prefixWord ++ tailWord_4826496).sum := by decide
  have hdescent : baseEnd_4826496 < baseStart_4826496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826503 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_4826503 : Nat := 118140960795 + 4826503 * 2 ^ 59
def prefixEnd_4826503 : Nat := 4983230072969 + 3 ^ 40 * 4826503 * 2
def baseEnd_4826503 : Nat := 2478315919367435018515823

theorem tailTrace_4826503 : CollatzResearch.WordTrace tailWord_4826503 prefixEnd_4826503 2478315919367435018515823 := by
  unfold tailWord_4826503
  simp only [CollatzResearch.WordTrace]
  refine ⟨176037026433411406931548163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117358017622274271287698775 176037026433411406931548163)
  ·
    refine ⟨264055539650117110397322245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176037026433411406931548163 264055539650117110397322245)
    ·
      refine ⟨49510413684396958199497921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264055539650117110397322245 49510413684396958199497921)
      ·
        refine ⟨37132810263297718649623441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49510413684396958199497921 37132810263297718649623441)
        ·
          refine ⟨27849607697473288987217581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37132810263297718649623441 27849607697473288987217581)
          ·
            refine ⟨10443602886552483370206593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27849607697473288987217581 10443602886552483370206593)
            ·
              refine ⟨7832702164914362527654945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10443602886552483370206593 7832702164914362527654945)
              ·
                refine ⟨5874526623685771895741209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7832702164914362527654945 5874526623685771895741209)
                ·
                  refine ⟨4405894967764328921805907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5874526623685771895741209 4405894967764328921805907)
                  ·
                    refine ⟨6608842451646493382708861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4405894967764328921805907 6608842451646493382708861)
                    ·
                      refine ⟨2478315919367435018515823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6608842451646493382708861 2478315919367435018515823)
                      ·
                        rfl

theorem cell23_4826503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_4826503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826503 prefixEnd_4826503 := by exact prefixLift 4826503
  have htrace : WordTrace (prefixWord ++ tailWord_4826503) baseStart_4826503 baseEnd_4826503 := by
    simpa [prefixWord, tailWord_4826503, baseEnd_4826503] using wordTrace_append hprefix tailTrace_4826503
  have hstable : (prefixWord ++ tailWord_4826503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826503).length < 2 ^ (prefixWord ++ tailWord_4826503).sum := by decide
  have hdescent : baseEnd_4826503 < baseStart_4826503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826613 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4826613 : Nat := 118140960795 + 4826613 * 2 ^ 59
def prefixEnd_4826613 : Nat := 4983230072969 + 3 ^ 40 * 4826613 * 2
def baseEnd_4826613 : Nat := 826124134079809862713439

theorem tailTrace_4826613 : CollatzResearch.WordTrace tailWord_4826613 prefixEnd_4826613 826124134079809862713439 := by
  unfold tailWord_4826613
  simp only [CollatzResearch.WordTrace]
  refine ⟨176041038463012895718052493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117360692308675263812034995 176041038463012895718052493)
  ·
    refine ⟨66015389423629835894269685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176041038463012895718052493 66015389423629835894269685)
    ·
      refine ⟨6188942758465297115087783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66015389423629835894269685 6188942758465297115087783)
      ·
        refine ⟨9283414137697945672631675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188942758465297115087783 9283414137697945672631675)
        ·
          refine ⟨13925121206546918508947513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9283414137697945672631675 13925121206546918508947513)
          ·
            refine ⟨10443840904910188881710635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13925121206546918508947513 10443840904910188881710635)
            ·
              refine ⟨15665761357365283322565953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443840904910188881710635 15665761357365283322565953)
              ·
                refine ⟨11749321018023962491924465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15665761357365283322565953 11749321018023962491924465)
                ·
                  refine ⟨8811990763517971868943349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11749321018023962491924465 8811990763517971868943349)
                  ·
                    refine ⟨826124134079809862713439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8811990763517971868943349 826124134079809862713439)
                    ·
                      rfl

theorem cell23_4826613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4826613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826613 prefixEnd_4826613 := by exact prefixLift 4826613
  have htrace : WordTrace (prefixWord ++ tailWord_4826613) baseStart_4826613 baseEnd_4826613 := by
    simpa [prefixWord, tailWord_4826613, baseEnd_4826613] using wordTrace_append hprefix tailTrace_4826613
  have hstable : (prefixWord ++ tailWord_4826613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826613).length < 2 ^ (prefixWord ++ tailWord_4826613).sum := by decide
  have hdescent : baseEnd_4826613 < baseStart_4826613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826616 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_4826616 : Nat := 118140960795 + 4826616 * 2 ^ 59
def prefixEnd_4826616 : Nat := 4983230072969 + 3 ^ 40 * 4826616 * 2
def baseEnd_4826616 : Nat := 2478373942681393076402803

theorem tailTrace_4826616 : CollatzResearch.WordTrace tailWord_4826616 prefixEnd_4826616 2478373942681393076402803 := by
  unfold tailWord_4826616
  simp only [CollatzResearch.WordTrace]
  refine ⟨88020573941001013615205851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117360765254668018153607801 88020573941001013615205851)
  ·
    refine ⟨132030860911501520422808777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88020573941001013615205851 132030860911501520422808777)
    ·
      refine ⟨99023145683626140317106583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132030860911501520422808777 99023145683626140317106583)
      ·
        refine ⟨148534718525439210475659875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99023145683626140317106583 148534718525439210475659875)
        ·
          refine ⟨222802077788158815713489813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148534718525439210475659875 222802077788158815713489813)
          ·
            refine ⟨10443847396319944486569835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 222802077788158815713489813 10443847396319944486569835)
            ·
              refine ⟨15665771094479916729854753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443847396319944486569835 15665771094479916729854753)
              ·
                refine ⟨11749328320859937547391065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15665771094479916729854753 11749328320859937547391065)
                ·
                  refine ⟨8811996240644953160543299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11749328320859937547391065 8811996240644953160543299)
                  ·
                    refine ⟨13217994360967429740814949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8811996240644953160543299 13217994360967429740814949)
                    ·
                      refine ⟨2478373942681393076402803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13217994360967429740814949 2478373942681393076402803)
                      ·
                        rfl

theorem cell23_4826616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_4826616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826616 prefixEnd_4826616 := by exact prefixLift 4826616
  have htrace : WordTrace (prefixWord ++ tailWord_4826616) baseStart_4826616 baseEnd_4826616 := by
    simpa [prefixWord, tailWord_4826616, baseEnd_4826616] using wordTrace_append hprefix tailTrace_4826616
  have hstable : (prefixWord ++ tailWord_4826616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826616).length < 2 ^ (prefixWord ++ tailWord_4826616).sum := by decide
  have hdescent : baseEnd_4826616 < baseStart_4826616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826653 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_4826653 : Nat := 118140960795 + 4826653 * 2 ^ 59
def prefixEnd_4826653 : Nat := 4983230072969 + 3 ^ 40 * 4826653 * 2
def baseEnd_4826653 : Nat := 2478392941465609431640133

theorem tailTrace_4826653 : CollatzResearch.WordTrace tailWord_4826653 prefixEnd_4826653 2478392941465609431640133 := by
  unfold tailWord_4826653
  simp only [CollatzResearch.WordTrace]
  refine ⟨176042497382867982549508613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117361664921911988366339075 176042497382867982549508613)
  ·
    refine ⟨33007968259287746728032865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176042497382867982549508613 33007968259287746728032865)
    ·
      refine ⟨24755976194465810046024649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33007968259287746728032865 24755976194465810046024649)
      ·
        refine ⟨18566982145849357534518487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24755976194465810046024649 18566982145849357534518487)
        ·
          refine ⟨27850473218774036301777731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18566982145849357534518487 27850473218774036301777731)
          ·
            refine ⟨41775709828161054452666597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27850473218774036301777731 41775709828161054452666597)
            ·
              refine ⟨7832945592780197709874987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41775709828161054452666597 7832945592780197709874987)
              ·
                refine ⟨11749418389170296564812481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7832945592780197709874987 11749418389170296564812481)
                ·
                  refine ⟨8812063791877722423609361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11749418389170296564812481 8812063791877722423609361)
                  ·
                    refine ⟨6609047843908291817707021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8812063791877722423609361 6609047843908291817707021)
                    ·
                      refine ⟨2478392941465609431640133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6609047843908291817707021 2478392941465609431640133)
                      ·
                        rfl

theorem cell23_4826653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_4826653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826653 prefixEnd_4826653 := by exact prefixLift 4826653
  have htrace : WordTrace (prefixWord ++ tailWord_4826653) baseStart_4826653 baseEnd_4826653 := by
    simpa [prefixWord, tailWord_4826653, baseEnd_4826653] using wordTrace_append hprefix tailTrace_4826653
  have hstable : (prefixWord ++ tailWord_4826653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826653).length < 2 ^ (prefixWord ++ tailWord_4826653).sum := by decide
  have hdescent : baseEnd_4826653 < baseStart_4826653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826677 : List Nat := [1, 3, 3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_4826677 : Nat := 118140960795 + 4826677 * 2 ^ 59
def prefixEnd_4826677 : Nat := 4983230072969 + 3 ^ 40 * 4826677 * 2
def baseEnd_4826677 : Nat := 826135088333772445913341

theorem tailTrace_4826677 : CollatzResearch.WordTrace tailWord_4826677 prefixEnd_4826677 826135088333772445913341 := by
  unfold tailWord_4826677
  simp only [CollatzResearch.WordTrace]
  refine ⟨176043372734781034648382285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117362248489854023098921523 176043372734781034648382285)
  ·
    refine ⟨66016264775542887993143357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176043372734781034648382285 66016264775542887993143357)
    ·
      refine ⟨24756099290828582997428759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66016264775542887993143357 24756099290828582997428759)
      ·
        refine ⟨37134148936242874496143139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24756099290828582997428759 37134148936242874496143139)
        ·
          refine ⟨55701223404364311744214709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37134148936242874496143139 55701223404364311744214709)
          ·
            refine ⟨5221989694159154226020129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55701223404364311744214709 5221989694159154226020129)
            ·
              refine ⟨3916492270619365669515097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5221989694159154226020129 3916492270619365669515097)
              ·
                refine ⟨2937369202964524252136323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3916492270619365669515097 2937369202964524252136323)
                ·
                  refine ⟨4406053804446786378204485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937369202964524252136323 4406053804446786378204485)
                  ·
                    refine ⟨826135088333772445913341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4406053804446786378204485 826135088333772445913341)
                    ·
                      rfl

theorem cell23_4826677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_4826677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826677 prefixEnd_4826677 := by exact prefixLift 4826677
  have htrace : WordTrace (prefixWord ++ tailWord_4826677) baseStart_4826677 baseEnd_4826677 := by
    simpa [prefixWord, tailWord_4826677, baseEnd_4826677] using wordTrace_append hprefix tailTrace_4826677
  have hstable : (prefixWord ++ tailWord_4826677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826677).length < 2 ^ (prefixWord ++ tailWord_4826677).sum := by decide
  have hdescent : baseEnd_4826677 < baseStart_4826677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826719 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_4826719 : Nat := 118140960795 + 4826719 * 2 ^ 59
def prefixEnd_4826719 : Nat := 4983230072969 + 3 ^ 40 * 4826719 * 2
def baseEnd_4826719 : Nat := 2478426831188806173414829

theorem tailTrace_4826719 : CollatzResearch.WordTrace tailWord_4826719 prefixEnd_4826719 2478426831188806173414829 := by
  unfold tailWord_4826719
  simp only [CollatzResearch.WordTrace]
  refine ⟨176044904600628875821411211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117363269733752583880940807 176044904600628875821411211)
  ·
    refine ⟨264067356900943313732116817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176044904600628875821411211 264067356900943313732116817)
    ·
      refine ⟨198050517675707485299087613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264067356900943313732116817 198050517675707485299087613)
      ·
        refine ⟨74268944128390306987157855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198050517675707485299087613 74268944128390306987157855)
        ·
          refine ⟨111403416192585460480736783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74268944128390306987157855 111403416192585460480736783)
          ·
            refine ⟨167105124288878190721105175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111403416192585460480736783 167105124288878190721105175)
            ·
              refine ⟨250657686433317286081657763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167105124288878190721105175 250657686433317286081657763)
              ·
                refine ⟨375986529649975929122486645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250657686433317286081657763 375986529649975929122486645)
                ·
                  refine ⟨35248737154685243355233123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375986529649975929122486645 35248737154685243355233123)
                  ·
                    refine ⟨52873105732027865032849685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35248737154685243355233123 52873105732027865032849685)
                    ·
                      refine ⟨2478426831188806173414829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52873105732027865032849685 2478426831188806173414829)
                      ·
                        rfl

theorem cell23_4826719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_4826719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826719 prefixEnd_4826719 := by exact prefixLift 4826719
  have htrace : WordTrace (prefixWord ++ tailWord_4826719) baseStart_4826719 baseEnd_4826719 := by
    simpa [prefixWord, tailWord_4826719, baseEnd_4826719] using wordTrace_append hprefix tailTrace_4826719
  have hstable : (prefixWord ++ tailWord_4826719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826719).length < 2 ^ (prefixWord ++ tailWord_4826719).sum := by decide
  have hdescent : baseEnd_4826719 < baseStart_4826719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826723 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 4]
def baseStart_4826723 : Nat := 118140960795 + 4826723 * 2 ^ 59
def prefixEnd_4826723 : Nat := 4983230072969 + 3 ^ 40 * 4826723 * 2
def baseEnd_4826723 : Nat := 2478428885111424157764811

theorem tailTrace_4826723 : CollatzResearch.WordTrace tailWord_4826723 prefixEnd_4826723 2478428885111424157764811 := by
  unfold tailWord_4826723
  simp only [CollatzResearch.WordTrace]
  refine ⟨176045050492614384504556823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117363366995076256336371215 176045050492614384504556823)
  ·
    refine ⟨264067575738921576756835235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176045050492614384504556823 264067575738921576756835235)
    ·
      refine ⟨396101363608382365135252853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264067575738921576756835235 396101363608382365135252853)
      ·
        refine ⟨37134502838285846731429955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 396101363608382365135252853 37134502838285846731429955)
        ·
          refine ⟨55701754257428770097144933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37134502838285846731429955 55701754257428770097144933)
          ·
            refine ⟨10444078923267894393214675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55701754257428770097144933 10444078923267894393214675)
            ·
              refine ⟨15666118384901841589822013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10444078923267894393214675 15666118384901841589822013)
              ·
                refine ⟨5874794394338190596183255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15666118384901841589822013 5874794394338190596183255)
                ·
                  refine ⟨8812191591507285894274883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874794394338190596183255 8812191591507285894274883)
                  ·
                    refine ⟨13218287387260928841412325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8812191591507285894274883 13218287387260928841412325)
                    ·
                      refine ⟨2478428885111424157764811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13218287387260928841412325 2478428885111424157764811)
                      ·
                        rfl

theorem cell23_4826723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_4826723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826723 prefixEnd_4826723 := by exact prefixLift 4826723
  have htrace : WordTrace (prefixWord ++ tailWord_4826723) baseStart_4826723 baseEnd_4826723 := by
    simpa [prefixWord, tailWord_4826723, baseEnd_4826723] using wordTrace_append hprefix tailTrace_4826723
  have hstable : (prefixWord ++ tailWord_4826723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826723).length < 2 ^ (prefixWord ++ tailWord_4826723).sum := by decide
  have hdescent : baseEnd_4826723 < baseStart_4826723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826753 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_4826753 : Nat := 118140960795 + 4826753 * 2 ^ 59
def prefixEnd_4826753 : Nat := 4983230072969 + 3 ^ 40 * 4826753 * 2
def baseEnd_4826753 : Nat := 2478444289531059040389673

theorem tailTrace_4826753 : CollatzResearch.WordTrace tailWord_4826753 prefixEnd_4826753 2478444289531059040389673 := by
  unfold tailWord_4826753
  simp only [CollatzResearch.WordTrace]
  refine ⟨176046144682505699628148913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117364096455003799752099275 176046144682505699628148913)
  ·
    refine ⟨132034608511879274721111685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176046144682505699628148913 132034608511879274721111685)
    ·
      refine ⟨24756489095977364010208441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132034608511879274721111685 24756489095977364010208441)
      ·
        refine ⟨18567366821983023007656331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24756489095977364010208441 18567366821983023007656331)
        ·
          refine ⟨27851050232974534511484497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18567366821983023007656331 27851050232974534511484497)
          ·
            refine ⟨20888287674730900883613373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27851050232974534511484497 20888287674730900883613373)
            ·
              refine ⟨7833107878024087831355015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20888287674730900883613373 7833107878024087831355015)
              ·
                refine ⟨11749661817036131747032523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7833107878024087831355015 11749661817036131747032523)
                ·
                  refine ⟨17624492725554197620548785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11749661817036131747032523 17624492725554197620548785)
                  ·
                    refine ⟨13218369544165648215411589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17624492725554197620548785 13218369544165648215411589)
                    ·
                      refine ⟨2478444289531059040389673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13218369544165648215411589 2478444289531059040389673)
                      ·
                        rfl

theorem cell23_4826753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_4826753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826753 prefixEnd_4826753 := by exact prefixLift 4826753
  have htrace : WordTrace (prefixWord ++ tailWord_4826753) baseStart_4826753 baseEnd_4826753 := by
    simpa [prefixWord, tailWord_4826753, baseEnd_4826753] using wordTrace_append hprefix tailTrace_4826753
  have hstable : (prefixWord ++ tailWord_4826753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826753).length < 2 ^ (prefixWord ++ tailWord_4826753).sum := by decide
  have hdescent : baseEnd_4826753 < baseStart_4826753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826807 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 2, 1, 3]
def baseStart_4826807 : Nat := 118140960795 + 4826807 * 2 ^ 59
def prefixEnd_4826807 : Nat := 4983230072969 + 3 ^ 40 * 4826807 * 2
def baseEnd_4826807 : Nat := 2478472017486401829114425

theorem tailTrace_4826807 : CollatzResearch.WordTrace tailWord_4826807 prefixEnd_4826807 2478472017486401829114425 := by
  unfold tailWord_4826807
  simp only [CollatzResearch.WordTrace]
  refine ⟨176048114224310066850614675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117365409482873377900409783 176048114224310066850614675)
  ·
    refine ⟨264072171336465100275922013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176048114224310066850614675 264072171336465100275922013)
    ·
      refine ⟨99027064251174412603470755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264072171336465100275922013 99027064251174412603470755)
      ·
        refine ⟨148540596376761618905206133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99027064251174412603470755 148540596376761618905206133)
        ·
          refine ⟨13925680910321401772363075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148540596376761618905206133 13925680910321401772363075)
          ·
            refine ⟨20888521365482102658544613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13925680910321401772363075 20888521365482102658544613)
            ·
              refine ⟨3916597756027894248477115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20888521365482102658544613 3916597756027894248477115)
              ·
                refine ⟨5874896634041841372715673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916597756027894248477115 5874896634041841372715673)
                ·
                  refine ⟨4406172475531381029536755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5874896634041841372715673 4406172475531381029536755)
                  ·
                    refine ⟨6609258713297071544305133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4406172475531381029536755 6609258713297071544305133)
                    ·
                      refine ⟨2478472017486401829114425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6609258713297071544305133 2478472017486401829114425)
                      ·
                        rfl

theorem cell23_4826807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_4826807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826807 prefixEnd_4826807 := by exact prefixLift 4826807
  have htrace : WordTrace (prefixWord ++ tailWord_4826807) baseStart_4826807 baseEnd_4826807 := by
    simpa [prefixWord, tailWord_4826807, baseEnd_4826807] using wordTrace_append hprefix tailTrace_4826807
  have hstable : (prefixWord ++ tailWord_4826807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826807).length < 2 ^ (prefixWord ++ tailWord_4826807).sum := by decide
  have hdescent : baseEnd_4826807 < baseStart_4826807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826816 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_4826816 : Nat := 118140960795 + 4826816 * 2 ^ 59
def prefixEnd_4826816 : Nat := 4983230072969 + 3 ^ 40 * 4826816 * 2
def baseEnd_4826816 : Nat := 2478476638812292293901883

theorem tailTrace_4826816 : CollatzResearch.WordTrace tailWord_4826816 prefixEnd_4826816 2478476638812292293901883 := by
  unfold tailWord_4826816
  simp only [CollatzResearch.WordTrace]
  refine ⟨88024221240638730693846151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117365628320851640925128201 88024221240638730693846151)
  ·
    refine ⟨132036331860958096040769227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88024221240638730693846151 132036331860958096040769227)
    ·
      refine ⟨198054497791437144061153841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132036331860958096040769227 198054497791437144061153841)
      ·
        refine ⟨148540873343577858045865381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198054497791437144061153841 148540873343577858045865381)
        ·
          refine ⟨27851413751920848383599759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148540873343577858045865381 27851413751920848383599759)
          ·
            refine ⟨41777120627881272575399639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27851413751920848383599759 41777120627881272575399639)
            ·
              refine ⟨62665680941821908863099459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41777120627881272575399639 62665680941821908863099459)
              ·
                refine ⟨93998521412732863294649189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62665680941821908863099459 93998521412732863294649189)
                ·
                  refine ⟨17624722764887411867746723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93998521412732863294649189 17624722764887411867746723)
                  ·
                    refine ⟨26437084147331117801620085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17624722764887411867746723 26437084147331117801620085)
                    ·
                      refine ⟨2478476638812292293901883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26437084147331117801620085 2478476638812292293901883)
                      ·
                        rfl

theorem cell23_4826816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_4826816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826816 prefixEnd_4826816 := by exact prefixLift 4826816
  have htrace : WordTrace (prefixWord ++ tailWord_4826816) baseStart_4826816 baseEnd_4826816 := by
    simpa [prefixWord, tailWord_4826816, baseEnd_4826816] using wordTrace_append hprefix tailTrace_4826816
  have hstable : (prefixWord ++ tailWord_4826816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826816).length < 2 ^ (prefixWord ++ tailWord_4826816).sum := by decide
  have hdescent : baseEnd_4826816 < baseStart_4826816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826830 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_4826830 : Nat := 118140960795 + 4826830 * 2 ^ 59
def prefixEnd_4826830 : Nat := 4983230072969 + 3 ^ 40 * 4826830 * 2
def baseEnd_4826830 : Nat := 2478483827541455239126819

theorem tailTrace_4826830 : CollatzResearch.WordTrace tailWord_4826830 prefixEnd_4826830 2478483827541455239126819 := by
  unfold tailWord_4826830
  simp only [CollatzResearch.WordTrace]
  refine ⟨22006119137903342722337743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117365968735484494519134629 22006119137903342722337743)
  ·
    refine ⟨33009178706855014083506615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22006119137903342722337743 33009178706855014083506615)
    ·
      refine ⟨49513768060282521125259923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33009178706855014083506615 49513768060282521125259923)
      ·
        refine ⟨74270652090423781687889885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49513768060282521125259923 74270652090423781687889885)
        ·
          refine ⟨27851494533908918132958707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74270652090423781687889885 27851494533908918132958707)
          ·
            refine ⟨41777241800863377199438061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27851494533908918132958707 41777241800863377199438061)
            ·
              refine ⟨15666465675323766449789273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41777241800863377199438061 15666465675323766449789273)
              ·
                refine ⟨11749849256492824837341955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15666465675323766449789273 11749849256492824837341955)
                ·
                  refine ⟨17624773884739237256012933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11749849256492824837341955 17624773884739237256012933)
                  ·
                    refine ⟨3304645103388606985502425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17624773884739237256012933 3304645103388606985502425)
                    ·
                      refine ⟨2478483827541455239126819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304645103388606985502425 2478483827541455239126819)
                      ·
                        rfl

theorem cell23_4826830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_4826830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826830 prefixEnd_4826830 := by exact prefixLift 4826830
  have htrace : WordTrace (prefixWord ++ tailWord_4826830) baseStart_4826830 baseEnd_4826830 := by
    simpa [prefixWord, tailWord_4826830, baseEnd_4826830] using wordTrace_append hprefix tailTrace_4826830
  have hstable : (prefixWord ++ tailWord_4826830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826830).length < 2 ^ (prefixWord ++ tailWord_4826830).sum := by decide
  have hdescent : baseEnd_4826830 < baseStart_4826830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826834 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_4826834 : Nat := 118140960795 + 4826834 * 2 ^ 59
def prefixEnd_4826834 : Nat := 4983230072969 + 3 ^ 40 * 4826834 * 2
def baseEnd_4826834 : Nat := 2478485881464073223476801

theorem tailTrace_4826834 : CollatzResearch.WordTrace tailWord_4826834 prefixEnd_4826834 2478485881464073223476801 := by
  unfold tailWord_4826834
  simp only [CollatzResearch.WordTrace]
  refine ⟨44012274748803062615461889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117366065996808166974565037 44012274748803062615461889)
  ·
    refine ⟨33009206061602296961596417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44012274748803062615461889 33009206061602296961596417)
    ·
      refine ⟨24756904546201722721197313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33009206061602296961596417 24756904546201722721197313)
      ·
        refine ⟨18567678409651292040897985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24756904546201722721197313 18567678409651292040897985)
        ·
          refine ⟨13925758807238469030673489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18567678409651292040897985 13925758807238469030673489)
          ·
            refine ⟨10444319105428851773005117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13925758807238469030673489 10444319105428851773005117)
            ·
              refine ⟨3916619664535819414876919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10444319105428851773005117 3916619664535819414876919)
              ·
                refine ⟨5874929496803729122315379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916619664535819414876919 5874929496803729122315379)
                ·
                  refine ⟨8812394245205593683473069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874929496803729122315379 8812394245205593683473069)
                  ·
                    refine ⟨3304647841952097631302401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8812394245205593683473069 3304647841952097631302401)
                    ·
                      refine ⟨2478485881464073223476801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304647841952097631302401 2478485881464073223476801)
                      ·
                        rfl

theorem cell23_4826834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_4826834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826834 prefixEnd_4826834 := by exact prefixLift 4826834
  have htrace : WordTrace (prefixWord ++ tailWord_4826834) baseStart_4826834 baseEnd_4826834 := by
    simpa [prefixWord, tailWord_4826834, baseEnd_4826834] using wordTrace_append hprefix tailTrace_4826834
  have hstable : (prefixWord ++ tailWord_4826834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826834).length < 2 ^ (prefixWord ++ tailWord_4826834).sum := by decide
  have hdescent : baseEnd_4826834 < baseStart_4826834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826847 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 2, 2, 2]
def baseStart_4826847 : Nat := 118140960795 + 4826847 * 2 ^ 59
def prefixEnd_4826847 : Nat := 4983230072969 + 3 ^ 40 * 4826847 * 2
def baseEnd_4826847 : Nat := 2478492556712581672614241

theorem tailTrace_4826847 : CollatzResearch.WordTrace tailWord_4826847 prefixEnd_4826847 2478492556712581672614241 := by
  unfold tailWord_4826847
  simp only [CollatzResearch.WordTrace]
  refine ⟨176049573144165153682070795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117366382096110102454713863 176049573144165153682070795)
  ·
    refine ⟨264074359716247730523106193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176049573144165153682070795 264074359716247730523106193)
    ·
      refine ⟨198055769787185797892329645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264074359716247730523106193 198055769787185797892329645)
      ·
        refine ⟨74270913670194674209623617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198055769787185797892329645 74270913670194674209623617)
        ·
          refine ⟨55703185252646005657217713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74270913670194674209623617 55703185252646005657217713)
          ·
            refine ⟨41777388939484504242913285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55703185252646005657217713 41777388939484504242913285)
            ·
              refine ⟨7833260426153344545546241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41777388939484504242913285 7833260426153344545546241)
              ·
                refine ⟨5874945319615008409159681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7833260426153344545546241 5874945319615008409159681)
                ·
                  refine ⟨4406208989711256306869761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5874945319615008409159681 4406208989711256306869761)
                  ·
                    refine ⟨3304656742283442230152321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4406208989711256306869761 3304656742283442230152321)
                    ·
                      refine ⟨2478492556712581672614241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304656742283442230152321 2478492556712581672614241)
                      ·
                        rfl

theorem cell23_4826847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_4826847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826847 prefixEnd_4826847 := by exact prefixLift 4826847
  have htrace : WordTrace (prefixWord ++ tailWord_4826847) baseStart_4826847 baseEnd_4826847 := by
    simpa [prefixWord, tailWord_4826847, baseEnd_4826847] using wordTrace_append hprefix tailTrace_4826847
  have hstable : (prefixWord ++ tailWord_4826847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826847).length < 2 ^ (prefixWord ++ tailWord_4826847).sum := by decide
  have hdescent : baseEnd_4826847 < baseStart_4826847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826863 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_4826863 : Nat := 118140960795 + 4826863 * 2 ^ 59
def prefixEnd_4826863 : Nat := 4983230072969 + 3 ^ 40 * 4826863 * 2
def baseEnd_4826863 : Nat := 2478500772403053610014167

theorem tailTrace_4826863 : CollatzResearch.WordTrace tailWord_4826863 prefixEnd_4826863 2478500772403053610014167 := by
  unfold tailWord_4826863
  simp only [CollatzResearch.WordTrace]
  refine ⟨176050156712107188414653243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117366771141404792276435495 176050156712107188414653243)
  ·
    refine ⟨264075235068160782621979865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176050156712107188414653243 264075235068160782621979865)
    ·
      refine ⟨198056426301120586966484899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264075235068160782621979865 198056426301120586966484899)
      ·
        refine ⟨297084639451680880449727349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198056426301120586966484899 297084639451680880449727349)
        ·
          refine ⟨27851684948595082542161939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 297084639451680880449727349 27851684948595082542161939)
          ·
            refine ⟨41777527422892623813242909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27851684948595082542161939 41777527422892623813242909)
            ·
              refine ⟨15666572783584733929966091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41777527422892623813242909 15666572783584733929966091)
              ·
                refine ⟨23499859175377100894949137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15666572783584733929966091 23499859175377100894949137)
                ·
                  refine ⟨17624894381532825671211853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23499859175377100894949137 17624894381532825671211853)
                  ·
                    refine ⟨6609335393074809626704445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17624894381532825671211853 6609335393074809626704445)
                    ·
                      refine ⟨2478500772403053610014167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6609335393074809626704445 2478500772403053610014167)
                      ·
                        rfl

theorem cell23_4826863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_4826863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826863 prefixEnd_4826863 := by exact prefixLift 4826863
  have htrace : WordTrace (prefixWord ++ tailWord_4826863) baseStart_4826863 baseEnd_4826863 := by
    simpa [prefixWord, tailWord_4826863, baseEnd_4826863] using wordTrace_append hprefix tailTrace_4826863
  have hstable : (prefixWord ++ tailWord_4826863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826863).length < 2 ^ (prefixWord ++ tailWord_4826863).sum := by decide
  have hdescent : baseEnd_4826863 < baseStart_4826863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826883 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 2, 5]
def baseStart_4826883 : Nat := 118140960795 + 4826883 * 2 ^ 59
def prefixEnd_4826883 : Nat := 4983230072969 + 3 ^ 40 * 4826883 * 2
def baseEnd_4826883 : Nat := 826170347338714510588025

theorem tailTrace_4826883 : CollatzResearch.WordTrace tailWord_4826883 prefixEnd_4826883 826170347338714510588025 := by
  unfold tailWord_4826883
  simp only [CollatzResearch.WordTrace]
  refine ⟨176050886172034731830381303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117367257448023154553587535 176050886172034731830381303)
  ·
    refine ⟨264076329258052097745571955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176050886172034731830381303 264076329258052097745571955)
    ·
      refine ⟨396114493887078146618357933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264076329258052097745571955 396114493887078146618357933)
      ·
        refine ⟨148542935207654304981884225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396114493887078146618357933 148542935207654304981884225)
        ·
          refine ⟨111407201405740728736413169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148542935207654304981884225 111407201405740728736413169)
          ·
            refine ⟨83555401054305546552309877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111407201405740728736413169 83555401054305546552309877)
            ·
              refine ⟨7833318848841144989279051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83555401054305546552309877 7833318848841144989279051)
              ·
                refine ⟨11749978273261717483918577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7833318848841144989279051 11749978273261717483918577)
                ·
                  refine ⟨8812483704946288112938933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11749978273261717483918577 8812483704946288112938933)
                  ·
                    refine ⟨826170347338714510588025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8812483704946288112938933 826170347338714510588025)
                    ·
                      rfl

theorem cell23_4826883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 5].length) (baseStart_4826883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826883 prefixEnd_4826883 := by exact prefixLift 4826883
  have htrace : WordTrace (prefixWord ++ tailWord_4826883) baseStart_4826883 baseEnd_4826883 := by
    simpa [prefixWord, tailWord_4826883, baseEnd_4826883] using wordTrace_append hprefix tailTrace_4826883
  have hstable : (prefixWord ++ tailWord_4826883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826883).length < 2 ^ (prefixWord ++ tailWord_4826883).sum := by decide
  have hdescent : baseEnd_4826883 < baseStart_4826883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826887 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 5]
def baseStart_4826887 : Nat := 118140960795 + 4826887 * 2 ^ 59
def prefixEnd_4826887 : Nat := 4983230072969 + 3 ^ 40 * 4826887 * 2
def baseEnd_4826887 : Nat := 275390343993195724012673

theorem tailTrace_4826887 : CollatzResearch.WordTrace tailWord_4826887 prefixEnd_4826887 275390343993195724012673 := by
  unfold tailWord_4826887
  simp only [CollatzResearch.WordTrace]
  refine ⟨176051032064020240513526915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117367354709346827009017943 176051032064020240513526915)
  ·
    refine ⟨264076548096030360770290373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176051032064020240513526915 264076548096030360770290373)
    ·
      refine ⟨49514352768005692644429445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 264076548096030360770290373 49514352768005692644429445)
      ·
        refine ⟨9283941144001067370830521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49514352768005692644429445 9283941144001067370830521)
        ·
          refine ⟨6962955858000800528122891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9283941144001067370830521 6962955858000800528122891)
          ·
            refine ⟨10444433787001200792184337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962955858000800528122891 10444433787001200792184337)
            ·
              refine ⟨7833325340250900594138253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10444433787001200792184337 7833325340250900594138253)
              ·
                refine ⟨2937497002594087722801845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7833325340250900594138253 2937497002594087722801845)
                ·
                  refine ⟨275390343993195724012673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2937497002594087722801845 275390343993195724012673)
                  ·
                    rfl

theorem cell23_4826887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 5].length) (baseStart_4826887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826887 prefixEnd_4826887 := by exact prefixLift 4826887
  have htrace : WordTrace (prefixWord ++ tailWord_4826887) baseStart_4826887 baseEnd_4826887 := by
    simpa [prefixWord, tailWord_4826887, baseEnd_4826887] using wordTrace_append hprefix tailTrace_4826887
  have hstable : (prefixWord ++ tailWord_4826887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826887).length < 2 ^ (prefixWord ++ tailWord_4826887).sum := by decide
  have hdescent : baseEnd_4826887 < baseStart_4826887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826930 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_4826930 : Nat := 118140960795 + 4826930 * 2 ^ 59
def prefixEnd_4826930 : Nat := 4983230072969 + 3 ^ 40 * 4826930 * 2
def baseEnd_4826930 : Nat := 826178391868968282625453

theorem tailTrace_4826930 : CollatzResearch.WordTrace tailWord_4826930 prefixEnd_4826930 826178391868968282625453 := by
  unfold tailWord_4826930
  simp only [CollatzResearch.WordTrace]
  refine ⟨44013150100716114714335561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117368400268576305904894829 44013150100716114714335561)
  ·
    refine ⟨33009862575537086035751671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44013150100716114714335561 33009862575537086035751671)
    ·
      refine ⟨49514793863305629053627507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33009862575537086035751671 49514793863305629053627507)
      ·
        refine ⟨74272190794958443580441261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49514793863305629053627507 74272190794958443580441261)
        ·
          refine ⟨27852071548109416342665473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74272190794958443580441261 27852071548109416342665473)
          ·
            refine ⟨20889053661082062256999105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27852071548109416342665473 20889053661082062256999105)
            ·
              refine ⟨15666790245811546692749329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20889053661082062256999105 15666790245811546692749329)
              ·
                refine ⟨11750092684358660019561997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15666790245811546692749329 11750092684358660019561997)
                ·
                  refine ⟨4406284756634497507335749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11750092684358660019561997 4406284756634497507335749)
                  ·
                    refine ⟨826178391868968282625453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4406284756634497507335749 826178391868968282625453)
                    ·
                      rfl

theorem cell23_4826930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_4826930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826930 prefixEnd_4826930 := by exact prefixLift 4826930
  have htrace : WordTrace (prefixWord ++ tailWord_4826930) baseStart_4826930 baseEnd_4826930 := by
    simpa [prefixWord, tailWord_4826930, baseEnd_4826930] using wordTrace_append hprefix tailTrace_4826930
  have hstable : (prefixWord ++ tailWord_4826930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826930).length < 2 ^ (prefixWord ++ tailWord_4826930).sum := by decide
  have hdescent : baseEnd_4826930 < baseStart_4826930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826947 : List Nat := [1, 1, 1, 3, 1, 5, 3, 3, 1, 4]
def baseStart_4826947 : Nat := 118140960795 + 4826947 * 2 ^ 59
def prefixEnd_4826947 : Nat := 4983230072969 + 3 ^ 40 * 4826947 * 2
def baseEnd_4826947 : Nat := 826181301592677093787927

theorem tailTrace_4826947 : CollatzResearch.WordTrace tailWord_4826947 prefixEnd_4826947 826181301592677093787927 := by
  unfold tailWord_4826947
  simp only [CollatzResearch.WordTrace]
  refine ⟨176053220443802870760711095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117368813629201913840474063 176053220443802870760711095)
  ·
    refine ⟨264079830665704306141066643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176053220443802870760711095 264079830665704306141066643)
    ·
      refine ⟨396119745998556459211599965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264079830665704306141066643 396119745998556459211599965)
      ·
        refine ⟨148544904749458672204349987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396119745998556459211599965 148544904749458672204349987)
        ·
          refine ⟨222817357124188008306524981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148544904749458672204349987 222817357124188008306524981)
          ·
            refine ⟨20889127230392625778736717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222817357124188008306524981 20889127230392625778736717)
            ·
              refine ⟨7833422711397234667026269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20889127230392625778736717 7833422711397234667026269)
              ·
                refine ⟨2937533516773963000134851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7833422711397234667026269 2937533516773963000134851)
                ·
                  refine ⟨4406300275160944500202277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937533516773963000134851 4406300275160944500202277)
                  ·
                    refine ⟨826181301592677093787927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4406300275160944500202277 826181301592677093787927)
                    ·
                      rfl

theorem cell23_4826947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 1, 4].length) (baseStart_4826947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826947 prefixEnd_4826947 := by exact prefixLift 4826947
  have htrace : WordTrace (prefixWord ++ tailWord_4826947) baseStart_4826947 baseEnd_4826947 := by
    simpa [prefixWord, tailWord_4826947, baseEnd_4826947] using wordTrace_append hprefix tailTrace_4826947
  have hstable : (prefixWord ++ tailWord_4826947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826947).length < 2 ^ (prefixWord ++ tailWord_4826947).sum := by decide
  have hdescent : baseEnd_4826947 < baseStart_4826947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4826957 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4826957 : Nat := 118140960795 + 4826957 * 2 ^ 59
def prefixEnd_4826957 : Nat := 4983230072969 + 3 ^ 40 * 4826957 * 2
def baseEnd_4826957 : Nat := 2478549039584576242238735

theorem tailTrace_4826957 : CollatzResearch.WordTrace tailWord_4826957 prefixEnd_4826957 2478549039584576242238735 := by
  unfold tailWord_4826957
  simp only [CollatzResearch.WordTrace]
  refine ⟨176053585173766642468575125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117369056782511094979050083 176053585173766642468575125)
  ·
    refine ⟨8252511805020311365714459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 176053585173766642468575125 8252511805020311365714459)
    ·
      refine ⟨12378767707530467048571689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8252511805020311365714459 12378767707530467048571689)
      ·
        refine ⟨9284075780647850286428767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12378767707530467048571689 9284075780647850286428767)
        ·
          refine ⟨13926113670971775429643151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9284075780647850286428767 13926113670971775429643151)
          ·
            refine ⟨20889170506457663144464727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13926113670971775429643151 20889170506457663144464727)
            ·
              refine ⟨31333755759686494716697091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20889170506457663144464727 31333755759686494716697091)
              ·
                refine ⟨47000633639529742075045637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31333755759686494716697091 47000633639529742075045637)
                ·
                  refine ⟨8812618807411826639071057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47000633639529742075045637 8812618807411826639071057)
                  ·
                    refine ⟨6609464105558869979303293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8812618807411826639071057 6609464105558869979303293)
                    ·
                      refine ⟨2478549039584576242238735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6609464105558869979303293 2478549039584576242238735)
                      ·
                        rfl

theorem cell23_4826957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4826957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4826957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4826957 prefixEnd_4826957 := by exact prefixLift 4826957
  have htrace : WordTrace (prefixWord ++ tailWord_4826957) baseStart_4826957 baseEnd_4826957 := by
    simpa [prefixWord, tailWord_4826957, baseEnd_4826957] using wordTrace_append hprefix tailTrace_4826957
  have hstable : (prefixWord ++ tailWord_4826957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4826957).length < 2 ^ (prefixWord ++ tailWord_4826957).sum := by decide
  have hdescent : baseEnd_4826957 < baseStart_4826957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4826957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827033 : List Nat := [1, 2, 1, 2, 1, 3, 5, 8]
def baseStart_4827033 : Nat := 118140960795 + 4827033 * 2 ^ 59
def prefixEnd_4827033 : Nat := 4983230072969 + 3 ^ 40 * 4827033 * 2
def baseEnd_4827033 : Nat := 91799557930159923884755

theorem tailTrace_4827033 : CollatzResearch.WordTrace tailWord_4827033 prefixEnd_4827033 91799557930159923884755 := by
  unfold tailWord_4827033
  simp only [CollatzResearch.WordTrace]
  refine ⟨176056357121491307448341753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117370904747660871632227835 176056357121491307448341753)
  ·
    refine ⟨132042267841118480586256315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176056357121491307448341753 132042267841118480586256315)
    ·
      refine ⟨198063401761677720879384473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132042267841118480586256315 198063401761677720879384473)
      ·
        refine ⟨148547551321258290659538355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198063401761677720879384473 148547551321258290659538355)
        ·
          refine ⟨222821326981887435989307533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148547551321258290659538355 222821326981887435989307533)
          ·
            refine ⟨83557997618207788495990325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222821326981887435989307533 83557997618207788495990325)
            ·
              refine ⟨7833562276706980171499093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83557997618207788495990325 7833562276706980171499093)
              ·
                refine ⟨91799557930159923884755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7833562276706980171499093 91799557930159923884755)
                ·
                  rfl

theorem cell23_4827033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 8].length) (baseStart_4827033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827033 prefixEnd_4827033 := by exact prefixLift 4827033
  have htrace : WordTrace (prefixWord ++ tailWord_4827033) baseStart_4827033 baseEnd_4827033 := by
    simpa [prefixWord, tailWord_4827033, baseEnd_4827033] using wordTrace_append hprefix tailTrace_4827033
  have hstable : (prefixWord ++ tailWord_4827033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827033).length < 2 ^ (prefixWord ++ tailWord_4827033).sum := by decide
  have hdescent : baseEnd_4827033 < baseStart_4827033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827037 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4827037 : Nat := 118140960795 + 4827037 * 2 ^ 59
def prefixEnd_4827037 : Nat := 4983230072969 + 3 ^ 40 * 4827037 * 2
def baseEnd_4827037 : Nat := 826196706012311976412789

theorem tailTrace_4827037 : CollatzResearch.WordTrace tailWord_4827037 prefixEnd_4827037 826196706012311976412789 := by
  unfold tailWord_4827037
  simp only [CollatzResearch.WordTrace]
  refine ⟨176056503013476816131487365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117371002008984544087658243 176056503013476816131487365)
  ·
    refine ⟨33010594315026903024653881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176056503013476816131487365 33010594315026903024653881)
    ·
      refine ⟨24757945736270177268490411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33010594315026903024653881 24757945736270177268490411)
      ·
        refine ⟨37136918604405265902735617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24757945736270177268490411 37136918604405265902735617)
        ·
          refine ⟨27852688953303949427051713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37136918604405265902735617 27852688953303949427051713)
          ·
            refine ⟨20889516714977962070288785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27852688953303949427051713 20889516714977962070288785)
            ·
              refine ⟨15667137536233471552716589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20889516714977962070288785 15667137536233471552716589)
              ·
                refine ⟨5875176576087551832268721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15667137536233471552716589 5875176576087551832268721)
                ·
                  refine ⟨4406382432065663874201541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5875176576087551832268721 4406382432065663874201541)
                  ·
                    refine ⟨826196706012311976412789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4406382432065663874201541 826196706012311976412789)
                    ·
                      rfl

theorem cell23_4827037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4827037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827037 prefixEnd_4827037 := by exact prefixLift 4827037
  have htrace : WordTrace (prefixWord ++ tailWord_4827037) baseStart_4827037 baseEnd_4827037 := by
    simpa [prefixWord, tailWord_4827037, baseEnd_4827037] using wordTrace_append hprefix tailTrace_4827037
  have hstable : (prefixWord ++ tailWord_4827037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827037).length < 2 ^ (prefixWord ++ tailWord_4827037).sum := by decide
  have hdescent : baseEnd_4827037 < baseStart_4827037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827044 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_4827044 : Nat := 118140960795 + 4827044 * 2 ^ 59
def prefixEnd_4827044 : Nat := 4983230072969 + 3 ^ 40 * 4827044 * 2
def baseEnd_4827044 : Nat := 2478593712401517401850835

theorem tailTrace_4827044 : CollatzResearch.WordTrace tailWord_4827044 prefixEnd_4827044 2478593712401517401850835 := by
  unfold tailWord_4827044
  simp only [CollatzResearch.WordTrace]
  refine ⟨88028379162225728163496093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117371172216300970884661457 88028379162225728163496093)
  ·
    refine ⟨33010642185834648061311035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88028379162225728163496093 33010642185834648061311035)
    ·
      refine ⟨49515963278751972091966553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33010642185834648061311035 49515963278751972091966553)
      ·
        refine ⟨37136972459063979068974915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49515963278751972091966553 37136972459063979068974915)
        ·
          refine ⟨55705458688595968603462373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37136972459063979068974915 55705458688595968603462373)
          ·
            refine ⟨10444773504111744113149195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55705458688595968603462373 10444773504111744113149195)
            ·
              refine ⟨15667160256167616169723793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10444773504111744113149195 15667160256167616169723793)
              ·
                refine ⟨11750370192125712127292845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15667160256167616169723793 11750370192125712127292845)
                ·
                  refine ⟨4406388822047142047734817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11750370192125712127292845 4406388822047142047734817)
                  ·
                    refine ⟨3304791616535356535801113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4406388822047142047734817 3304791616535356535801113)
                    ·
                      refine ⟨2478593712401517401850835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304791616535356535801113 2478593712401517401850835)
                      ·
                        rfl

theorem cell23_4827044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_4827044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827044 prefixEnd_4827044 := by exact prefixLift 4827044
  have htrace : WordTrace (prefixWord ++ tailWord_4827044) baseStart_4827044 baseEnd_4827044 := by
    simpa [prefixWord, tailWord_4827044, baseEnd_4827044] using wordTrace_append hprefix tailTrace_4827044
  have hstable : (prefixWord ++ tailWord_4827044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827044).length < 2 ^ (prefixWord ++ tailWord_4827044).sum := by decide
  have hdescent : baseEnd_4827044 < baseStart_4827044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827047 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4827047 : Nat := 118140960795 + 4827047 * 2 ^ 59
def prefixEnd_4827047 : Nat := 4983230072969 + 3 ^ 40 * 4827047 * 2
def baseEnd_4827047 : Nat := 2478595252843480890113321

theorem tailTrace_4827047 : CollatzResearch.WordTrace tailWord_4827047 prefixEnd_4827047 2478595252843480890113321 := by
  unfold tailWord_4827047
  simp only [CollatzResearch.WordTrace]
  refine ⟨176056867743440587839351395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117371245162293725226234263 176056867743440587839351395)
  ·
    refine ⟨264085301615160881759027093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176056867743440587839351395 264085301615160881759027093)
    ·
      refine ⟨12378998513210666332454395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264085301615160881759027093 12378998513210666332454395)
      ·
        refine ⟨18568497769815999498681593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12378998513210666332454395 18568497769815999498681593)
        ·
          refine ⟨13926373327361999624011195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18568497769815999498681593 13926373327361999624011195)
          ·
            refine ⟨20889559991042999436016793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13926373327361999624011195 20889559991042999436016793)
            ·
              refine ⟨15667169993282249577012595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20889559991042999436016793 15667169993282249577012595)
              ·
                refine ⟨23500754989923374365518893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15667169993282249577012595 23500754989923374365518893)
                ·
                  refine ⟨8812783121221265387069585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23500754989923374365518893 8812783121221265387069585)
                  ·
                    refine ⟨6609587340915949040302189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8812783121221265387069585 6609587340915949040302189)
                    ·
                      refine ⟨2478595252843480890113321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6609587340915949040302189 2478595252843480890113321)
                      ·
                        rfl

theorem cell23_4827047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4827047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827047 prefixEnd_4827047 := by exact prefixLift 4827047
  have htrace : WordTrace (prefixWord ++ tailWord_4827047) baseStart_4827047 baseEnd_4827047 := by
    simpa [prefixWord, tailWord_4827047, baseEnd_4827047] using wordTrace_append hprefix tailTrace_4827047
  have hstable : (prefixWord ++ tailWord_4827047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827047).length < 2 ^ (prefixWord ++ tailWord_4827047).sum := by decide
  have hdescent : baseEnd_4827047 < baseStart_4827047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827048 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4827048 : Nat := 118140960795 + 4827048 * 2 ^ 59
def prefixEnd_4827048 : Nat := 4983230072969 + 3 ^ 40 * 4827048 * 2
def baseEnd_4827048 : Nat := 2478595766324135386200817

theorem tailTrace_4827048 : CollatzResearch.WordTrace tailWord_4827048 prefixEnd_4827048 2478595766324135386200817 := by
  unfold tailWord_4827048
  simp only [CollatzResearch.WordTrace]
  refine ⟨88028452108218482505068899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117371269477624643340091865 88028452108218482505068899)
  ·
    refine ⟨132042678162327723757603349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88028452108218482505068899 132042678162327723757603349)
    ·
      refine ⟨6189500538859112051137657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132042678162327723757603349 6189500538859112051137657)
      ·
        refine ⟨4642125404144334038353243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6189500538859112051137657 4642125404144334038353243)
        ·
          refine ⟨6963188106216501057529865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642125404144334038353243 6963188106216501057529865)
          ·
            refine ⟨5222391079662375793147399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6963188106216501057529865 5222391079662375793147399)
            ·
              refine ⟨7833586619493563689721099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222391079662375793147399 7833586619493563689721099)
              ·
                refine ⟨11750379929240345534581649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7833586619493563689721099 11750379929240345534581649)
                ·
                  refine ⟨8812784946930259150936237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11750379929240345534581649 8812784946930259150936237)
                  ·
                    refine ⟨3304794355098847181601089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8812784946930259150936237 3304794355098847181601089)
                    ·
                      refine ⟨2478595766324135386200817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304794355098847181601089 2478595766324135386200817)
                      ·
                        rfl

theorem cell23_4827048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4827048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827048 prefixEnd_4827048 := by exact prefixLift 4827048
  have htrace : WordTrace (prefixWord ++ tailWord_4827048) baseStart_4827048 baseEnd_4827048 := by
    simpa [prefixWord, tailWord_4827048, baseEnd_4827048] using wordTrace_append hprefix tailTrace_4827048
  have hstable : (prefixWord ++ tailWord_4827048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827048).length < 2 ^ (prefixWord ++ tailWord_4827048).sum := by decide
  have hdescent : baseEnd_4827048 < baseStart_4827048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827061 : List Nat := [1, 3, 3, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_4827061 : Nat := 118140960795 + 4827061 * 2 ^ 59
def prefixEnd_4827061 : Nat := 4983230072969 + 3 ^ 40 * 4827061 * 2
def baseEnd_4827061 : Nat := 2478602441572643835338257

theorem tailTrace_4827061 : CollatzResearch.WordTrace tailWord_4827061 prefixEnd_4827061 2478602441572643835338257 := by
  unfold tailWord_4827061
  simp only [CollatzResearch.WordTrace]
  refine ⟨176057378365389868230361037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117371585576926578820240691 176057378365389868230361037)
  ·
    refine ⟨66021516887021200586385389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176057378365389868230361037 66021516887021200586385389)
    ·
      refine ⟨24758068832632950219894521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66021516887021200586385389 24758068832632950219894521)
      ·
        refine ⟨18568551624474712664920891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24758068832632950219894521 18568551624474712664920891)
        ·
          refine ⟨27852827436712068997381337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18568551624474712664920891 27852827436712068997381337)
          ·
            refine ⟨20889620577534051748036003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27852827436712068997381337 20889620577534051748036003)
            ·
              refine ⟨31334430866301077622054005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20889620577534051748036003 31334430866301077622054005)
              ·
                refine ⟨2937602893715726027067563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31334430866301077622054005 2937602893715726027067563)
                ·
                  refine ⟨4406404340573589040601345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937602893715726027067563 4406404340573589040601345)
                  ·
                    refine ⟨3304803255430191780451009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4406404340573589040601345 3304803255430191780451009)
                    ·
                      refine ⟨2478602441572643835338257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3304803255430191780451009 2478602441572643835338257)
                      ·
                        rfl

theorem cell23_4827061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_4827061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827061 prefixEnd_4827061 := by exact prefixLift 4827061
  have htrace : WordTrace (prefixWord ++ tailWord_4827061) baseStart_4827061 baseEnd_4827061 := by
    simpa [prefixWord, tailWord_4827061, baseEnd_4827061] using wordTrace_append hprefix tailTrace_4827061
  have hstable : (prefixWord ++ tailWord_4827061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827061).length < 2 ^ (prefixWord ++ tailWord_4827061).sum := by decide
  have hdescent : baseEnd_4827061 < baseStart_4827061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827077 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_4827077 : Nat := 118140960795 + 4827077 * 2 ^ 59
def prefixEnd_4827077 : Nat := 4983230072969 + 3 ^ 40 * 4827077 * 2
def baseEnd_4827077 : Nat := 2478610657263115772738183

theorem tailTrace_4827077 : CollatzResearch.WordTrace tailWord_4827077 prefixEnd_4827077 2478610657263115772738183 := by
  unfold tailWord_4827077
  simp only [CollatzResearch.WordTrace]
  refine ⟨176057961933331902962943485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117371974622221268641962323 176057961933331902962943485)
  ·
    refine ⟨66021735724999463611103807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176057961933331902962943485 66021735724999463611103807)
    ·
      refine ⟨99032603587499195416655711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66021735724999463611103807 99032603587499195416655711)
      ·
        refine ⟨148548905381248793124983567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99032603587499195416655711 148548905381248793124983567)
        ·
          refine ⟨222823358071873189687475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148548905381248793124983567 222823358071873189687475351)
          ·
            refine ⟨334235037107809784531213027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222823358071873189687475351 334235037107809784531213027)
            ·
              refine ⟨501352555661714676796819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334235037107809784531213027 501352555661714676796819541)
              ·
                refine ⟨5875225261660718868712729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 501352555661714676796819541 5875225261660718868712729)
                ·
                  refine ⟨4406418946245539151534547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5875225261660718868712729 4406418946245539151534547)
                  ·
                    refine ⟨6609628419368308727301821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4406418946245539151534547 6609628419368308727301821)
                    ·
                      refine ⟨2478610657263115772738183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6609628419368308727301821 2478610657263115772738183)
                      ·
                        rfl

theorem cell23_4827077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_4827077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827077 prefixEnd_4827077 := by exact prefixLift 4827077
  have htrace : WordTrace (prefixWord ++ tailWord_4827077) baseStart_4827077 baseEnd_4827077 := by
    simpa [prefixWord, tailWord_4827077, baseEnd_4827077] using wordTrace_append hprefix tailTrace_4827077
  have hstable : (prefixWord ++ tailWord_4827077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827077).length < 2 ^ (prefixWord ++ tailWord_4827077).sum := by decide
  have hdescent : baseEnd_4827077 < baseStart_4827077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827123 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 9]
def baseStart_4827123 : Nat := 118140960795 + 4827123 * 2 ^ 59
def prefixEnd_4827123 : Nat := 4983230072969 + 3 ^ 40 * 4827123 * 2
def baseEnd_4827123 : Nat := 275403808597024732529219

theorem tailTrace_4827123 : CollatzResearch.WordTrace tailWord_4827123 prefixEnd_4827123 275403808597024732529219 := by
  unfold tailWord_4827123
  simp only [CollatzResearch.WordTrace]
  refine ⟨176059639691165252819118023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117373093127443501879412015 176059639691165252819118023)
  ·
    refine ⟨264089459536747879228677035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176059639691165252819118023 264089459536747879228677035)
    ·
      refine ⟨396134189305121818843015553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264089459536747879228677035 396134189305121818843015553)
      ·
        refine ⟨297100641978841364132261665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396134189305121818843015553 297100641978841364132261665)
        ·
          refine ⟨222825481484131023099196249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297100641978841364132261665 222825481484131023099196249)
          ·
            refine ⟨167119111113098267324397187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222825481484131023099196249 167119111113098267324397187)
            ·
              refine ⟨250678666669647400986595781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167119111113098267324397187 250678666669647400986595781)
              ·
                refine ⟨47002250000558887684986709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250678666669647400986595781 47002250000558887684986709)
                ·
                  refine ⟨275403808597024732529219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47002250000558887684986709 275403808597024732529219)
                  ·
                    rfl

theorem cell23_4827123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 9].length) (baseStart_4827123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827123 prefixEnd_4827123 := by exact prefixLift 4827123
  have htrace : WordTrace (prefixWord ++ tailWord_4827123) baseStart_4827123 baseEnd_4827123 := by
    simpa [prefixWord, tailWord_4827123, baseEnd_4827123] using wordTrace_append hprefix tailTrace_4827123
  have hstable : (prefixWord ++ tailWord_4827123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827123).length < 2 ^ (prefixWord ++ tailWord_4827123).sum := by decide
  have hdescent : baseEnd_4827123 < baseStart_4827123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827224 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_4827224 : Nat := 118140960795 + 4827224 * 2 ^ 59
def prefixEnd_4827224 : Nat := 4983230072969 + 3 ^ 40 * 4827224 * 2
def baseEnd_4827224 : Nat := 2478686138919326697600007

theorem tailTrace_4827224 : CollatzResearch.WordTrace tailWord_4827224 prefixEnd_4827224 2478686138919326697600007 := by
  unfold tailWord_4827224
  simp only [CollatzResearch.WordTrace]
  refine ⟨88031661731899673534272363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117375548975866231379029817 88031661731899673534272363)
  ·
    refine ⟨132047492597849510301408545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88031661731899673534272363 132047492597849510301408545)
    ·
      refine ⟨99035619448387132726056409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132047492597849510301408545 99035619448387132726056409)
      ·
        refine ⟨74276714586290349544542307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99035619448387132726056409 74276714586290349544542307)
        ·
          refine ⟨111415071879435524316813461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74276714586290349544542307 111415071879435524316813461)
          ·
            refine ⟨5222581494348540202350631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111415071879435524316813461 5222581494348540202350631)
            ·
              refine ⟨7833872241522810303525947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222581494348540202350631 7833872241522810303525947)
              ·
                refine ⟨11750808362284215455288921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7833872241522810303525947 11750808362284215455288921)
                ·
                  refine ⟨8813106271713161591466691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11750808362284215455288921 8813106271713161591466691)
                  ·
                    refine ⟨13219659407569742387200037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8813106271713161591466691 13219659407569742387200037)
                    ·
                      refine ⟨2478686138919326697600007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13219659407569742387200037 2478686138919326697600007)
                      ·
                        rfl

theorem cell23_4827224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_4827224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827224 prefixEnd_4827224 := by exact prefixLift 4827224
  have htrace : WordTrace (prefixWord ++ tailWord_4827224) baseStart_4827224 baseEnd_4827224 := by
    simpa [prefixWord, tailWord_4827224, baseEnd_4827224] using wordTrace_append hprefix tailTrace_4827224
  have hstable : (prefixWord ++ tailWord_4827224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827224).length < 2 ^ (prefixWord ++ tailWord_4827224).sum := by decide
  have hdescent : baseEnd_4827224 < baseStart_4827224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827247 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 6]
def baseStart_4827247 : Nat := 118140960795 + 4827247 * 2 ^ 59
def prefixEnd_4827247 : Nat := 4983230072969 + 3 ^ 40 * 4827247 * 2
def baseEnd_4827247 : Nat := 275410883219375567512489

theorem tailTrace_4827247 : CollatzResearch.WordTrace tailWord_4827247 prefixEnd_4827247 275410883219375567512489 := by
  unfold tailWord_4827247
  simp only [CollatzResearch.WordTrace]
  refine ⟨176064162342716021996631995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117376108228477347997754663 176064162342716021996631995)
  ·
    refine ⟨264096243514074032994947993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176064162342716021996631995 264096243514074032994947993)
    ·
      refine ⟨198072182635555524746210995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264096243514074032994947993 198072182635555524746210995)
      ·
        refine ⟨297108273953333287119316493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198072182635555524746210995 297108273953333287119316493)
        ·
          refine ⟨111415602732499982669743685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297108273953333287119316493 111415602732499982669743685)
          ·
            refine ⟨20890425512343746750576941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111415602732499982669743685 20890425512343746750576941)
            ·
              refine ⟨7833909567128905031466353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20890425512343746750576941 7833909567128905031466353)
              ·
                refine ⟨5875432175346678773599765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7833909567128905031466353 5875432175346678773599765)
                ·
                  refine ⟨275410883219375567512489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5875432175346678773599765 275410883219375567512489)
                  ·
                    rfl

theorem cell23_4827247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 6].length) (baseStart_4827247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827247 prefixEnd_4827247 := by exact prefixLift 4827247
  have htrace : WordTrace (prefixWord ++ tailWord_4827247) baseStart_4827247 baseEnd_4827247 := by
    simpa [prefixWord, tailWord_4827247, baseEnd_4827247] using wordTrace_append hprefix tailTrace_4827247
  have hstable : (prefixWord ++ tailWord_4827247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827247).length < 2 ^ (prefixWord ++ tailWord_4827247).sum := by decide
  have hdescent : baseEnd_4827247 < baseStart_4827247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827327 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_4827327 : Nat := 118140960795 + 4827327 * 2 ^ 59
def prefixEnd_4827327 : Nat := 4983230072969 + 3 ^ 40 * 4827327 * 2
def baseEnd_4827327 : Nat := 2478739027426739794612033

theorem tailTrace_4827327 : CollatzResearch.WordTrace tailWord_4827327 prefixEnd_4827327 2478739027426739794612033 := by
  unfold tailWord_4827327
  simp only [CollatzResearch.WordTrace]
  refine ⟨176067080182426195659544235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117378053454950797106362823 176067080182426195659544235)
  ·
    refine ⟨264100620273639293489316353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176067080182426195659544235 264100620273639293489316353)
    ·
      refine ⟨198075465205229470116987265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264100620273639293489316353 198075465205229470116987265)
      ·
        refine ⟨148556598903922102587740449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198075465205229470116987265 148556598903922102587740449)
        ·
          refine ⟨111417449177941576940805337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148556598903922102587740449 111417449177941576940805337)
          ·
            refine ⟨83563086883456182705604003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111417449177941576940805337 83563086883456182705604003)
            ·
              refine ⟨125344630325184274058406005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83563086883456182705604003 125344630325184274058406005)
              ·
                refine ⟨11751059092986025692975563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125344630325184274058406005 11751059092986025692975563)
                ·
                  refine ⟨17626588639479038539463345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11751059092986025692975563 17626588639479038539463345)
                  ·
                    refine ⟨13219941479609278904597509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17626588639479038539463345 13219941479609278904597509)
                    ·
                      refine ⟨2478739027426739794612033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13219941479609278904597509 2478739027426739794612033)
                      ·
                        rfl

theorem cell23_4827327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_4827327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827327 prefixEnd_4827327 := by exact prefixLift 4827327
  have htrace : WordTrace (prefixWord ++ tailWord_4827327) baseStart_4827327 baseEnd_4827327 := by
    simpa [prefixWord, tailWord_4827327, baseEnd_4827327] using wordTrace_append hprefix tailTrace_4827327
  have hstable : (prefixWord ++ tailWord_4827327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827327).length < 2 ^ (prefixWord ++ tailWord_4827327).sum := by decide
  have hdescent : baseEnd_4827327 < baseStart_4827327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827365 : List Nat := [1, 3, 1, 4, 2, 2, 1, 4, 1, 2, 2]
def baseStart_4827365 : Nat := 118140960795 + 4827365 * 2 ^ 59
def prefixEnd_4827365 : Nat := 4983230072969 + 3 ^ 40 * 4827365 * 2
def baseEnd_4827365 : Nat := 2478758539691610645936859

theorem tailTrace_4827365 : CollatzResearch.WordTrace tailWord_4827365 prefixEnd_4827365 2478758539691610645936859 := by
  unfold tailWord_4827365
  simp only [CollatzResearch.WordTrace]
  refine ⟨176068466156288528149427549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117378977437525685432951699 176068466156288528149427549)
  ·
    refine ⟨66025674808608198056035331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176068466156288528149427549 66025674808608198056035331)
    ·
      refine ⟨99038512212912297084052997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66025674808608198056035331 99038512212912297084052997)
      ·
        refine ⟨18569721039921055703259937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99038512212912297084052997 18569721039921055703259937)
        ·
          refine ⟨13927290779940791777444953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18569721039921055703259937 13927290779940791777444953)
          ·
            refine ⟨10445468084955593833083715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13927290779940791777444953 10445468084955593833083715)
            ·
              refine ⟨15668202127433390749625573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10445468084955593833083715 15668202127433390749625573)
              ·
                refine ⟨2937787898893760765554795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15668202127433390749625573 2937787898893760765554795)
                ·
                  refine ⟨4406681848340641148332193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937787898893760765554795 4406681848340641148332193)
                  ·
                    refine ⟨3305011386255480861249145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4406681848340641148332193 3305011386255480861249145)
                    ·
                      refine ⟨2478758539691610645936859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305011386255480861249145 2478758539691610645936859)
                      ·
                        rfl

theorem cell23_4827365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_4827365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827365 prefixEnd_4827365 := by exact prefixLift 4827365
  have htrace : WordTrace (prefixWord ++ tailWord_4827365) baseStart_4827365 baseEnd_4827365 := by
    simpa [prefixWord, tailWord_4827365, baseEnd_4827365] using wordTrace_append hprefix tailTrace_4827365
  have hstable : (prefixWord ++ tailWord_4827365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827365).length < 2 ^ (prefixWord ++ tailWord_4827365).sum := by decide
  have hdescent : baseEnd_4827365 < baseStart_4827365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827391 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 1, 3, 2]
def baseStart_4827391 : Nat := 118140960795 + 4827391 * 2 ^ 59
def prefixEnd_4827391 : Nat := 4983230072969 + 3 ^ 40 * 4827391 * 2
def baseEnd_4827391 : Nat := 2478771890188627544211739

theorem tailTrace_4827391 : CollatzResearch.WordTrace tailWord_4827391 prefixEnd_4827391 2478771890188627544211739 := by
  unfold tailWord_4827391
  simp only [CollatzResearch.WordTrace]
  refine ⟨176069414454194334589874027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117379609636129556393249351 176069414454194334589874027)
  ·
    refine ⟨264104121681291501884811041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176069414454194334589874027 264104121681291501884811041)
    ·
      refine ⟨198078091260968626413608281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264104121681291501884811041 198078091260968626413608281)
      ·
        refine ⟨148558568445726469810206211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198078091260968626413608281 148558568445726469810206211)
        ·
          refine ⟨222837852668589704715309317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148558568445726469810206211 222837852668589704715309317)
          ·
            refine ⟨41782097375360569634120497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 222837852668589704715309317 41782097375360569634120497)
            ·
              refine ⟨31336573031520427225590373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41782097375360569634120497 31336573031520427225590373)
              ·
                refine ⟨5875607443410080104798195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31336573031520427225590373 5875607443410080104798195)
                ·
                  refine ⟨8813411165115120157197293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5875607443410080104798195 8813411165115120157197293)
                  ·
                    refine ⟨3305029186918170058948985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8813411165115120157197293 3305029186918170058948985)
                    ·
                      refine ⟨2478771890188627544211739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3305029186918170058948985 2478771890188627544211739)
                      ·
                        rfl

theorem cell23_4827391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_4827391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827391 prefixEnd_4827391 := by exact prefixLift 4827391
  have htrace : WordTrace (prefixWord ++ tailWord_4827391) baseStart_4827391 baseEnd_4827391 := by
    simpa [prefixWord, tailWord_4827391, baseEnd_4827391] using wordTrace_append hprefix tailTrace_4827391
  have hstable : (prefixWord ++ tailWord_4827391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827391).length < 2 ^ (prefixWord ++ tailWord_4827391).sum := by decide
  have hdescent : baseEnd_4827391 < baseStart_4827391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827407 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_4827407 : Nat := 118140960795 + 4827407 * 2 ^ 59
def prefixEnd_4827407 : Nat := 4983230072969 + 3 ^ 40 * 4827407 * 2
def baseEnd_4827407 : Nat := 2478780105879099481611665

theorem tailTrace_4827407 : CollatzResearch.WordTrace tailWord_4827407 prefixEnd_4827407 2478780105879099481611665 := by
  unfold tailWord_4827407
  simp only [CollatzResearch.WordTrace]
  refine ⟨176069998022136369322456475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117379998681424246214970983 176069998022136369322456475)
  ·
    refine ⟨264104997033204553983684713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176069998022136369322456475 264104997033204553983684713)
    ·
      refine ⟨198078747774903415487763535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264104997033204553983684713 198078747774903415487763535)
      ·
        refine ⟨297118121662355123231645303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198078747774903415487763535 297118121662355123231645303)
        ·
          refine ⟨445677182493532684847467955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297118121662355123231645303 445677182493532684847467955)
          ·
            refine ⟨668515773740299027271201933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445677182493532684847467955 668515773740299027271201933)
            ·
              refine ⟨250693415152612135226700725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 668515773740299027271201933 250693415152612135226700725)
              ·
                refine ⟨23502507670557387677503193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250693415152612135226700725 23502507670557387677503193)
                ·
                  refine ⟨17626880752918040758127395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23502507670557387677503193 17626880752918040758127395)
                  ·
                    refine ⟨26440321129377061137191093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17626880752918040758127395 26440321129377061137191093)
                    ·
                      refine ⟨2478780105879099481611665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26440321129377061137191093 2478780105879099481611665)
                      ·
                        rfl

theorem cell23_4827407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_4827407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827407 prefixEnd_4827407 := by exact prefixLift 4827407
  have htrace : WordTrace (prefixWord ++ tailWord_4827407) baseStart_4827407 baseEnd_4827407 := by
    simpa [prefixWord, tailWord_4827407, baseEnd_4827407] using wordTrace_append hprefix tailTrace_4827407
  have hstable : (prefixWord ++ tailWord_4827407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827407).length < 2 ^ (prefixWord ++ tailWord_4827407).sum := by decide
  have hdescent : baseEnd_4827407 < baseStart_4827407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827474 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_4827474 : Nat := 118140960795 + 4827474 * 2 ^ 59
def prefixEnd_4827474 : Nat := 4983230072969 + 3 ^ 40 * 4827474 * 2
def baseEnd_4827474 : Nat := 826271503027650239824619

theorem tailTrace_4827474 : CollatzResearch.WordTrace tailWord_4827474 prefixEnd_4827474 826271503027650239824619 := by
  unfold tailWord_4827474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44018110428223409941286369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117381627808595759843430317 44018110428223409941286369)
  ·
    refine ⟨33013582821167557455964777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44018110428223409941286369 33013582821167557455964777)
    ·
      refine ⟨24760187115875668091973583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33013582821167557455964777 24760187115875668091973583)
      ·
        refine ⟨37140280673813502137960375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24760187115875668091973583 37140280673813502137960375)
        ·
          refine ⟨55710421010720253206940563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37140280673813502137960375 55710421010720253206940563)
          ·
            refine ⟨83565631516080379810410845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55710421010720253206940563 83565631516080379810410845)
            ·
              refine ⟨31337111818530142428904067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83565631516080379810410845 31337111818530142428904067)
              ·
                refine ⟨47005667727795213643356101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31337111818530142428904067 47005667727795213643356101)
                ·
                  refine ⟨8813562698961602558129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47005667727795213643356101 8813562698961602558129269)
                  ·
                    refine ⟨826271503027650239824619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8813562698961602558129269 826271503027650239824619)
                    ·
                      rfl

theorem cell23_4827474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_4827474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827474 prefixEnd_4827474 := by exact prefixLift 4827474
  have htrace : WordTrace (prefixWord ++ tailWord_4827474) baseStart_4827474 baseEnd_4827474 := by
    simpa [prefixWord, tailWord_4827474, baseEnd_4827474] using wordTrace_append hprefix tailTrace_4827474
  have hstable : (prefixWord ++ tailWord_4827474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827474).length < 2 ^ (prefixWord ++ tailWord_4827474).sum := by decide
  have hdescent : baseEnd_4827474 < baseStart_4827474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827524 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4827524 : Nat := 118140960795 + 4827524 * 2 ^ 59
def prefixEnd_4827524 : Nat := 4983230072969 + 3 ^ 40 * 4827524 * 2
def baseEnd_4827524 : Nat := 2478840183115675523848627

theorem tailTrace_4827524 : CollatzResearch.WordTrace tailWord_4827524 prefixEnd_4827524 2478840183115675523848627 := by
  unfold tailWord_4827524
  simp only [CollatzResearch.WordTrace]
  refine ⟨88037132681356249152232813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117382843575141665536310417 88037132681356249152232813)
  ·
    refine ⟨33013924755508593432087305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88037132681356249152232813 33013924755508593432087305)
    ·
      refine ⟨24760443566631445074065479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33013924755508593432087305 24760443566631445074065479)
      ·
        refine ⟨37140665349947167611098219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24760443566631445074065479 37140665349947167611098219)
        ·
          refine ⟨55710998024920751416647329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37140665349947167611098219 55710998024920751416647329)
          ·
            refine ⟨41783248518690563562485497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55710998024920751416647329 41783248518690563562485497)
            ·
              refine ⟨31337436389017922671864123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41783248518690563562485497 31337436389017922671864123)
              ·
                refine ⟨47006154583526884007796185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31337436389017922671864123 47006154583526884007796185)
                ·
                  refine ⟨35254615937645163005847139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47006154583526884007796185 35254615937645163005847139)
                  ·
                    refine ⟨52881923906467744508770709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35254615937645163005847139 52881923906467744508770709)
                    ·
                      refine ⟨2478840183115675523848627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 52881923906467744508770709 2478840183115675523848627)
                      ·
                        rfl

theorem cell23_4827524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4827524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827524 prefixEnd_4827524 := by exact prefixLift 4827524
  have htrace : WordTrace (prefixWord ++ tailWord_4827524) baseStart_4827524 baseEnd_4827524 := by
    simpa [prefixWord, tailWord_4827524, baseEnd_4827524] using wordTrace_append hprefix tailTrace_4827524
  have hstable : (prefixWord ++ tailWord_4827524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827524).length < 2 ^ (prefixWord ++ tailWord_4827524).sum := by decide
  have hdescent : baseEnd_4827524 < baseStart_4827524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4827531 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 3]
def baseStart_4827531 : Nat := 118140960795 + 4827531 * 2 ^ 59
def prefixEnd_4827531 : Nat := 4983230072969 + 3 ^ 40 * 4827531 * 2
def baseEnd_4827531 : Nat := 2478843777480256996461095

theorem tailTrace_4827531 : CollatzResearch.WordTrace tailWord_4827531 prefixEnd_4827531 2478843777480256996461095 := by
  unfold tailWord_4827531
  simp only [CollatzResearch.WordTrace]
  refine ⟨176074520673687138499970447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117383013782458092333313631 176074520673687138499970447)
  ·
    refine ⟨264111781010530707749955671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176074520673687138499970447 264111781010530707749955671)
    ·
      refine ⟨396167671515796061624933507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264111781010530707749955671 396167671515796061624933507)
      ·
        refine ⟨594251507273694092437400261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396167671515796061624933507 594251507273694092437400261)
        ·
          refine ⟨111422157613817642332012549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 594251507273694092437400261 111422157613817642332012549)
          ·
            refine ⟨20891654552590807937252353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111422157613817642332012549 20891654552590807937252353)
            ·
              refine ⟨15668740914443105952939265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20891654552590807937252353 15668740914443105952939265)
              ·
                refine ⟨11751555685832329464704449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15668740914443105952939265 11751555685832329464704449)
                ·
                  refine ⟨8813666764374247098528337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11751555685832329464704449 8813666764374247098528337)
                  ·
                    refine ⟨6610250073280685323896253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8813666764374247098528337 6610250073280685323896253)
                    ·
                      refine ⟨2478843777480256996461095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6610250073280685323896253 2478843777480256996461095)
                      ·
                        rfl

theorem cell23_4827531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 3].length) (baseStart_4827531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4827531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4827531 prefixEnd_4827531 := by exact prefixLift 4827531
  have htrace : WordTrace (prefixWord ++ tailWord_4827531) baseStart_4827531 baseEnd_4827531 := by
    simpa [prefixWord, tailWord_4827531, baseEnd_4827531] using wordTrace_append hprefix tailTrace_4827531
  have hstable : (prefixWord ++ tailWord_4827531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4827531).length < 2 ^ (prefixWord ++ tailWord_4827531).sum := by decide
  have hdescent : baseEnd_4827531 < baseStart_4827531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4827531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
