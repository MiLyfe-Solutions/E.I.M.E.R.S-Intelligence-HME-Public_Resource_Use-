import V185TrunkScan20Chunk045

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_279989 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_279989 : Nat := 118140960795 + 279989 * 2 ^ 59
def prefixEnd_279989 : Nat := 4983230072969 + 3 ^ 40 * 279989 * 2
def baseEnd_279989 : Nat := 127794608863831355955431

theorem tailTrace_279989 : CollatzResearch.WordTrace tailWord_279989 prefixEnd_279989 127794608863831355955431 := by
  unfold tailWord_279989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10212037782655146159299021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6808025188436764106199347 10212037782655146159299021)
  ·
    refine ⟨3829514168495679809737133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10212037782655146159299021 3829514168495679809737133)
    ·
      refine ⟨1436067813185879928651425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3829514168495679809737133 1436067813185879928651425)
      ·
        refine ⟨1077050859889409946488569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1436067813185879928651425 1077050859889409946488569)
        ·
          refine ⟨807788144917057459866427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077050859889409946488569 807788144917057459866427)
          ·
            refine ⟨1211682217375586189799641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807788144917057459866427 1211682217375586189799641)
            ·
              refine ⟨908761663031689642349731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1211682217375586189799641 908761663031689642349731)
              ·
                refine ⟨1363142494547534463524597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908761663031689642349731 1363142494547534463524597)
                ·
                  refine ⟨127794608863831355955431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363142494547534463524597 127794608863831355955431)
                  ·
                    rfl

theorem cell20_279989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_279989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_279989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_279989 prefixEnd_279989 := by exact prefixLift 279989
  have htrace : WordTrace (prefixWord ++ tailWord_279989) baseStart_279989 baseEnd_279989 := by
    simpa [prefixWord, tailWord_279989, baseEnd_279989] using wordTrace_append hprefix tailTrace_279989
  have hstable : (prefixWord ++ tailWord_279989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_279989).length < 2 ^ (prefixWord ++ tailWord_279989).sum := by decide
  have hdescent : baseEnd_279989 < baseStart_279989 := by decide
  rcases family_descends (prefixWord ++ tailWord_279989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280099 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 3]
def baseStart_280099 : Nat := 118140960795 + 280099 * 2 ^ 59
def prefixEnd_280099 : Nat := 4983230072969 + 3 ^ 40 * 280099 * 2
def baseEnd_280099 : Nat := 127844815861159862288315

theorem tailTrace_280099 : CollatzResearch.WordTrace tailWord_280099 prefixEnd_280099 127844815861159862288315 := by
  unfold tailWord_280099
  simp only [CollatzResearch.WordTrace]
  refine ⟨10216049812256634945803351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6810699874837756630535567 10216049812256634945803351)
  ·
    refine ⟨15324074718384952418705027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10216049812256634945803351 15324074718384952418705027)
    ·
      refine ⟨22986112077577428628057541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15324074718384952418705027 22986112077577428628057541)
      ·
        refine ⟨4309896014545767867760789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22986112077577428628057541 4309896014545767867760789)
        ·
          refine ⟨202026375681832868801287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4309896014545767867760789 202026375681832868801287)
          ·
            refine ⟨303039563522749303201931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202026375681832868801287 303039563522749303201931)
            ·
              refine ⟨454559345284123954802897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303039563522749303201931 454559345284123954802897)
              ·
                refine ⟨340919508963092966102173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454559345284123954802897 340919508963092966102173)
                ·
                  refine ⟨127844815861159862288315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340919508963092966102173 127844815861159862288315)
                  ·
                    rfl

theorem cell20_280099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 3].length) (baseStart_280099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280099 prefixEnd_280099 := by exact prefixLift 280099
  have htrace : WordTrace (prefixWord ++ tailWord_280099) baseStart_280099 baseEnd_280099 := by
    simpa [prefixWord, tailWord_280099, baseEnd_280099] using wordTrace_append hprefix tailTrace_280099
  have hstable : (prefixWord ++ tailWord_280099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280099).length < 2 ^ (prefixWord ++ tailWord_280099).sum := by decide
  have hdescent : baseEnd_280099 < baseStart_280099 := by decide
  rcases family_descends (prefixWord ++ tailWord_280099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280120 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_280120 : Nat := 118140960795 + 280120 * 2 ^ 59
def prefixEnd_280120 : Nat := 4983230072969 + 3 ^ 40 * 280120 * 2
def baseEnd_280120 : Nat := 127854400833377122588229

theorem tailTrace_280120 : CollatzResearch.WordTrace tailWord_280120 prefixEnd_280120 127854400833377122588229 := by
  unfold tailWord_280120
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108407872590277766158907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6811210496787037021545209 5108407872590277766158907)
  ·
    refine ⟨7662611808885416649238361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5108407872590277766158907 7662611808885416649238361)
    ·
      refine ⟨5746958856664062486928771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7662611808885416649238361 5746958856664062486928771)
      ·
        refine ⟨8620438284996093730393157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5746958856664062486928771 8620438284996093730393157)
        ·
          refine ⟨1616332178436767574448717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8620438284996093730393157 1616332178436767574448717)
          ·
            refine ⟨606124566913787840418269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1616332178436767574448717 606124566913787840418269)
            ·
              refine ⟨227296712592670440156851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606124566913787840418269 227296712592670440156851)
              ·
                refine ⟨340945068889005660235277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227296712592670440156851 340945068889005660235277)
                ·
                  refine ⟨127854400833377122588229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340945068889005660235277 127854400833377122588229)
                  ·
                    rfl

theorem cell20_280120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_280120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280120 prefixEnd_280120 := by exact prefixLift 280120
  have htrace : WordTrace (prefixWord ++ tailWord_280120) baseStart_280120 baseEnd_280120 := by
    simpa [prefixWord, tailWord_280120, baseEnd_280120] using wordTrace_append hprefix tailTrace_280120
  have hstable : (prefixWord ++ tailWord_280120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280120).length < 2 ^ (prefixWord ++ tailWord_280120).sum := by decide
  have hdescent : baseEnd_280120 < baseStart_280120 := by decide
  rcases family_descends (prefixWord ++ tailWord_280120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280165 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 4]
def baseStart_280165 : Nat := 118140960795 + 280165 * 2 ^ 59
def prefixEnd_280165 : Nat := 4983230072969 + 3 ^ 40 * 280165 * 2
def baseEnd_280165 : Nat := 127874940059556966088045

theorem tailTrace_280165 : CollatzResearch.WordTrace tailWord_280165 prefixEnd_280165 127874940059556966088045 := by
  unfold tailWord_280165
  simp only [CollatzResearch.WordTrace]
  refine ⟨10218457030017528217705949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6812304686678352145137299 10218457030017528217705949)
  ·
    refine ⟨3831921386256573081639731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10218457030017528217705949 3831921386256573081639731)
    ·
      refine ⟨5747882079384859622459597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3831921386256573081639731 5747882079384859622459597)
      ·
        refine ⟨2155455779769322358422349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5747882079384859622459597 2155455779769322358422349)
        ·
          refine ⟨808295917413495884408381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2155455779769322358422349 808295917413495884408381)
          ·
            refine ⟨303110969030060956653143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 808295917413495884408381 303110969030060956653143)
            ·
              refine ⟨454666453545091434979715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303110969030060956653143 454666453545091434979715)
              ·
                refine ⟨681999680317637152469573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454666453545091434979715 681999680317637152469573)
                ·
                  refine ⟨127874940059556966088045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681999680317637152469573 127874940059556966088045)
                  ·
                    rfl

theorem cell20_280165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_280165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280165 prefixEnd_280165 := by exact prefixLift 280165
  have htrace : WordTrace (prefixWord ++ tailWord_280165) baseStart_280165 baseEnd_280165 := by
    simpa [prefixWord, tailWord_280165, baseEnd_280165] using wordTrace_append hprefix tailTrace_280165
  have hstable : (prefixWord ++ tailWord_280165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280165).length < 2 ^ (prefixWord ++ tailWord_280165).sum := by decide
  have hdescent : baseEnd_280165 < baseStart_280165 := by decide
  rcases family_descends (prefixWord ++ tailWord_280165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280193 : List Nat := [1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_280193 : Nat := 118140960795 + 280193 * 2 ^ 59
def prefixEnd_280193 : Nat := 4983230072969 + 3 ^ 40 * 280193 * 2
def baseEnd_280193 : Nat := 42629240007504437718199

theorem tailTrace_280193 : CollatzResearch.WordTrace tailWord_280193 prefixEnd_280193 42629240007504437718199 := by
  unfold tailWord_280193
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219478273916088999725233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6812985515944059333150155 10219478273916088999725233)
  ·
    refine ⟨7664608705437066749793925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10219478273916088999725233 7664608705437066749793925)
    ·
      refine ⟨1437114132269450015586361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7664608705437066749793925 1437114132269450015586361)
      ·
        refine ⟨1077835599202087511689771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1437114132269450015586361 1077835599202087511689771)
        ·
          refine ⟨1616753398803131267534657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1077835599202087511689771 1616753398803131267534657)
          ·
            refine ⟨1212565049102348450650993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616753398803131267534657 1212565049102348450650993)
            ·
              refine ⟨909423786826761337988245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212565049102348450650993 909423786826761337988245)
              ·
                refine ⟨42629240007504437718199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 909423786826761337988245 42629240007504437718199)
                ·
                  rfl

theorem cell20_280193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_280193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280193 prefixEnd_280193 := by exact prefixLift 280193
  have htrace : WordTrace (prefixWord ++ tailWord_280193) baseStart_280193 baseEnd_280193 := by
    simpa [prefixWord, tailWord_280193, baseEnd_280193] using wordTrace_append hprefix tailTrace_280193
  have hstable : (prefixWord ++ tailWord_280193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280193).length < 2 ^ (prefixWord ++ tailWord_280193).sum := by decide
  have hdescent : baseEnd_280193 < baseStart_280193 := by decide
  rcases family_descends (prefixWord ++ tailWord_280193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280210 : List Nat := [3, 2, 3, 1, 4, 7]
def baseStart_280210 : Nat := 118140960795 + 280210 * 2 ^ 59
def prefixEnd_280210 : Nat := 4983230072969 + 3 ^ 40 * 280210 * 2
def baseEnd_280210 : Nat := 4736869603175437392143

theorem tailTrace_280210 : CollatzResearch.WordTrace tailWord_280210 prefixEnd_280210 4736869603175437392143 := by
  unfold tailWord_280210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555024578713625225773521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6813398876569667268729389 2555024578713625225773521)
  ·
    refine ⟨1916268434035218919330141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2555024578713625225773521 1916268434035218919330141)
    ·
      refine ⟨718600662763207094748803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1916268434035218919330141 718600662763207094748803)
      ·
        refine ⟨1077900994144810642123205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718600662763207094748803 1077900994144810642123205)
        ·
          refine ⟨202106436402151995398101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1077900994144810642123205 202106436402151995398101)
          ·
            refine ⟨4736869603175437392143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202106436402151995398101 4736869603175437392143)
            ·
              rfl

theorem cell20_280210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 7].length) (baseStart_280210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280210 prefixEnd_280210 := by exact prefixLift 280210
  have htrace : WordTrace (prefixWord ++ tailWord_280210) baseStart_280210 baseEnd_280210 := by
    simpa [prefixWord, tailWord_280210, baseEnd_280210] using wordTrace_append hprefix tailTrace_280210
  have hstable : (prefixWord ++ tailWord_280210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280210).length < 2 ^ (prefixWord ++ tailWord_280210).sum := by decide
  have hdescent : baseEnd_280210 < baseStart_280210 := by decide
  rcases family_descends (prefixWord ++ tailWord_280210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280220 : List Nat := [2, 2, 3, 2, 3, 1, 1, 4, 2]
def baseStart_280220 : Nat := 118140960795 + 280220 * 2 ^ 59
def prefixEnd_280220 : Nat := 4983230072969 + 3 ^ 40 * 280220 * 2
def baseEnd_280220 : Nat := 127900043558221219254487

theorem tailTrace_280220 : CollatzResearch.WordTrace tailWord_280220 prefixEnd_280220 127900043558221219254487 := by
  unfold tailWord_280220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110231522409136305479057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6813642029878848407305409 5110231522409136305479057)
  ·
    refine ⟨3832673641806852229109293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5110231522409136305479057 3832673641806852229109293)
    ·
      refine ⟨1437252615677569585915985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3832673641806852229109293 1437252615677569585915985)
      ·
        refine ⟨1077939461758177189436989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1437252615677569585915985 1077939461758177189436989)
        ·
          refine ⟨404227298159316446038871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1077939461758177189436989 404227298159316446038871)
          ·
            refine ⟨606340947238974669058307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404227298159316446038871 606340947238974669058307)
            ·
              refine ⟨909511420858462003587461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606340947238974669058307 909511420858462003587461)
              ·
                refine ⟨170533391410961625672649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 909511420858462003587461 170533391410961625672649)
                ·
                  refine ⟨127900043558221219254487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170533391410961625672649 127900043558221219254487)
                  ·
                    rfl

theorem cell20_280220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_280220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280220 prefixEnd_280220 := by exact prefixLift 280220
  have htrace : WordTrace (prefixWord ++ tailWord_280220) baseStart_280220 baseEnd_280220 := by
    simpa [prefixWord, tailWord_280220, baseEnd_280220] using wordTrace_append hprefix tailTrace_280220
  have hstable : (prefixWord ++ tailWord_280220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280220).length < 2 ^ (prefixWord ++ tailWord_280220).sum := by decide
  have hdescent : baseEnd_280220 < baseStart_280220 := by decide
  rcases family_descends (prefixWord ++ tailWord_280220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280307 : List Nat := [1, 1, 1, 2, 2, 3, 6, 4]
def baseStart_280307 : Nat := 118140960795 + 280307 * 2 ^ 59
def prefixEnd_280307 : Nat := 4983230072969 + 3 ^ 40 * 280307 * 2
def baseEnd_280307 : Nat := 42646584242945194451377

theorem tailTrace_280307 : CollatzResearch.WordTrace tailWord_280307 prefixEnd_280307 42646584242945194451377 := by
  unfold tailWord_280307
  simp only [CollatzResearch.WordTrace]
  refine ⟨10223636195503086469375175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6815757463668724312916783 10223636195503086469375175)
  ·
    refine ⟨15335454293254629704062763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10223636195503086469375175 15335454293254629704062763)
    ·
      refine ⟨23003181439881944556094145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15335454293254629704062763 23003181439881944556094145)
      ·
        refine ⟨17252386079911458417070609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23003181439881944556094145 17252386079911458417070609)
        ·
          refine ⟨12939289559933593812802957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17252386079911458417070609 12939289559933593812802957)
          ·
            refine ⟨4852233584975097679801109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12939289559933593812802957 4852233584975097679801109)
            ·
              refine ⟨227448449295707703740677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4852233584975097679801109 227448449295707703740677)
              ·
                refine ⟨42646584242945194451377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227448449295707703740677 42646584242945194451377)
                ·
                  rfl

theorem cell20_280307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_280307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280307 prefixEnd_280307 := by exact prefixLift 280307
  have htrace : WordTrace (prefixWord ++ tailWord_280307) baseStart_280307 baseEnd_280307 := by
    simpa [prefixWord, tailWord_280307, baseEnd_280307] using wordTrace_append hprefix tailTrace_280307
  have hstable : (prefixWord ++ tailWord_280307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280307).length < 2 ^ (prefixWord ++ tailWord_280307).sum := by decide
  have hdescent : baseEnd_280307 < baseStart_280307 := by decide
  rcases family_descends (prefixWord ++ tailWord_280307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280321 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_280321 : Nat := 118140960795 + 280321 * 2 ^ 59
def prefixEnd_280321 : Nat := 4983230072969 + 3 ^ 40 * 280321 * 2
def baseEnd_280321 : Nat := 127946142710313756887407

theorem tailTrace_280321 : CollatzResearch.WordTrace tailWord_280321 prefixEnd_280321 127946142710313756887407 := by
  unfold tailWord_280321
  simp only [CollatzResearch.WordTrace]
  refine ⟨10224146817452366860384817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6816097878301577906923211 10224146817452366860384817)
  ·
    refine ⟨7668110113089275145288613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10224146817452366860384817 7668110113089275145288613)
    ·
      refine ⟨1437770646204239089741615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7668110113089275145288613 1437770646204239089741615)
      ·
        refine ⟨2156655969306358634612423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437770646204239089741615 2156655969306358634612423)
        ·
          refine ⟨3234983953959537951918635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156655969306358634612423 3234983953959537951918635)
          ·
            refine ⟨4852475930939306927877953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3234983953959537951918635 4852475930939306927877953)
            ·
              refine ⟨3639356948204480195908465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4852475930939306927877953 3639356948204480195908465)
              ·
                refine ⟨2729517711153360146931349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3639356948204480195908465 2729517711153360146931349)
                ·
                  refine ⟨127946142710313756887407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2729517711153360146931349 127946142710313756887407)
                  ·
                    rfl

theorem cell20_280321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_280321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280321 prefixEnd_280321 := by exact prefixLift 280321
  have htrace : WordTrace (prefixWord ++ tailWord_280321) baseStart_280321 baseEnd_280321 := by
    simpa [prefixWord, tailWord_280321, baseEnd_280321] using wordTrace_append hprefix tailTrace_280321
  have hstable : (prefixWord ++ tailWord_280321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280321).length < 2 ^ (prefixWord ++ tailWord_280321).sum := by decide
  have hdescent : baseEnd_280321 < baseStart_280321 := by decide
  rcases family_descends (prefixWord ++ tailWord_280321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280326 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_280326 : Nat := 118140960795 + 280326 * 2 ^ 59
def prefixEnd_280326 : Nat := 4983230072969 + 3 ^ 40 * 280326 * 2
def baseEnd_280326 : Nat := 127948424846555961720721

theorem tailTrace_280326 : CollatzResearch.WordTrace tailWord_280326 prefixEnd_280326 127948424846555961720721 := by
  unfold tailWord_280326
  simp only [CollatzResearch.WordTrace]
  refine ⟨319510286951070397322401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6816219454956168476211221 319510286951070397322401)
  ·
    refine ⟨239632715213302797991801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 319510286951070397322401 239632715213302797991801)
    ·
      refine ⟨179724536409977098493851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239632715213302797991801 179724536409977098493851)
      ·
        refine ⟨269586804614965647740777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179724536409977098493851 269586804614965647740777)
        ·
          refine ⟨202190103461224235805583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269586804614965647740777 202190103461224235805583)
          ·
            refine ⟨303285155191836353708375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202190103461224235805583 303285155191836353708375)
            ·
              refine ⟨454927732787754530562563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303285155191836353708375 454927732787754530562563)
              ·
                refine ⟨682391599181631795843845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454927732787754530562563 682391599181631795843845)
                ·
                  refine ⟨127948424846555961720721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682391599181631795843845 127948424846555961720721)
                  ·
                    rfl

theorem cell20_280326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_280326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280326 prefixEnd_280326 := by exact prefixLift 280326
  have htrace : WordTrace (prefixWord ++ tailWord_280326) baseStart_280326 baseEnd_280326 := by
    simpa [prefixWord, tailWord_280326, baseEnd_280326] using wordTrace_append hprefix tailTrace_280326
  have hstable : (prefixWord ++ tailWord_280326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280326).length < 2 ^ (prefixWord ++ tailWord_280326).sum := by decide
  have hdescent : baseEnd_280326 < baseStart_280326 := by decide
  rcases family_descends (prefixWord ++ tailWord_280326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280340 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 3]
def baseStart_280340 : Nat := 118140960795 + 280340 * 2 ^ 59
def prefixEnd_280340 : Nat := 4983230072969 + 3 ^ 40 * 280340 * 2
def baseEnd_280340 : Nat := 127954814828034135253997

theorem tailTrace_280340 : CollatzResearch.WordTrace tailWord_280340 prefixEnd_280340 127954814828034135253997 := by
  unfold tailWord_280340
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112419902191766552663237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6816559869589022070217649 5112419902191766552663237)
  ·
    refine ⟨958578731660956228624357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5112419902191766552663237 958578731660956228624357)
    ·
      refine ⟨179733512186429292867067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 958578731660956228624357 179733512186429292867067)
      ·
        refine ⟨269600268279643939300601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179733512186429292867067 269600268279643939300601)
        ·
          refine ⟨202200201209732954475451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269600268279643939300601 202200201209732954475451)
          ·
            refine ⟨303300301814599431713177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202200201209732954475451 303300301814599431713177)
            ·
              refine ⟨227475226360949573784883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303300301814599431713177 227475226360949573784883)
              ·
                refine ⟨341212839541424360677325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227475226360949573784883 341212839541424360677325)
                ·
                  refine ⟨127954814828034135253997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341212839541424360677325 127954814828034135253997)
                  ·
                    rfl

theorem cell20_280340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_280340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280340 prefixEnd_280340 := by exact prefixLift 280340
  have htrace : WordTrace (prefixWord ++ tailWord_280340) baseStart_280340 baseEnd_280340 := by
    simpa [prefixWord, tailWord_280340, baseEnd_280340] using wordTrace_append hprefix tailTrace_280340
  have hstable : (prefixWord ++ tailWord_280340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280340).length < 2 ^ (prefixWord ++ tailWord_280340).sum := by decide
  have hdescent : baseEnd_280340 < baseStart_280340 := by decide
  rcases family_descends (prefixWord ++ tailWord_280340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280383 : List Nat := [1, 1, 2, 2, 7, 7]
def baseStart_280383 : Nat := 118140960795 + 280383 * 2 ^ 59
def prefixEnd_280383 : Nat := 4983230072969 + 3 ^ 40 * 280383 * 2
def baseEnd_280383 : Nat := 4739794118508040622981

theorem tailTrace_280383 : CollatzResearch.WordTrace tailWord_280383 prefixEnd_280383 4739794118508040622981 := by
  unfold tailWord_280383
  simp only [CollatzResearch.WordTrace]
  refine ⟨10226408143227751449141803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6817605428818500966094535 10226408143227751449141803)
  ·
    refine ⟨15339612214841627173712705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10226408143227751449141803 15339612214841627173712705)
    ·
      refine ⟨11504709161131220380284529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15339612214841627173712705 11504709161131220380284529)
      ·
        refine ⟨8628531870848415285213397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11504709161131220380284529 8628531870848415285213397)
        ·
          refine ⟨202231215723009733247189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8628531870848415285213397 202231215723009733247189)
          ·
            refine ⟨4739794118508040622981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202231215723009733247189 4739794118508040622981)
            ·
              rfl

theorem cell20_280383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 7].length) (baseStart_280383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280383 prefixEnd_280383 := by exact prefixLift 280383
  have htrace : WordTrace (prefixWord ++ tailWord_280383) baseStart_280383 baseEnd_280383 := by
    simpa [prefixWord, tailWord_280383, baseEnd_280383] using wordTrace_append hprefix tailTrace_280383
  have hstable : (prefixWord ++ tailWord_280383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280383).length < 2 ^ (prefixWord ++ tailWord_280383).sum := by decide
  have hdescent : baseEnd_280383 < baseStart_280383 := by decide
  rcases family_descends (prefixWord ++ tailWord_280383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280438 : List Nat := [5, 1, 1, 3, 2, 1, 7]
def baseStart_280438 : Nat := 118140960795 + 280438 * 2 ^ 59
def prefixEnd_280438 : Nat := 4983230072969 + 3 ^ 40 * 280438 * 2
def baseEnd_280438 : Nat := 14222171633153483331881

theorem tailTrace_280438 : CollatzResearch.WordTrace tailWord_280438 prefixEnd_280438 14222171633153483331881 := by
  unfold tailWord_280438
  simp only [CollatzResearch.WordTrace]
  refine ⟨639275884876780990149623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6818942772018997228262645 639275884876780990149623)
  ·
    refine ⟨958913827315171485224435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 639275884876780990149623 958913827315171485224435)
    ·
      refine ⟨1438370740972757227836653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958913827315171485224435 1438370740972757227836653)
      ·
        refine ⟨539389027864783960438745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1438370740972757227836653 539389027864783960438745)
        ·
          refine ⟨404541770898587970329059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539389027864783960438745 404541770898587970329059)
          ·
            refine ⟨606812656347881955493589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404541770898587970329059 606812656347881955493589)
            ·
              refine ⟨14222171633153483331881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 606812656347881955493589 14222171633153483331881)
              ·
                rfl

theorem cell20_280438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 7].length) (baseStart_280438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280438 prefixEnd_280438 := by exact prefixLift 280438
  have htrace : WordTrace (prefixWord ++ tailWord_280438) baseStart_280438 baseEnd_280438 := by
    simpa [prefixWord, tailWord_280438, baseEnd_280438] using wordTrace_append hprefix tailTrace_280438
  have hstable : (prefixWord ++ tailWord_280438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280438).length < 2 ^ (prefixWord ++ tailWord_280438).sum := by decide
  have hdescent : baseEnd_280438 < baseStart_280438 := by decide
  rcases family_descends (prefixWord ++ tailWord_280438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280472 : List Nat := [2, 1, 2, 6, 2, 1, 2, 4]
def baseStart_280472 : Nat := 118140960795 + 280472 * 2 ^ 59
def prefixEnd_280472 : Nat := 4983230072969 + 3 ^ 40 * 280472 * 2
def baseEnd_280472 : Nat := 42671687741609447617819

theorem tailTrace_280472 : CollatzResearch.WordTrace tailWord_280472 prefixEnd_280472 42671687741609447617819 := by
  unfold tailWord_280472
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114827119952659824565835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6819769493270213099421113 5114827119952659824565835)
  ·
    refine ⟨7672240679928989736848753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5114827119952659824565835 7672240679928989736848753)
    ·
      refine ⟨5754180509946742302636565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7672240679928989736848753 5754180509946742302636565)
      ·
        refine ⟨269727211403753545436089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5754180509946742302636565 269727211403753545436089)
        ·
          refine ⟨202295408552815159077067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269727211403753545436089 202295408552815159077067)
          ·
            refine ⟨303443112829222738615601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202295408552815159077067 303443112829222738615601)
            ·
              refine ⟨227582334621917053961701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303443112829222738615601 227582334621917053961701)
              ·
                refine ⟨42671687741609447617819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227582334621917053961701 42671687741609447617819)
                ·
                  rfl

theorem cell20_280472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_280472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280472 prefixEnd_280472 := by exact prefixLift 280472
  have htrace : WordTrace (prefixWord ++ tailWord_280472) baseStart_280472 baseEnd_280472 := by
    simpa [prefixWord, tailWord_280472, baseEnd_280472] using wordTrace_append hprefix tailTrace_280472
  have hstable : (prefixWord ++ tailWord_280472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280472).length < 2 ^ (prefixWord ++ tailWord_280472).sum := by decide
  have hdescent : baseEnd_280472 < baseStart_280472 := by decide
  rcases family_descends (prefixWord ++ tailWord_280472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280473 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_280473 : Nat := 118140960795 + 280473 * 2 ^ 59
def prefixEnd_280473 : Nat := 4983230072969 + 3 ^ 40 * 280473 * 2
def baseEnd_280473 : Nat := 128015519652076783820119

theorem tailTrace_280473 : CollatzResearch.WordTrace tailWord_280473 prefixEnd_280473 128015519652076783820119 := by
  unfold tailWord_280473
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229690712901696819918073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6819793808601131213278715 10229690712901696819918073)
  ·
    refine ⟨7672268034676272614938555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10229690712901696819918073 7672268034676272614938555)
    ·
      refine ⟨11508402052014408922407833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7672268034676272614938555 11508402052014408922407833)
      ·
        refine ⟨8631301539010806691805875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11508402052014408922407833 8631301539010806691805875)
        ·
          refine ⟨12946952308516210037708813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8631301539010806691805875 12946952308516210037708813)
          ·
            refine ⟨4855107115693578764140805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12946952308516210037708813 4855107115693578764140805)
            ·
              refine ⟨910332584192546018276401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4855107115693578764140805 910332584192546018276401)
              ·
                refine ⟨682749438144409513707301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910332584192546018276401 682749438144409513707301)
                ·
                  refine ⟨128015519652076783820119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682749438144409513707301 128015519652076783820119)
                  ·
                    rfl

theorem cell20_280473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_280473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280473 prefixEnd_280473 := by exact prefixLift 280473
  have htrace : WordTrace (prefixWord ++ tailWord_280473) baseStart_280473 baseEnd_280473 := by
    simpa [prefixWord, tailWord_280473, baseEnd_280473] using wordTrace_append hprefix tailTrace_280473
  have hstable : (prefixWord ++ tailWord_280473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280473).length < 2 ^ (prefixWord ++ tailWord_280473).sum := by decide
  have hdescent : baseEnd_280473 < baseStart_280473 := by decide
  rcases family_descends (prefixWord ++ tailWord_280473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280476 : List Nat := [2, 2, 3, 3, 1, 1, 4, 4]
def baseStart_280476 : Nat := 118140960795 + 280476 * 2 ^ 59
def prefixEnd_280476 : Nat := 4983230072969 + 3 ^ 40 * 280476 * 2
def baseEnd_280476 : Nat := 42672296311274035573369

theorem tailTrace_280476 : CollatzResearch.WordTrace tailWord_280476 prefixEnd_280476 42672296311274035573369 := by
  unfold tailWord_280476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5114900065945414166138641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6819866754593885554851521 5114900065945414166138641)
  ·
    refine ⟨3836175049459060624603981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5114900065945414166138641 3836175049459060624603981)
    ·
      refine ⟨1438565643547147734226493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3836175049459060624603981 1438565643547147734226493)
      ·
        refine ⟨539462116330180400334935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1438565643547147734226493 539462116330180400334935)
        ·
          refine ⟨809193174495270600502403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539462116330180400334935 809193174495270600502403)
          ·
            refine ⟨1213789761742905900753605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809193174495270600502403 1213789761742905900753605)
            ·
              refine ⟨227585580326794856391301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1213789761742905900753605 227585580326794856391301)
              ·
                refine ⟨42672296311274035573369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227585580326794856391301 42672296311274035573369)
                ·
                  rfl

theorem cell20_280476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_280476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280476 prefixEnd_280476 := by exact prefixLift 280476
  have htrace : WordTrace (prefixWord ++ tailWord_280476) baseStart_280476 baseEnd_280476 := by
    simpa [prefixWord, tailWord_280476, baseEnd_280476] using wordTrace_append hprefix tailTrace_280476
  have hstable : (prefixWord ++ tailWord_280476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280476).length < 2 ^ (prefixWord ++ tailWord_280476).sum := by decide
  have hdescent : baseEnd_280476 < baseStart_280476 := by decide
  rcases family_descends (prefixWord ++ tailWord_280476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280497 : List Nat := [1, 2, 2, 4, 2, 3, 6]
def baseStart_280497 : Nat := 118140960795 + 280497 * 2 ^ 59
def prefixEnd_280497 : Nat := 4983230072969 + 3 ^ 40 * 280497 * 2
def baseEnd_280497 : Nat := 14225163767337707446669

theorem tailTrace_280497 : CollatzResearch.WordTrace tailWord_280497 prefixEnd_280497 14225163767337707446669 := by
  unfold tailWord_280497
  simp only [CollatzResearch.WordTrace]
  refine ⟨10230566064814748918791745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6820377376543165945861163 10230566064814748918791745)
  ·
    refine ⟨7672924548611061689093809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10230566064814748918791745 7672924548611061689093809)
    ·
      refine ⟨5754693411458296266820357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7672924548611061689093809 5754693411458296266820357)
      ·
        refine ⟨1079005014648430550028817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5754693411458296266820357 1079005014648430550028817)
        ·
          refine ⟨809253760986322912521613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079005014648430550028817 809253760986322912521613)
          ·
            refine ⟨303470160369871092195605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 809253760986322912521613 303470160369871092195605)
            ·
              refine ⟨14225163767337707446669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 303470160369871092195605 14225163767337707446669)
              ·
                rfl

theorem cell20_280497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_280497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280497 prefixEnd_280497 := by exact prefixLift 280497
  have htrace : WordTrace (prefixWord ++ tailWord_280497) baseStart_280497 baseEnd_280497 := by
    simpa [prefixWord, tailWord_280497, baseEnd_280497] using wordTrace_append hprefix tailTrace_280497
  have hstable : (prefixWord ++ tailWord_280497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280497).length < 2 ^ (prefixWord ++ tailWord_280497).sum := by decide
  have hdescent : baseEnd_280497 < baseStart_280497 := by decide
  rcases family_descends (prefixWord ++ tailWord_280497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280504 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_280504 : Nat := 118140960795 + 280504 * 2 ^ 59
def prefixEnd_280504 : Nat := 4983230072969 + 3 ^ 40 * 280504 * 2
def baseEnd_280504 : Nat := 128029668896778453786659

theorem tailTrace_280504 : CollatzResearch.WordTrace tailWord_280504 prefixEnd_280504 128029668896778453786659 := by
  unfold tailWord_280504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115410687894694557148283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6820547583859592742864377 5115410687894694557148283)
  ·
    refine ⟨7673116031842041835722425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115410687894694557148283 7673116031842041835722425)
    ·
      refine ⟨5754837023881531376791819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7673116031842041835722425 5754837023881531376791819)
      ·
        refine ⟨8632255535822297065187729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5754837023881531376791819 8632255535822297065187729)
        ·
          refine ⟨6474191651866722798890797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8632255535822297065187729 6474191651866722798890797)
          ·
            refine ⟨2427821869450021049584049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6474191651866722798890797 2427821869450021049584049)
            ·
              refine ⟨1820866402087515787188037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427821869450021049584049 1820866402087515787188037)
              ·
                refine ⟨341412450391409210097757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1820866402087515787188037 341412450391409210097757)
                ·
                  refine ⟨128029668896778453786659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341412450391409210097757 128029668896778453786659)
                  ·
                    rfl

theorem cell20_280504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_280504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280504 prefixEnd_280504 := by exact prefixLift 280504
  have htrace : WordTrace (prefixWord ++ tailWord_280504) baseStart_280504 baseEnd_280504 := by
    simpa [prefixWord, tailWord_280504, baseEnd_280504] using wordTrace_append hprefix tailTrace_280504
  have hstable : (prefixWord ++ tailWord_280504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280504).length < 2 ^ (prefixWord ++ tailWord_280504).sum := by decide
  have hdescent : baseEnd_280504 < baseStart_280504 := by decide
  rcases family_descends (prefixWord ++ tailWord_280504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280563 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_280563 : Nat := 118140960795 + 280563 * 2 ^ 59
def prefixEnd_280563 : Nat := 4983230072969 + 3 ^ 40 * 280563 * 2
def baseEnd_280563 : Nat := 128056598104436470819751

theorem tailTrace_280563 : CollatzResearch.WordTrace tailWord_280563 prefixEnd_280563 128056598104436470819751 := by
  unfold tailWord_280563
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232973282575642190694343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6821982188383761460462895 10232973282575642190694343)
  ·
    refine ⟨15349459923863463286041515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10232973282575642190694343 15349459923863463286041515)
    ·
      refine ⟨23024189885795194929062273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15349459923863463286041515 23024189885795194929062273)
      ·
        refine ⟨17268142414346396196796705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23024189885795194929062273 17268142414346396196796705)
        ·
          refine ⟨12951106810759797147597529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17268142414346396196796705 12951106810759797147597529)
          ·
            refine ⟨9713330108069847860698147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12951106810759797147597529 9713330108069847860698147)
            ·
              refine ⟨14569995162104771791047221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9713330108069847860698147 14569995162104771791047221)
              ·
                refine ⟨1365937046447322355410677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14569995162104771791047221 1365937046447322355410677)
                ·
                  refine ⟨128056598104436470819751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1365937046447322355410677 128056598104436470819751)
                  ·
                    rfl

theorem cell20_280563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_280563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280563 prefixEnd_280563 := by exact prefixLift 280563
  have htrace : WordTrace (prefixWord ++ tailWord_280563) baseStart_280563 baseEnd_280563 := by
    simpa [prefixWord, tailWord_280563, baseEnd_280563] using wordTrace_append hprefix tailTrace_280563
  have hstable : (prefixWord ++ tailWord_280563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280563).length < 2 ^ (prefixWord ++ tailWord_280563).sum := by decide
  have hdescent : baseEnd_280563 < baseStart_280563 := by decide
  rcases family_descends (prefixWord ++ tailWord_280563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280587 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_280587 : Nat := 118140960795 + 280587 * 2 ^ 59
def prefixEnd_280587 : Nat := 4983230072969 + 3 ^ 40 * 280587 * 2
def baseEnd_280587 : Nat := 128067552358399054019653

theorem tailTrace_280587 : CollatzResearch.WordTrace tailWord_280587 prefixEnd_280587 128067552358399054019653 := by
  unfold tailWord_280587
  simp only [CollatzResearch.WordTrace]
  refine ⟨10233848634488694289568015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6822565756325796193045343 10233848634488694289568015)
  ·
    refine ⟨15350772951733041434352023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10233848634488694289568015 15350772951733041434352023)
    ·
      refine ⟨23026159427599562151528035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15350772951733041434352023 23026159427599562151528035)
      ·
        refine ⟨34539239141399343227292053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23026159427599562151528035 34539239141399343227292053)
        ·
          refine ⟨1619026834753094213779315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34539239141399343227292053 1619026834753094213779315)
          ·
            refine ⟨2428540252129641320668973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619026834753094213779315 2428540252129641320668973)
            ·
              refine ⟨910702594548615495250865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2428540252129641320668973 910702594548615495250865)
              ·
                refine ⟨683026945911461621438149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910702594548615495250865 683026945911461621438149)
                ·
                  refine ⟨128067552358399054019653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683026945911461621438149 128067552358399054019653)
                  ·
                    rfl

theorem cell20_280587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_280587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280587 prefixEnd_280587 := by exact prefixLift 280587
  have htrace : WordTrace (prefixWord ++ tailWord_280587) baseStart_280587 baseEnd_280587 := by
    simpa [prefixWord, tailWord_280587, baseEnd_280587] using wordTrace_append hprefix tailTrace_280587
  have hstable : (prefixWord ++ tailWord_280587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280587).length < 2 ^ (prefixWord ++ tailWord_280587).sum := by decide
  have hdescent : baseEnd_280587 < baseStart_280587 := by decide
  rcases family_descends (prefixWord ++ tailWord_280587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280601 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_280601 : Nat := 118140960795 + 280601 * 2 ^ 59
def prefixEnd_280601 : Nat := 4983230072969 + 3 ^ 40 * 280601 * 2
def baseEnd_280601 : Nat := 128073942339877227552929

theorem tailTrace_280601 : CollatzResearch.WordTrace tailWord_280601 prefixEnd_280601 128073942339877227552929 := by
  unfold tailWord_280601
  simp only [CollatzResearch.WordTrace]
  refine ⟨10234359256437974680577657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6822906170958649787051771 10234359256437974680577657)
  ·
    refine ⟨7675769442328481010433243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10234359256437974680577657 7675769442328481010433243)
    ·
      refine ⟨11513654163492721515649865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7675769442328481010433243 11513654163492721515649865)
      ·
        refine ⟨8635240622619541136737399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11513654163492721515649865 8635240622619541136737399)
        ·
          refine ⟨12952860933929311705106099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8635240622619541136737399 12952860933929311705106099)
          ·
            refine ⟨19429291400893967557659149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12952860933929311705106099 19429291400893967557659149)
            ·
              refine ⟨7285984275335237834122181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19429291400893967557659149 7285984275335237834122181)
              ·
                refine ⟨1366122051625357093897909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7285984275335237834122181 1366122051625357093897909)
                ·
                  refine ⟨128073942339877227552929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1366122051625357093897909 128073942339877227552929)
                  ·
                    rfl

theorem cell20_280601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_280601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280601 prefixEnd_280601 := by exact prefixLift 280601
  have htrace : WordTrace (prefixWord ++ tailWord_280601) baseStart_280601 baseEnd_280601 := by
    simpa [prefixWord, tailWord_280601, baseEnd_280601] using wordTrace_append hprefix tailTrace_280601
  have hstable : (prefixWord ++ tailWord_280601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280601).length < 2 ^ (prefixWord ++ tailWord_280601).sum := by decide
  have hdescent : baseEnd_280601 < baseStart_280601 := by decide
  rcases family_descends (prefixWord ++ tailWord_280601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280625 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_280625 : Nat := 118140960795 + 280625 * 2 ^ 59
def prefixEnd_280625 : Nat := 4983230072969 + 3 ^ 40 * 280625 * 2
def baseEnd_280625 : Nat := 128084896593839810752831

theorem tailTrace_280625 : CollatzResearch.WordTrace tailWord_280625 prefixEnd_280625 128084896593839810752831 := by
  unfold tailWord_280625
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235234608351026779451329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6823489738900684519634219 10235234608351026779451329)
  ·
    refine ⟨7676425956263270084588497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10235234608351026779451329 7676425956263270084588497)
    ·
      refine ⟨5757319467197452563441373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7676425956263270084588497 5757319467197452563441373)
      ·
        refine ⟨2158994800199044711290515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5757319467197452563441373 2158994800199044711290515)
        ·
          refine ⟨3238492200298567066935773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158994800199044711290515 3238492200298567066935773)
          ·
            refine ⟨1214434575111962650100915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3238492200298567066935773 1214434575111962650100915)
            ·
              refine ⟨1821651862667943975151373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214434575111962650100915 1821651862667943975151373)
              ·
                refine ⟨683119448500478990681765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1821651862667943975151373 683119448500478990681765)
                ·
                  refine ⟨128084896593839810752831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683119448500478990681765 128084896593839810752831)
                  ·
                    rfl

theorem cell20_280625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_280625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280625 prefixEnd_280625 := by exact prefixLift 280625
  have htrace : WordTrace (prefixWord ++ tailWord_280625) baseStart_280625 baseEnd_280625 := by
    simpa [prefixWord, tailWord_280625, baseEnd_280625] using wordTrace_append hprefix tailTrace_280625
  have hstable : (prefixWord ++ tailWord_280625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280625).length < 2 ^ (prefixWord ++ tailWord_280625).sum := by decide
  have hdescent : baseEnd_280625 < baseStart_280625 := by decide
  rcases family_descends (prefixWord ++ tailWord_280625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280690 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_280690 : Nat := 118140960795 + 280690 * 2 ^ 59
def prefixEnd_280690 : Nat := 4983230072969 + 3 ^ 40 * 280690 * 2
def baseEnd_280690 : Nat := 128114564364988473585899

theorem tailTrace_280690 : CollatzResearch.WordTrace tailWord_280690 prefixEnd_280690 128114564364988473585899 := by
  unfold tailWord_280690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559401338278885720141881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6825070235410361920378349 2559401338278885720141881)
  ·
    refine ⟨1919551003709164290106411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2559401338278885720141881 1919551003709164290106411)
    ·
      refine ⟨2879326505563746435159617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1919551003709164290106411 2879326505563746435159617)
      ·
        refine ⟨2159494879172809826369713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2879326505563746435159617 2159494879172809826369713)
        ·
          refine ⟨1619621159379607369777285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159494879172809826369713 1619621159379607369777285)
          ·
            refine ⟨303678967383676381833241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1619621159379607369777285 303678967383676381833241)
            ·
              refine ⟨227759225537757286374931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303678967383676381833241 227759225537757286374931)
              ·
                refine ⟨341638838306635929562397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227759225537757286374931 341638838306635929562397)
                ·
                  refine ⟨128114564364988473585899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341638838306635929562397 128114564364988473585899)
                  ·
                    rfl

theorem cell20_280690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_280690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280690 prefixEnd_280690 := by exact prefixLift 280690
  have htrace : WordTrace (prefixWord ++ tailWord_280690) baseStart_280690 baseEnd_280690 := by
    simpa [prefixWord, tailWord_280690, baseEnd_280690] using wordTrace_append hprefix tailTrace_280690
  have hstable : (prefixWord ++ tailWord_280690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280690).length < 2 ^ (prefixWord ++ tailWord_280690).sum := by decide
  have hdescent : baseEnd_280690 < baseStart_280690 := by decide
  rcases family_descends (prefixWord ++ tailWord_280690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280708 : List Nat := [2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_280708 : Nat := 118140960795 + 280708 * 2 ^ 59
def prefixEnd_280708 : Nat := 4983230072969 + 3 ^ 40 * 280708 * 2
def baseEnd_280708 : Nat := 42707593351820136995275

theorem tailTrace_280708 : CollatzResearch.WordTrace tailWord_280708 prefixEnd_280708 42707593351820136995275 := by
  unfold tailWord_280708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119130933525165977361389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6825507911366887969815185 5119130933525165977361389)
  ·
    refine ⟨1919674100071937241510521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5119130933525165977361389 1919674100071937241510521)
    ·
      refine ⟨1439755575053952931132891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1919674100071937241510521 1439755575053952931132891)
      ·
        refine ⟨2159633362580929396699337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439755575053952931132891 2159633362580929396699337)
        ·
          refine ⟨1619725021935697047524503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159633362580929396699337 1619725021935697047524503)
          ·
            refine ⟨2429587532903545571286755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619725021935697047524503 2429587532903545571286755)
            ·
              refine ⟨3644381299355318356930133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2429587532903545571286755 3644381299355318356930133)
              ·
                refine ⟨42707593351820136995275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3644381299355318356930133 42707593351820136995275)
                ·
                  rfl

theorem cell20_280708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_280708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280708 prefixEnd_280708 := by exact prefixLift 280708
  have htrace : WordTrace (prefixWord ++ tailWord_280708) baseStart_280708 baseEnd_280708 := by
    simpa [prefixWord, tailWord_280708, baseEnd_280708] using wordTrace_append hprefix tailTrace_280708
  have hstable : (prefixWord ++ tailWord_280708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280708).length < 2 ^ (prefixWord ++ tailWord_280708).sum := by decide
  have hdescent : baseEnd_280708 < baseStart_280708 := by decide
  rcases family_descends (prefixWord ++ tailWord_280708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280735 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 2]
def baseStart_280735 : Nat := 118140960795 + 280735 * 2 ^ 59
def prefixEnd_280735 : Nat := 4983230072969 + 3 ^ 40 * 280735 * 2
def baseEnd_280735 : Nat := 128135103591168317085715

theorem tailTrace_280735 : CollatzResearch.WordTrace tailWord_280735 prefixEnd_280735 128135103591168317085715 := by
  unfold tailWord_280735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10239246637952515565955659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6826164425301677043970439 10239246637952515565955659)
  ·
    refine ⟨15358869956928773348933489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10239246637952515565955659 15358869956928773348933489)
    ·
      refine ⟨11519152467696580011700117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15358869956928773348933489 11519152467696580011700117)
      ·
        refine ⟨539960271923277188048443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11519152467696580011700117 539960271923277188048443)
        ·
          refine ⟨809940407884915782072665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539960271923277188048443 809940407884915782072665)
          ·
            refine ⟨607455305913686836554499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809940407884915782072665 607455305913686836554499)
            ·
              refine ⟨911182958870530254831749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607455305913686836554499 911182958870530254831749)
              ·
                refine ⟨170846804788224422780953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 911182958870530254831749 170846804788224422780953)
                ·
                  refine ⟨128135103591168317085715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170846804788224422780953 128135103591168317085715)
                  ·
                    rfl

theorem cell20_280735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 2].length) (baseStart_280735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280735 prefixEnd_280735 := by exact prefixLift 280735
  have htrace : WordTrace (prefixWord ++ tailWord_280735) baseStart_280735 baseEnd_280735 := by
    simpa [prefixWord, tailWord_280735, baseEnd_280735] using wordTrace_append hprefix tailTrace_280735
  have hstable : (prefixWord ++ tailWord_280735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280735).length < 2 ^ (prefixWord ++ tailWord_280735).sum := by decide
  have hdescent : baseEnd_280735 < baseStart_280735 := by decide
  rcases family_descends (prefixWord ++ tailWord_280735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280749 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_280749 : Nat := 118140960795 + 280749 * 2 ^ 59
def prefixEnd_280749 : Nat := 4983230072969 + 3 ^ 40 * 280749 * 2
def baseEnd_280749 : Nat := 128141493572646490618991

theorem tailTrace_280749 : CollatzResearch.WordTrace tailWord_280749 prefixEnd_280749 128141493572646490618991 := by
  unfold tailWord_280749
  simp only [CollatzResearch.WordTrace]
  refine ⟨10239757259901795956965301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6826504839934530637976867 10239757259901795956965301)
  ·
    refine ⟨959977243115793370965497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10239757259901795956965301 959977243115793370965497)
    ·
      refine ⟨719982932336845028224123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 959977243115793370965497 719982932336845028224123)
      ·
        refine ⟨1079974398505267542336185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719982932336845028224123 1079974398505267542336185)
        ·
          refine ⟨809980798878950656752139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1079974398505267542336185 809980798878950656752139)
          ·
            refine ⟨1214971198318425985128209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809980798878950656752139 1214971198318425985128209)
            ·
              refine ⟨911228398738819488846157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1214971198318425985128209 911228398738819488846157)
              ·
                refine ⟨341710649527057308317309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 911228398738819488846157 341710649527057308317309)
                ·
                  refine ⟨128141493572646490618991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341710649527057308317309 128141493572646490618991)
                  ·
                    rfl

theorem cell20_280749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_280749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280749 prefixEnd_280749 := by exact prefixLift 280749
  have htrace : WordTrace (prefixWord ++ tailWord_280749) baseStart_280749 baseEnd_280749 := by
    simpa [prefixWord, tailWord_280749, baseEnd_280749] using wordTrace_append hprefix tailTrace_280749
  have hstable : (prefixWord ++ tailWord_280749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280749).length < 2 ^ (prefixWord ++ tailWord_280749).sum := by decide
  have hdescent : baseEnd_280749 < baseStart_280749 := by decide
  rcases family_descends (prefixWord ++ tailWord_280749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280790 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_280790 : Nat := 118140960795 + 280790 * 2 ^ 59
def prefixEnd_280790 : Nat := 4983230072969 + 3 ^ 40 * 280790 * 2
def baseEnd_280790 : Nat := 128160207089832570252157

theorem tailTrace_280790 : CollatzResearch.WordTrace tailWord_280790 prefixEnd_280790 128160207089832570252157 := by
  unfold tailWord_280790
  simp only [CollatzResearch.WordTrace]
  refine ⟨640078290797078747450489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6827501768502173306138549 640078290797078747450489)
  ·
    refine ⟨480058718097809060587867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 640078290797078747450489 480058718097809060587867)
    ·
      refine ⟨720088077146713590881801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480058718097809060587867 720088077146713590881801)
      ·
        refine ⟨540066057860035193161351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720088077146713590881801 540066057860035193161351)
        ·
          refine ⟨810099086790052789742027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540066057860035193161351 810099086790052789742027)
          ·
            refine ⟨1215148630185079184613041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810099086790052789742027 1215148630185079184613041)
            ·
              refine ⟨911361472638809388459781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215148630185079184613041 911361472638809388459781)
              ·
                refine ⟨170880276119776760336209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 911361472638809388459781 170880276119776760336209)
                ·
                  refine ⟨128160207089832570252157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170880276119776760336209 128160207089832570252157)
                  ·
                    rfl

theorem cell20_280790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_280790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280790 prefixEnd_280790 := by exact prefixLift 280790
  have htrace : WordTrace (prefixWord ++ tailWord_280790) baseStart_280790 baseEnd_280790 := by
    simpa [prefixWord, tailWord_280790, baseEnd_280790] using wordTrace_append hprefix tailTrace_280790
  have hstable : (prefixWord ++ tailWord_280790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280790).length < 2 ^ (prefixWord ++ tailWord_280790).sum := by decide
  have hdescent : baseEnd_280790 < baseStart_280790 := by decide
  rcases family_descends (prefixWord ++ tailWord_280790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280794 : List Nat := [3, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_280794 : Nat := 118140960795 + 280794 * 2 ^ 59
def prefixEnd_280794 : Nat := 4983230072969 + 3 ^ 40 * 280794 * 2
def baseEnd_280794 : Nat := 128162032798826334118807

theorem tailTrace_280794 : CollatzResearch.WordTrace tailWord_280794 prefixEnd_280794 128162032798826334118807 := by
  unfold tailWord_280794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560349636184692160588359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6827599029825845761568957 2560349636184692160588359)
  ·
    refine ⟨3840524454277038240882539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560349636184692160588359 3840524454277038240882539)
    ·
      refine ⟨5760786681415557361323809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3840524454277038240882539 5760786681415557361323809)
      ·
        refine ⟨4320590011061668020992857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5760786681415557361323809 4320590011061668020992857)
        ·
          refine ⟨3240442508296251015744643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4320590011061668020992857 3240442508296251015744643)
          ·
            refine ⟨4860663762444376523616965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240442508296251015744643 4860663762444376523616965)
            ·
              refine ⟨911374455458320598178181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4860663762444376523616965 911374455458320598178181)
              ·
                refine ⟨170882710398435112158409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 911374455458320598178181 170882710398435112158409)
                ·
                  refine ⟨128162032798826334118807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170882710398435112158409 128162032798826334118807)
                  ·
                    rfl

theorem cell20_280794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_280794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280794 prefixEnd_280794 := by exact prefixLift 280794
  have htrace : WordTrace (prefixWord ++ tailWord_280794) baseStart_280794 baseEnd_280794 := by
    simpa [prefixWord, tailWord_280794, baseEnd_280794] using wordTrace_append hprefix tailTrace_280794
  have hstable : (prefixWord ++ tailWord_280794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280794).length < 2 ^ (prefixWord ++ tailWord_280794).sum := by decide
  have hdescent : baseEnd_280794 < baseStart_280794 := by decide
  rcases family_descends (prefixWord ++ tailWord_280794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280815 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_280815 : Nat := 118140960795 + 280815 * 2 ^ 59
def prefixEnd_280815 : Nat := 4983230072969 + 3 ^ 40 * 280815 * 2
def baseEnd_280815 : Nat := 128171617771043594418721

theorem tailTrace_280815 : CollatzResearch.WordTrace tailWord_280815 prefixEnd_280815 128171617771043594418721 := by
  unfold tailWord_280815
  simp only [CollatzResearch.WordTrace]
  refine ⟨10242164477662689228867899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6828109651775126152578599 10242164477662689228867899)
  ·
    refine ⟨15363246716494033843301849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10242164477662689228867899 15363246716494033843301849)
    ·
      refine ⟨11522435037370525382476387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15363246716494033843301849 11522435037370525382476387)
      ·
        refine ⟨17283652556055788073714581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11522435037370525382476387 17283652556055788073714581)
        ·
          refine ⟨810171213565115065955371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17283652556055788073714581 810171213565115065955371)
          ·
            refine ⟨1215256820347672598933057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810171213565115065955371 1215256820347672598933057)
            ·
              refine ⟨911442615260754449199793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215256820347672598933057 911442615260754449199793)
              ·
                refine ⟨683581961445565836899845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911442615260754449199793 683581961445565836899845)
                ·
                  refine ⟨128171617771043594418721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683581961445565836899845 128171617771043594418721)
                  ·
                    rfl

theorem cell20_280815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_280815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280815 prefixEnd_280815 := by exact prefixLift 280815
  have htrace : WordTrace (prefixWord ++ tailWord_280815) baseStart_280815 baseEnd_280815 := by
    simpa [prefixWord, tailWord_280815, baseEnd_280815] using wordTrace_append hprefix tailTrace_280815
  have hstable : (prefixWord ++ tailWord_280815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280815).length < 2 ^ (prefixWord ++ tailWord_280815).sum := by decide
  have hdescent : baseEnd_280815 < baseStart_280815 := by decide
  rcases family_descends (prefixWord ++ tailWord_280815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280818 : List Nat := [3, 2, 1, 3, 2, 3, 2, 4]
def baseStart_280818 : Nat := 118140960795 + 280818 * 2 ^ 59
def prefixEnd_280818 : Nat := 4983230072969 + 3 ^ 40 * 280818 * 2
def baseEnd_280818 : Nat := 42724329017596305772903

theorem tailTrace_280818 : CollatzResearch.WordTrace tailWord_280818 prefixEnd_280818 42724329017596305772903 := by
  unfold tailWord_280818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560568474162955185306777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6828182597767880494151405 2560568474162955185306777)
  ·
    refine ⟨1920426355622216388980083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2560568474162955185306777 1920426355622216388980083)
    ·
      refine ⟨2880639533433324583470125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920426355622216388980083 2880639533433324583470125)
      ·
        refine ⟨1080239825037496718801297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2880639533433324583470125 1080239825037496718801297)
        ·
          refine ⟨810179868778122539100973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080239825037496718801297 810179868778122539100973)
          ·
            refine ⟨303817450791795952162865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 810179868778122539100973 303817450791795952162865)
            ·
              refine ⟨227863088093846964122149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303817450791795952162865 227863088093846964122149)
              ·
                refine ⟨42724329017596305772903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227863088093846964122149 42724329017596305772903)
                ·
                  rfl

theorem cell20_280818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_280818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280818 prefixEnd_280818 := by exact prefixLift 280818
  have htrace : WordTrace (prefixWord ++ tailWord_280818) baseStart_280818 baseEnd_280818 := by
    simpa [prefixWord, tailWord_280818, baseEnd_280818] using wordTrace_append hprefix tailTrace_280818
  have hstable : (prefixWord ++ tailWord_280818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280818).length < 2 ^ (prefixWord ++ tailWord_280818).sum := by decide
  have hdescent : baseEnd_280818 < baseStart_280818 := by decide
  rcases family_descends (prefixWord ++ tailWord_280818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280832 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 2]
def baseStart_280832 : Nat := 118140960795 + 280832 * 2 ^ 59
def prefixEnd_280832 : Nat := 4983230072969 + 3 ^ 40 * 280832 * 2
def baseEnd_280832 : Nat := 128179377034267090851985

theorem tailTrace_280832 : CollatzResearch.WordTrace tailWord_280832 prefixEnd_280832 128179377034267090851985 := by
  unfold tailWord_280832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5121392259300550566118375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6828523012400734088157833 5121392259300550566118375)
  ·
    refine ⟨7682088388950825849177563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5121392259300550566118375 7682088388950825849177563)
    ·
      refine ⟨11523132583426238773766345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7682088388950825849177563 11523132583426238773766345)
      ·
        refine ⟨8642349437569679080324759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11523132583426238773766345 8642349437569679080324759)
        ·
          refine ⟨12963524156354518620487139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8642349437569679080324759 12963524156354518620487139)
          ·
            refine ⟨19445286234531777930730709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12963524156354518620487139 19445286234531777930730709)
            ·
              refine ⟨455748896121838545251501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19445286234531777930730709 455748896121838545251501)
              ·
                refine ⟨170905836045689454469313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455748896121838545251501 170905836045689454469313)
                ·
                  refine ⟨128179377034267090851985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170905836045689454469313 128179377034267090851985)
                  ·
                    rfl

theorem cell20_280832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_280832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280832 prefixEnd_280832 := by exact prefixLift 280832
  have htrace : WordTrace (prefixWord ++ tailWord_280832) baseStart_280832 baseEnd_280832 := by
    simpa [prefixWord, tailWord_280832, baseEnd_280832] using wordTrace_append hprefix tailTrace_280832
  have hstable : (prefixWord ++ tailWord_280832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280832).length < 2 ^ (prefixWord ++ tailWord_280832).sum := by decide
  have hdescent : baseEnd_280832 < baseStart_280832 := by decide
  rcases family_descends (prefixWord ++ tailWord_280832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280846 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_280846 : Nat := 118140960795 + 280846 * 2 ^ 59
def prefixEnd_280846 : Nat := 4983230072969 + 3 ^ 40 * 280846 * 2
def baseEnd_280846 : Nat := 128185767015745264385261

theorem tailTrace_280846 : CollatzResearch.WordTrace tailWord_280846 prefixEnd_280846 128185767015745264385261 := by
  unfold tailWord_280846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280411892568797690405799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6828863427033587682164261 1280411892568797690405799)
  ·
    refine ⟨1920617838853196535608699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1280411892568797690405799 1920617838853196535608699)
    ·
      refine ⟨2880926758279794803413049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1920617838853196535608699 2880926758279794803413049)
      ·
        refine ⟨2160695068709846102559787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880926758279794803413049 2160695068709846102559787)
        ·
          refine ⟨3241042603064769153839681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160695068709846102559787 3241042603064769153839681)
          ·
            refine ⟨2430781952298576865379761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241042603064769153839681 2430781952298576865379761)
            ·
              refine ⟨1823086464223932649034821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430781952298576865379761 1823086464223932649034821)
              ·
                refine ⟨341828712041987371694029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1823086464223932649034821 341828712041987371694029)
                ·
                  refine ⟨128185767015745264385261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341828712041987371694029 128185767015745264385261)
                  ·
                    rfl

theorem cell20_280846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_280846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280846 prefixEnd_280846 := by exact prefixLift 280846
  have htrace : WordTrace (prefixWord ++ tailWord_280846) baseStart_280846 baseEnd_280846 := by
    simpa [prefixWord, tailWord_280846, baseEnd_280846] using wordTrace_append hprefix tailTrace_280846
  have hstable : (prefixWord ++ tailWord_280846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280846).length < 2 ^ (prefixWord ++ tailWord_280846).sum := by decide
  have hdescent : baseEnd_280846 < baseStart_280846 := by decide
  rcases family_descends (prefixWord ++ tailWord_280846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280849 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 2]
def baseStart_280849 : Nat := 118140960795 + 280849 * 2 ^ 59
def prefixEnd_280849 : Nat := 4983230072969 + 3 ^ 40 * 280849 * 2
def baseEnd_280849 : Nat := 128187136297490587285249

theorem tailTrace_280849 : CollatzResearch.WordTrace tailWord_280849 prefixEnd_280849 128187136297490587285249 := by
  unfold tailWord_280849
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243404559539513035605601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6828936373026342023737067 10243404559539513035605601)
  ·
    refine ⟨7682553419654634776704201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10243404559539513035605601 7682553419654634776704201)
    ·
      refine ⟨5761915064740976082528151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7682553419654634776704201 5761915064740976082528151)
      ·
        refine ⟨8642872597111464123792227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5761915064740976082528151 8642872597111464123792227)
        ·
          refine ⟨12964308895667196185688341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8642872597111464123792227 12964308895667196185688341)
          ·
            refine ⟨607701979484399821204141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12964308895667196185688341 607701979484399821204141)
            ·
              refine ⟨227888242306649932951553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 607701979484399821204141 227888242306649932951553)
              ·
                refine ⟨170916181729987449713665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227888242306649932951553 170916181729987449713665)
                ·
                  refine ⟨128187136297490587285249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170916181729987449713665 128187136297490587285249)
                  ·
                    rfl

theorem cell20_280849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_280849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280849 prefixEnd_280849 := by exact prefixLift 280849
  have htrace : WordTrace (prefixWord ++ tailWord_280849) baseStart_280849 baseEnd_280849 := by
    simpa [prefixWord, tailWord_280849, baseEnd_280849] using wordTrace_append hprefix tailTrace_280849
  have hstable : (prefixWord ++ tailWord_280849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280849).length < 2 ^ (prefixWord ++ tailWord_280849).sum := by decide
  have hdescent : baseEnd_280849 < baseStart_280849 := by decide
  rcases family_descends (prefixWord ++ tailWord_280849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280853 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 4]
def baseStart_280853 : Nat := 118140960795 + 280853 * 2 ^ 59
def prefixEnd_280853 : Nat := 4983230072969 + 3 ^ 40 * 280853 * 2
def baseEnd_280853 : Nat := 128188962006484351151899

theorem tailTrace_280853 : CollatzResearch.WordTrace tailWord_280853 prefixEnd_280853 128188962006484351151899 := by
  unfold tailWord_280853
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243550451525021718751213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6829033634350014479167475 10243550451525021718751213)
  ·
    refine ⟨3841331419321883144531705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10243550451525021718751213 3841331419321883144531705)
    ·
      refine ⟨2880998564491412358398779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3841331419321883144531705 2880998564491412358398779)
      ·
        refine ⟨4321497846737118537598169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2880998564491412358398779 4321497846737118537598169)
        ·
          refine ⟨3241123385052838903198627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4321497846737118537598169 3241123385052838903198627)
          ·
            refine ⟨4861685077579258354797941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3241123385052838903198627 4861685077579258354797941)
            ·
              refine ⟨455782976023055470762307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4861685077579258354797941 455782976023055470762307)
              ·
                refine ⟨683674464034583206143461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455782976023055470762307 683674464034583206143461)
                ·
                  refine ⟨128188962006484351151899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683674464034583206143461 128188962006484351151899)
                  ·
                    rfl

theorem cell20_280853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_280853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280853 prefixEnd_280853 := by exact prefixLift 280853
  have htrace : WordTrace (prefixWord ++ tailWord_280853) baseStart_280853 baseEnd_280853 := by
    simpa [prefixWord, tailWord_280853, baseEnd_280853] using wordTrace_append hprefix tailTrace_280853
  have hstable : (prefixWord ++ tailWord_280853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280853).length < 2 ^ (prefixWord ++ tailWord_280853).sum := by decide
  have hdescent : baseEnd_280853 < baseStart_280853 := by decide
  rcases family_descends (prefixWord ++ tailWord_280853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280863 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 3]
def baseStart_280863 : Nat := 118140960795 + 280863 * 2 ^ 59
def prefixEnd_280863 : Nat := 4983230072969 + 3 ^ 40 * 280863 * 2
def baseEnd_280863 : Nat := 128193526278968760818525

theorem tailTrace_280863 : CollatzResearch.WordTrace tailWord_280863 prefixEnd_280863 128193526278968760818525 := by
  unfold tailWord_280863
  simp only [CollatzResearch.WordTrace]
  refine ⟨10243915181488793426615243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6829276787659195617743495 10243915181488793426615243)
  ·
    refine ⟨15365872772233190139922865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10243915181488793426615243 15365872772233190139922865)
    ·
      refine ⟨11524404579174892604942149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15365872772233190139922865 11524404579174892604942149)
      ·
        refine ⟨2160825858595292363426653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11524404579174892604942149 2160825858595292363426653)
        ·
          refine ⟨810309696973234636284995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2160825858595292363426653 810309696973234636284995)
          ·
            refine ⟨1215464545459851954427493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810309696973234636284995 1215464545459851954427493)
            ·
              refine ⟨227899602273722241455155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1215464545459851954427493 227899602273722241455155)
              ·
                refine ⟨341849403410583362182733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227899602273722241455155 341849403410583362182733)
                ·
                  refine ⟨128193526278968760818525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341849403410583362182733 128193526278968760818525)
                  ·
                    rfl

theorem cell20_280863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_280863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280863 prefixEnd_280863 := by exact prefixLift 280863
  have htrace : WordTrace (prefixWord ++ tailWord_280863) baseStart_280863 baseEnd_280863 := by
    simpa [prefixWord, tailWord_280863, baseEnd_280863] using wordTrace_append hprefix tailTrace_280863
  have hstable : (prefixWord ++ tailWord_280863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280863).length < 2 ^ (prefixWord ++ tailWord_280863).sum := by decide
  have hdescent : baseEnd_280863 < baseStart_280863 := by decide
  rcases family_descends (prefixWord ++ tailWord_280863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280900 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 2]
def baseStart_280900 : Nat := 118140960795 + 280900 * 2 ^ 59
def prefixEnd_280900 : Nat := 4983230072969 + 3 ^ 40 * 280900 * 2
def baseEnd_280900 : Nat := 128210414087161076585041

theorem tailTrace_280900 : CollatzResearch.WordTrace tailWord_280900 prefixEnd_280900 128210414087161076585041 := by
  unfold tailWord_280900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122632341177374372856077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6830176454903165830474769 5122632341177374372856077)
  ·
    refine ⟨1920987127941515389821029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5122632341177374372856077 1920987127941515389821029)
    ·
      refine ⟨360185086489034135591443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1920987127941515389821029 360185086489034135591443)
      ·
        refine ⟨540277629733551203387165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360185086489034135591443 540277629733551203387165)
        ·
          refine ⟨202604111150081701270187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 540277629733551203387165 202604111150081701270187)
          ·
            refine ⟨303906166725122551905281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202604111150081701270187 303906166725122551905281)
            ·
              refine ⟨227929625043841913928961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303906166725122551905281 227929625043841913928961)
              ·
                refine ⟨170947218782881435446721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227929625043841913928961 170947218782881435446721)
                ·
                  refine ⟨128210414087161076585041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170947218782881435446721 128210414087161076585041)
                  ·
                    rfl

theorem cell20_280900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_280900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280900 prefixEnd_280900 := by exact prefixLift 280900
  have htrace : WordTrace (prefixWord ++ tailWord_280900) baseStart_280900 baseEnd_280900 := by
    simpa [prefixWord, tailWord_280900, baseEnd_280900] using wordTrace_append hprefix tailTrace_280900
  have hstable : (prefixWord ++ tailWord_280900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280900).length < 2 ^ (prefixWord ++ tailWord_280900).sum := by decide
  have hdescent : baseEnd_280900 < baseStart_280900 := by decide
  rcases family_descends (prefixWord ++ tailWord_280900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280908 : List Nat := [2, 2, 1, 3, 2, 1, 3, 4, 2]
def baseStart_280908 : Nat := 118140960795 + 280908 * 2 ^ 59
def prefixEnd_280908 : Nat := 4983230072969 + 3 ^ 40 * 280908 * 2
def baseEnd_280908 : Nat := 128214065505148604318341

theorem tailTrace_280908 : CollatzResearch.WordTrace tailWord_280908 prefixEnd_280908 128214065505148604318341 := by
  unfold tailWord_280908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122778233162883056001689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6830370977550510741335585 5122778233162883056001689)
  ·
    refine ⟨3842083674872162292001267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5122778233162883056001689 3842083674872162292001267)
    ·
      refine ⟨5763125512308243438001901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3842083674872162292001267 5763125512308243438001901)
      ·
        refine ⟨2161172067115591289250713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5763125512308243438001901 2161172067115591289250713)
        ·
          refine ⟨1620879050336693466938035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161172067115591289250713 1620879050336693466938035)
          ·
            refine ⟨2431318575505040200407053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620879050336693466938035 2431318575505040200407053)
            ·
              refine ⟨911744465814390075152645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431318575505040200407053 911744465814390075152645)
              ·
                refine ⟨170952087340198139091121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 911744465814390075152645 170952087340198139091121)
                ·
                  refine ⟨128214065505148604318341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170952087340198139091121 128214065505148604318341)
                  ·
                    rfl

theorem cell20_280908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_280908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280908 prefixEnd_280908 := by exact prefixLift 280908
  have htrace : WordTrace (prefixWord ++ tailWord_280908) baseStart_280908 baseEnd_280908 := by
    simpa [prefixWord, tailWord_280908, baseEnd_280908] using wordTrace_append hprefix tailTrace_280908
  have hstable : (prefixWord ++ tailWord_280908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280908).length < 2 ^ (prefixWord ++ tailWord_280908).sum := by decide
  have hdescent : baseEnd_280908 < baseStart_280908 := by decide
  rcases family_descends (prefixWord ++ tailWord_280908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280946 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_280946 : Nat := 118140960795 + 280946 * 2 ^ 59
def prefixEnd_280946 : Nat := 4983230072969 + 3 ^ 40 * 280946 * 2
def baseEnd_280946 : Nat := 128231409740589361051519

theorem tailTrace_280946 : CollatzResearch.WordTrace tailWord_280946 prefixEnd_280946 128231409740589361051519 := by
  unfold tailWord_280946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2561735610047024650471673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6831294960125399067924461 2561735610047024650471673)
  ·
    refine ⟨1921301707535268487853755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2561735610047024650471673 1921301707535268487853755)
    ·
      refine ⟨2881952561302902731780633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921301707535268487853755 2881952561302902731780633)
      ·
        refine ⟨2161464420977177048835475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2881952561302902731780633 2161464420977177048835475)
        ·
          refine ⟨3242196631465765573253213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161464420977177048835475 3242196631465765573253213)
          ·
            refine ⟨1215823736799662089969955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3242196631465765573253213 1215823736799662089969955)
            ·
              refine ⟨1823735605199493134954933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215823736799662089969955 1823735605199493134954933)
              ·
                refine ⟨170975212987452481402025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1823735605199493134954933 170975212987452481402025)
                ·
                  refine ⟨128231409740589361051519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170975212987452481402025 128231409740589361051519)
                  ·
                    rfl

theorem cell20_280946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_280946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280946 prefixEnd_280946 := by exact prefixLift 280946
  have htrace : WordTrace (prefixWord ++ tailWord_280946) baseStart_280946 baseEnd_280946 := by
    simpa [prefixWord, tailWord_280946, baseEnd_280946] using wordTrace_append hprefix tailTrace_280946
  have hstable : (prefixWord ++ tailWord_280946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280946).length < 2 ^ (prefixWord ++ tailWord_280946).sum := by decide
  have hdescent : baseEnd_280946 < baseStart_280946 := by decide
  rcases family_descends (prefixWord ++ tailWord_280946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_280967 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_280967 : Nat := 118140960795 + 280967 * 2 ^ 59
def prefixEnd_280967 : Nat := 4983230072969 + 3 ^ 40 * 280967 * 2
def baseEnd_280967 : Nat := 128240994712806621351433

theorem tailTrace_280967 : CollatzResearch.WordTrace tailWord_280967 prefixEnd_280967 128240994712806621351433 := by
  unfold tailWord_280967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10247708373112019188401155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6831805582074679458934103 10247708373112019188401155)
  ·
    refine ⟨15371562559668028782601733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10247708373112019188401155 15371562559668028782601733)
    ·
      refine ⟨2882167979937755396737825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15371562559668028782601733 2882167979937755396737825)
      ·
        refine ⟨2161625984953316547553369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2882167979937755396737825 2161625984953316547553369)
        ·
          refine ⟨1621219488714987410665027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161625984953316547553369 1621219488714987410665027)
          ·
            refine ⟨2431829233072481115997541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621219488714987410665027 2431829233072481115997541)
            ·
              refine ⟨455967981201090209249539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2431829233072481115997541 455967981201090209249539)
              ·
                refine ⟨683951971801635313874309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455967981201090209249539 683951971801635313874309)
                ·
                  refine ⟨128240994712806621351433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683951971801635313874309 128240994712806621351433)
                  ·
                    rfl

theorem cell20_280967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_280967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_280967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_280967 prefixEnd_280967 := by exact prefixLift 280967
  have htrace : WordTrace (prefixWord ++ tailWord_280967) baseStart_280967 baseEnd_280967 := by
    simpa [prefixWord, tailWord_280967, baseEnd_280967] using wordTrace_append hprefix tailTrace_280967
  have hstable : (prefixWord ++ tailWord_280967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_280967).length < 2 ^ (prefixWord ++ tailWord_280967).sum := by decide
  have hdescent : baseEnd_280967 < baseStart_280967 := by decide
  rcases family_descends (prefixWord ++ tailWord_280967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281022 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_281022 : Nat := 118140960795 + 281022 * 2 ^ 59
def prefixEnd_281022 : Nat := 4983230072969 + 3 ^ 40 * 281022 * 2
def baseEnd_281022 : Nat := 128266098211470874517875

theorem tailTrace_281022 : CollatzResearch.WordTrace tailWord_281022 prefixEnd_281022 128266098211470874517875 := by
  unfold tailWord_281022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281214298489095447706665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6833142925275175721102213 1281214298489095447706665)
  ·
    refine ⟨960910723866821585779999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1281214298489095447706665 960910723866821585779999)
    ·
      refine ⟨1441366085800232378669999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960910723866821585779999 1441366085800232378669999)
      ·
        refine ⟨2162049128700348568004999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441366085800232378669999 2162049128700348568004999)
        ·
          refine ⟨3243073693050522852007499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162049128700348568004999 3243073693050522852007499)
          ·
            refine ⟨4864610539575784278011249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3243073693050522852007499 4864610539575784278011249)
            ·
              refine ⟨3648457904681838208508437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4864610539575784278011249 3648457904681838208508437)
              ·
                refine ⟨171021464281961166023833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3648457904681838208508437 171021464281961166023833)
                ·
                  refine ⟨128266098211470874517875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171021464281961166023833 128266098211470874517875)
                  ·
                    rfl

theorem cell20_281022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_281022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281022 prefixEnd_281022 := by exact prefixLift 281022
  have htrace : WordTrace (prefixWord ++ tailWord_281022) baseStart_281022 baseEnd_281022 := by
    simpa [prefixWord, tailWord_281022, baseEnd_281022] using wordTrace_append hprefix tailTrace_281022
  have hstable : (prefixWord ++ tailWord_281022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281022).length < 2 ^ (prefixWord ++ tailWord_281022).sum := by decide
  have hdescent : baseEnd_281022 < baseStart_281022 := by decide
  rcases family_descends (prefixWord ++ tailWord_281022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281025 : List Nat := [1, 2, 7, 1, 1, 1, 2, 5]
def baseStart_281025 : Nat := 118140960795 + 281025 * 2 ^ 59
def prefixEnd_281025 : Nat := 4983230072969 + 3 ^ 40 * 281025 * 2
def baseEnd_281025 : Nat := 42755822497738732472621

theorem tailTrace_281025 : CollatzResearch.WordTrace tailWord_281025 prefixEnd_281025 42755822497738732472621 := by
  unfold tailWord_281025
  simp only [CollatzResearch.WordTrace]
  refine ⟨10249823806901895094012529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6833215871267930062675019 10249823806901895094012529)
  ·
    refine ⟨7687367855176421320509397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10249823806901895094012529 7687367855176421320509397)
    ·
      refine ⟨180172684105697374699439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7687367855176421320509397 180172684105697374699439)
      ·
        refine ⟨270259026158546062049159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180172684105697374699439 270259026158546062049159)
        ·
          refine ⟨405388539237819093073739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270259026158546062049159 405388539237819093073739)
          ·
            refine ⟨608082808856728639610609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405388539237819093073739 608082808856728639610609)
            ·
              refine ⟨456062106642546479707957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608082808856728639610609 456062106642546479707957)
              ·
                refine ⟨42755822497738732472621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 456062106642546479707957 42755822497738732472621)
                ·
                  rfl

theorem cell20_281025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 5].length) (baseStart_281025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281025 prefixEnd_281025 := by exact prefixLift 281025
  have htrace : WordTrace (prefixWord ++ tailWord_281025) baseStart_281025 baseEnd_281025 := by
    simpa [prefixWord, tailWord_281025, baseEnd_281025] using wordTrace_append hprefix tailTrace_281025
  have hstable : (prefixWord ++ tailWord_281025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281025).length < 2 ^ (prefixWord ++ tailWord_281025).sum := by decide
  have hdescent : baseEnd_281025 < baseStart_281025 := by decide
  rcases family_descends (prefixWord ++ tailWord_281025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281033 : List Nat := [1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_281033 : Nat := 118140960795 + 281033 * 2 ^ 59
def prefixEnd_281033 : Nat := 4983230072969 + 3 ^ 40 * 281033 * 2
def baseEnd_281033 : Nat := 42757039637067908383721

theorem tailTrace_281033 : CollatzResearch.WordTrace tailWord_281033 prefixEnd_281033 42757039637067908383721 := by
  unfold tailWord_281033
  simp only [CollatzResearch.WordTrace]
  refine ⟨10250115590872912460303753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6833410393915274973535835 10250115590872912460303753)
  ·
    refine ⟨7687586693154684345227815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10250115590872912460303753 7687586693154684345227815)
    ·
      refine ⟨11531380039732026517841723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7687586693154684345227815 11531380039732026517841723)
      ·
        refine ⟨17297070059598039776762585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11531380039732026517841723 17297070059598039776762585)
        ·
          refine ⟨12972802544698529832571939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17297070059598039776762585 12972802544698529832571939)
          ·
            refine ⟨19459203817047794748857909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12972802544698529832571939 19459203817047794748857909)
            ·
              refine ⟨1824300357848230757705429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19459203817047794748857909 1824300357848230757705429)
              ·
                refine ⟨42757039637067908383721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1824300357848230757705429 42757039637067908383721)
                ·
                  rfl

theorem cell20_281033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_281033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281033 prefixEnd_281033 := by exact prefixLift 281033
  have htrace : WordTrace (prefixWord ++ tailWord_281033) baseStart_281033 baseEnd_281033 := by
    simpa [prefixWord, tailWord_281033, baseEnd_281033] using wordTrace_append hprefix tailTrace_281033
  have hstable : (prefixWord ++ tailWord_281033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281033).length < 2 ^ (prefixWord ++ tailWord_281033).sum := by decide
  have hdescent : baseEnd_281033 < baseStart_281033 := by decide
  rcases family_descends (prefixWord ++ tailWord_281033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281094 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_281094 : Nat := 118140960795 + 281094 * 2 ^ 59
def prefixEnd_281094 : Nat := 4983230072969 + 3 ^ 40 * 281094 * 2
def baseEnd_281094 : Nat := 128298960973358624117581

theorem tailTrace_281094 : CollatzResearch.WordTrace tailWord_281094 prefixEnd_281094 128298960973358624117581 := by
  unfold tailWord_281094
  simp only [CollatzResearch.WordTrace]
  refine ⟨320385638864122496196073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6834893629101279918849557 320385638864122496196073)
  ·
    refine ⟨240289229148091872147055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 320385638864122496196073 240289229148091872147055)
    ·
      refine ⟨360433843722137808220583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240289229148091872147055 360433843722137808220583)
      ·
        refine ⟨540650765583206712330875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360433843722137808220583 540650765583206712330875)
        ·
          refine ⟨810976148374810068496313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540650765583206712330875 810976148374810068496313)
          ·
            refine ⟨608232111281107551372235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810976148374810068496313 608232111281107551372235)
            ·
              refine ⟨912348166921661327058353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608232111281107551372235 912348166921661327058353)
              ·
                refine ⟨684261125191245995293765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912348166921661327058353 684261125191245995293765)
                ·
                  refine ⟨128298960973358624117581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684261125191245995293765 128298960973358624117581)
                  ·
                    rfl

theorem cell20_281094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_281094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281094 prefixEnd_281094 := by exact prefixLift 281094
  have htrace : WordTrace (prefixWord ++ tailWord_281094) baseStart_281094 baseEnd_281094 := by
    simpa [prefixWord, tailWord_281094, baseEnd_281094] using wordTrace_append hprefix tailTrace_281094
  have hstable : (prefixWord ++ tailWord_281094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281094).length < 2 ^ (prefixWord ++ tailWord_281094).sum := by decide
  have hdescent : baseEnd_281094 < baseStart_281094 := by decide
  rcases family_descends (prefixWord ++ tailWord_281094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281101 : List Nat := [1, 7, 1, 1, 1, 2, 3, 4]
def baseStart_281101 : Nat := 118140960795 + 281101 * 2 ^ 59
def prefixEnd_281101 : Nat := 4983230072969 + 3 ^ 40 * 281101 * 2
def baseEnd_281101 : Nat := 42767385321365903628073

theorem tailTrace_281101 : CollatzResearch.WordTrace tailWord_281101 prefixEnd_281101 42767385321365903628073 := by
  unfold tailWord_281101
  simp only [CollatzResearch.WordTrace]
  refine ⟨10252595754626560073779157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6835063836417706715852771 10252595754626560073779157)
  ·
    refine ⟨240295212999060001729199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10252595754626560073779157 240295212999060001729199)
    ·
      refine ⟨360442819498590002593799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240295212999060001729199 360442819498590002593799)
      ·
        refine ⟨540664229247885003890699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360442819498590002593799 540664229247885003890699)
        ·
          refine ⟨810996343871827505836049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540664229247885003890699 810996343871827505836049)
          ·
            refine ⟨608247257903870629377037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810996343871827505836049 608247257903870629377037)
            ·
              refine ⟨228092721713951486016389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 608247257903870629377037 228092721713951486016389)
              ·
                refine ⟨42767385321365903628073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228092721713951486016389 42767385321365903628073)
                ·
                  rfl

theorem cell20_281101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 4].length) (baseStart_281101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281101 prefixEnd_281101 := by exact prefixLift 281101
  have htrace : WordTrace (prefixWord ++ tailWord_281101) baseStart_281101 baseEnd_281101 := by
    simpa [prefixWord, tailWord_281101, baseEnd_281101] using wordTrace_append hprefix tailTrace_281101
  have hstable : (prefixWord ++ tailWord_281101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281101).length < 2 ^ (prefixWord ++ tailWord_281101).sum := by decide
  have hdescent : baseEnd_281101 < baseStart_281101 := by decide
  rcases family_descends (prefixWord ++ tailWord_281101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281156 : List Nat := [2, 3, 5, 1, 1, 2, 2, 4]
def baseStart_281156 : Nat := 118140960795 + 281156 * 2 ^ 59
def prefixEnd_281156 : Nat := 4983230072969 + 3 ^ 40 * 281156 * 2
def baseEnd_281156 : Nat := 42775753154253988016887

theorem tailTrace_281156 : CollatzResearch.WordTrace tailWord_281156 prefixEnd_281156 42775753154253988016887 := by
  unfold tailWord_281156
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127300884713652233515661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6836401179618202978020881 5127300884713652233515661)
  ·
    refine ⟨1922737831767619587568373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5127300884713652233515661 1922737831767619587568373)
    ·
      refine ⟨180256671728214336334535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1922737831767619587568373 180256671728214336334535)
      ·
        refine ⟨270385007592321504501803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180256671728214336334535 270385007592321504501803)
        ·
          refine ⟨405577511388482256752705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270385007592321504501803 405577511388482256752705)
          ·
            refine ⟨304183133541361692564529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405577511388482256752705 304183133541361692564529)
            ·
              refine ⟨228137350156021269423397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304183133541361692564529 228137350156021269423397)
              ·
                refine ⟨42775753154253988016887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228137350156021269423397 42775753154253988016887)
                ·
                  rfl

theorem cell20_281156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_281156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281156 prefixEnd_281156 := by exact prefixLift 281156
  have htrace : WordTrace (prefixWord ++ tailWord_281156) baseStart_281156 baseEnd_281156 := by
    simpa [prefixWord, tailWord_281156, baseEnd_281156] using wordTrace_append hprefix tailTrace_281156
  have hstable : (prefixWord ++ tailWord_281156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281156).length < 2 ^ (prefixWord ++ tailWord_281156).sum := by decide
  have hdescent : baseEnd_281156 < baseStart_281156 := by decide
  rcases family_descends (prefixWord ++ tailWord_281156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281185 : List Nat := [1, 2, 3, 1, 1, 4, 8]
def baseStart_281185 : Nat := 118140960795 + 281185 * 2 ^ 59
def prefixEnd_281185 : Nat := 4983230072969 + 3 ^ 40 * 281185 * 2
def baseEnd_281185 : Nat := 14260055094774083564875

theorem tailTrace_281185 : CollatzResearch.WordTrace tailWord_281185 prefixEnd_281185 14260055094774083564875 := by
  unfold tailWord_281185
  simp only [CollatzResearch.WordTrace]
  refine ⟨10255659486322242419837009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6837106324214828279891339 10255659486322242419837009)
  ·
    refine ⟨7691744614741681814877757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10255659486322242419837009 7691744614741681814877757)
    ·
      refine ⟨2884404230528130680579159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7691744614741681814877757 2884404230528130680579159)
      ·
        refine ⟨4326606345792196020868739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884404230528130680579159 4326606345792196020868739)
        ·
          refine ⟨6489909518688294031303109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326606345792196020868739 6489909518688294031303109)
          ·
            refine ⟨1216858034754055130869333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6489909518688294031303109 1216858034754055130869333)
            ·
              refine ⟨14260055094774083564875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1216858034754055130869333 14260055094774083564875)
              ·
                rfl

theorem cell20_281185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_281185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281185 prefixEnd_281185 := by exact prefixLift 281185
  have htrace : WordTrace (prefixWord ++ tailWord_281185) baseStart_281185 baseEnd_281185 := by
    simpa [prefixWord, tailWord_281185, baseEnd_281185] using wordTrace_append hprefix tailTrace_281185
  have hstable : (prefixWord ++ tailWord_281185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281185).length < 2 ^ (prefixWord ++ tailWord_281185).sum := by decide
  have hdescent : baseEnd_281185 < baseStart_281185 := by decide
  rcases family_descends (prefixWord ++ tailWord_281185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281205 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_281205 : Nat := 118140960795 + 281205 * 2 ^ 59
def prefixEnd_281205 : Nat := 4983230072969 + 3 ^ 40 * 281205 * 2
def baseEnd_281205 : Nat := 128349624397935571417127

theorem tailTrace_281205 : CollatzResearch.WordTrace tailWord_281205 prefixEnd_281205 128349624397935571417127 := by
  unfold tailWord_281205
  simp only [CollatzResearch.WordTrace]
  refine ⟨10256388946249785835565069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6837592630833190557043379 10256388946249785835565069)
  ·
    refine ⟨3846145854843669688336901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10256388946249785835565069 3846145854843669688336901)
    ·
      refine ⟨721152347783188066563169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3846145854843669688336901 721152347783188066563169)
      ·
        refine ⟨540864260837391049922377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 721152347783188066563169 540864260837391049922377)
        ·
          refine ⟨405648195628043287441783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540864260837391049922377 405648195628043287441783)
          ·
            refine ⟨608472293442064931162675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405648195628043287441783 608472293442064931162675)
            ·
              refine ⟨912708440163097396744013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608472293442064931162675 912708440163097396744013)
              ·
                refine ⟨342265665061161523779005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 912708440163097396744013 342265665061161523779005)
                ·
                  refine ⟨128349624397935571417127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342265665061161523779005 128349624397935571417127)
                  ·
                    rfl

theorem cell20_281205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_281205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281205 prefixEnd_281205 := by exact prefixLift 281205
  have htrace : WordTrace (prefixWord ++ tailWord_281205) baseStart_281205 baseEnd_281205 := by
    simpa [prefixWord, tailWord_281205, baseEnd_281205] using wordTrace_append hprefix tailTrace_281205
  have hstable : (prefixWord ++ tailWord_281205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281205).length < 2 ^ (prefixWord ++ tailWord_281205).sum := by decide
  have hdescent : baseEnd_281205 < baseStart_281205 := by decide
  rcases family_descends (prefixWord ++ tailWord_281205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281223 : List Nat := [1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_281223 : Nat := 118140960795 + 281223 * 2 ^ 59
def prefixEnd_281223 : Nat := 4983230072969 + 3 ^ 40 * 281223 * 2
def baseEnd_281223 : Nat := 42785946696135836272351

theorem tailTrace_281223 : CollatzResearch.WordTrace tailWord_281223 prefixEnd_281223 42785946696135836272351 := by
  unfold tailWord_281223
  simp only [CollatzResearch.WordTrace]
  refine ⟨10257045460184574909720323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6838030306789716606480215 10257045460184574909720323)
  ·
    refine ⟨15385568190276862364580485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10257045460184574909720323 15385568190276862364580485)
    ·
      refine ⟨2884794035676911693358841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15385568190276862364580485 2884794035676911693358841)
      ·
        refine ⟨2163595526757683770019131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2884794035676911693358841 2163595526757683770019131)
        ·
          refine ⟨3245393290136525655028697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163595526757683770019131 3245393290136525655028697)
          ·
            refine ⟨2434044967602394241271523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3245393290136525655028697 2434044967602394241271523)
            ·
              refine ⟨3651067451403591361907285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434044967602394241271523 3651067451403591361907285)
              ·
                refine ⟨42785946696135836272351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3651067451403591361907285 42785946696135836272351)
                ·
                  rfl

theorem cell20_281223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_281223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281223 prefixEnd_281223 := by exact prefixLift 281223
  have htrace : WordTrace (prefixWord ++ tailWord_281223) baseStart_281223 baseEnd_281223 := by
    simpa [prefixWord, tailWord_281223, baseEnd_281223] using wordTrace_append hprefix tailTrace_281223
  have hstable : (prefixWord ++ tailWord_281223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281223).length < 2 ^ (prefixWord ++ tailWord_281223).sum := by decide
  have hdescent : baseEnd_281223 < baseStart_281223 := by decide
  rcases family_descends (prefixWord ++ tailWord_281223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281271 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_281271 : Nat := 118140960795 + 281271 * 2 ^ 59
def prefixEnd_281271 : Nat := 4983230072969 + 3 ^ 40 * 281271 * 2
def baseEnd_281271 : Nat := 128379748596332675216857

theorem tailTrace_281271 : CollatzResearch.WordTrace tailWord_281271 prefixEnd_281271 128379748596332675216857 := by
  unfold tailWord_281271
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258796164010679107467667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6839197442673786071645111 10258796164010679107467667)
  ·
    refine ⟨15388194246016018661201501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10258796164010679107467667 15388194246016018661201501)
    ·
      refine ⟨5770572842256006997950563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15388194246016018661201501 5770572842256006997950563)
      ·
        refine ⟨8655859263384010496925845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5770572842256006997950563 8655859263384010496925845)
        ·
          refine ⟨405743402971125492043399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8655859263384010496925845 405743402971125492043399)
          ·
            refine ⟨608615104456688238065099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405743402971125492043399 608615104456688238065099)
            ·
              refine ⟨912922656685032357097649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608615104456688238065099 912922656685032357097649)
              ·
                refine ⟨684691992513774267823237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912922656685032357097649 684691992513774267823237)
                ·
                  refine ⟨128379748596332675216857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684691992513774267823237 128379748596332675216857)
                  ·
                    rfl

theorem cell20_281271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_281271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281271 prefixEnd_281271 := by exact prefixLift 281271
  have htrace : WordTrace (prefixWord ++ tailWord_281271) baseStart_281271 baseEnd_281271 := by
    simpa [prefixWord, tailWord_281271, baseEnd_281271] using wordTrace_append hprefix tailTrace_281271
  have hstable : (prefixWord ++ tailWord_281271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281271).length < 2 ^ (prefixWord ++ tailWord_281271).sum := by decide
  have hdescent : baseEnd_281271 < baseStart_281271 := by decide
  rcases family_descends (prefixWord ++ tailWord_281271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281288 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 2]
def baseStart_281288 : Nat := 118140960795 + 281288 * 2 ^ 59
def prefixEnd_281288 : Nat := 4983230072969 + 3 ^ 40 * 281288 * 2
def baseEnd_281288 : Nat := 128387507859556171650121

theorem tailTrace_281288 : CollatzResearch.WordTrace tailWord_281288 prefixEnd_281288 128387507859556171650121 := by
  unfold tailWord_281288
  simp only [CollatzResearch.WordTrace]
  refine ⟨5129708102474545505418259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6839610803299394007224345 5129708102474545505418259)
  ·
    refine ⟨7694562153711818258127389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5129708102474545505418259 7694562153711818258127389)
    ·
      refine ⟨2885460807641931846797771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7694562153711818258127389 2885460807641931846797771)
      ·
        refine ⟨4328191211462897770196657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2885460807641931846797771 4328191211462897770196657)
        ·
          refine ⟨3246143408597173327647493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4328191211462897770196657 3246143408597173327647493)
          ·
            refine ⟨608651889111969998933905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3246143408597173327647493 608651889111969998933905)
            ·
              refine ⟨456488916833977499200429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608651889111969998933905 456488916833977499200429)
              ·
                refine ⟨171183343812741562200161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456488916833977499200429 171183343812741562200161)
                ·
                  refine ⟨128387507859556171650121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171183343812741562200161 128387507859556171650121)
                  ·
                    rfl

theorem cell20_281288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_281288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281288 prefixEnd_281288 := by exact prefixLift 281288
  have htrace : WordTrace (prefixWord ++ tailWord_281288) baseStart_281288 baseEnd_281288 := by
    simpa [prefixWord, tailWord_281288, baseEnd_281288] using wordTrace_append hprefix tailTrace_281288
  have hstable : (prefixWord ++ tailWord_281288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281288).length < 2 ^ (prefixWord ++ tailWord_281288).sum := by decide
  have hdescent : baseEnd_281288 < baseStart_281288 := by decide
  rcases family_descends (prefixWord ++ tailWord_281288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281298 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_281298 : Nat := 118140960795 + 281298 * 2 ^ 59
def prefixEnd_281298 : Nat := 4983230072969 + 3 ^ 40 * 281298 * 2
def baseEnd_281298 : Nat := 128392072132040581316747

theorem tailTrace_281298 : CollatzResearch.WordTrace tailWord_281298 prefixEnd_281298 128392072132040581316747 := by
  unfold tailWord_281298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564945233728215679675137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6839853956608575145800365 2564945233728215679675137)
  ·
    refine ⟨1923708925296161759756353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2564945233728215679675137 1923708925296161759756353)
    ·
      refine ⟨1442781693972121319817265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1923708925296161759756353 1442781693972121319817265)
      ·
        refine ⟨1082086270479090989862949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1442781693972121319817265 1082086270479090989862949)
        ·
          refine ⟨202891175714829560599303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1082086270479090989862949 202891175714829560599303)
          ·
            refine ⟨304336763572244340898955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202891175714829560599303 304336763572244340898955)
            ·
              refine ⟨456505145358366511348433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304336763572244340898955 456505145358366511348433)
              ·
                refine ⟨342378859018774883511325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456505145358366511348433 342378859018774883511325)
                ·
                  refine ⟨128392072132040581316747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342378859018774883511325 128392072132040581316747)
                  ·
                    rfl

theorem cell20_281298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_281298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281298 prefixEnd_281298 := by exact prefixLift 281298
  have htrace : WordTrace (prefixWord ++ tailWord_281298) baseStart_281298 baseEnd_281298 := by
    simpa [prefixWord, tailWord_281298, baseEnd_281298] using wordTrace_append hprefix tailTrace_281298
  have hstable : (prefixWord ++ tailWord_281298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281298).length < 2 ^ (prefixWord ++ tailWord_281298).sum := by decide
  have hdescent : baseEnd_281298 < baseStart_281298 := by decide
  rcases family_descends (prefixWord ++ tailWord_281298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281375 : List Nat := [1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_281375 : Nat := 118140960795 + 281375 * 2 ^ 59
def prefixEnd_281375 : Nat := 4983230072969 + 3 ^ 40 * 281375 * 2
def baseEnd_281375 : Nat := 42809072343390178583255

theorem tailTrace_281375 : CollatzResearch.WordTrace tailWord_281375 prefixEnd_281375 42809072343390178583255 := by
  unfold tailWord_281375
  simp only [CollatzResearch.WordTrace]
  refine ⟨10262589355633904869253579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6841726237089269912835719 10262589355633904869253579)
  ·
    refine ⟨15393884033450857303880369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10262589355633904869253579 15393884033450857303880369)
    ·
      refine ⟨11545413025088142977910277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15393884033450857303880369 11545413025088142977910277)
      ·
        refine ⟨2164764942204026808358177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11545413025088142977910277 2164764942204026808358177)
        ·
          refine ⟨1623573706653020106268633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2164764942204026808358177 1623573706653020106268633)
          ·
            refine ⟨1217680279989765079701475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623573706653020106268633 1217680279989765079701475)
            ·
              refine ⟨1826520419984647619552213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217680279989765079701475 1826520419984647619552213)
              ·
                refine ⟨42809072343390178583255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1826520419984647619552213 42809072343390178583255)
                ·
                  rfl

theorem cell20_281375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_281375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281375 prefixEnd_281375 := by exact prefixLift 281375
  have htrace : WordTrace (prefixWord ++ tailWord_281375) baseStart_281375 baseEnd_281375 := by
    simpa [prefixWord, tailWord_281375, baseEnd_281375] using wordTrace_append hprefix tailTrace_281375
  have hstable : (prefixWord ++ tailWord_281375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281375).length < 2 ^ (prefixWord ++ tailWord_281375).sum := by decide
  have hdescent : baseEnd_281375 < baseStart_281375 := by decide
  rcases family_descends (prefixWord ++ tailWord_281375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281378 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_281378 : Nat := 118140960795 + 281378 * 2 ^ 59
def prefixEnd_281378 : Nat := 4983230072969 + 3 ^ 40 * 281378 * 2
def baseEnd_281378 : Nat := 128428586311915858649753

theorem tailTrace_281378 : CollatzResearch.WordTrace tailWord_281378 prefixEnd_281378 128428586311915858649753 := by
  unfold tailWord_281378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565674693655759095403197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6841799183082024254408525 2565674693655759095403197)
  ·
    refine ⟨962128010120909660776199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2565674693655759095403197 962128010120909660776199)
    ·
      refine ⟨1443192015181364491164299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962128010120909660776199 1443192015181364491164299)
      ·
        refine ⟨2164788022772046736746449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443192015181364491164299 2164788022772046736746449)
        ·
          refine ⟨1623591017079035052559837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2164788022772046736746449 1623591017079035052559837)
          ·
            refine ⟨608846631404638144709939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1623591017079035052559837 608846631404638144709939)
            ·
              refine ⟨913269947106957217064909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608846631404638144709939 913269947106957217064909)
              ·
                refine ⟨342476230165108956399341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913269947106957217064909 342476230165108956399341)
                ·
                  refine ⟨128428586311915858649753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342476230165108956399341 128428586311915858649753)
                  ·
                    rfl

theorem cell20_281378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_281378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281378 prefixEnd_281378 := by exact prefixLift 281378
  have htrace : WordTrace (prefixWord ++ tailWord_281378) baseStart_281378 baseEnd_281378 := by
    simpa [prefixWord, tailWord_281378, baseEnd_281378] using wordTrace_append hprefix tailTrace_281378
  have hstable : (prefixWord ++ tailWord_281378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281378).length < 2 ^ (prefixWord ++ tailWord_281378).sum := by decide
  have hdescent : baseEnd_281378 < baseStart_281378 := by decide
  rcases family_descends (prefixWord ++ tailWord_281378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281409 : List Nat := [1, 2, 5, 3, 2, 7]
def baseStart_281409 : Nat := 118140960795 + 281409 * 2 ^ 59
def prefixEnd_281409 : Nat := 4983230072969 + 3 ^ 40 * 281409 * 2
def baseEnd_281409 : Nat := 4757138353948797356159

theorem tailTrace_281409 : CollatzResearch.WordTrace tailWord_281409 prefixEnd_281409 4757138353948797356159 := by
  unfold tailWord_281409
  simp only [CollatzResearch.WordTrace]
  refine ⟨10263829437510728675991281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6842552958340485783994187 10263829437510728675991281)
  ·
    refine ⟨7697872078133046506993461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10263829437510728675991281 7697872078133046506993461)
    ·
      refine ⟨721675507324973110030637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7697872078133046506993461 721675507324973110030637)
      ·
        refine ⟨270628315246864916261489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 721675507324973110030637 270628315246864916261489)
        ·
          refine ⟨202971236435148687196117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270628315246864916261489 202971236435148687196117)
          ·
            refine ⟨4757138353948797356159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202971236435148687196117 4757138353948797356159)
            ·
              rfl

theorem cell20_281409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 7].length) (baseStart_281409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281409 prefixEnd_281409 := by exact prefixLift 281409
  have htrace : WordTrace (prefixWord ++ tailWord_281409) baseStart_281409 baseEnd_281409 := by
    simpa [prefixWord, tailWord_281409, baseEnd_281409] using wordTrace_append hprefix tailTrace_281409
  have hstable : (prefixWord ++ tailWord_281409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281409).length < 2 ^ (prefixWord ++ tailWord_281409).sum := by decide
  have hdescent : baseEnd_281409 < baseStart_281409 := by decide
  rcases family_descends (prefixWord ++ tailWord_281409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281412 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_281412 : Nat := 118140960795 + 281412 * 2 ^ 59
def prefixEnd_281412 : Nat := 4983230072969 + 3 ^ 40 * 281412 * 2
def baseEnd_281412 : Nat := 128444104838362851516281

theorem tailTrace_281412 : CollatzResearch.WordTrace tailWord_281412 prefixEnd_281412 128444104838362851516281 := by
  unfold tailWord_281412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131969428249930094175245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6842625904333240125566993 5131969428249930094175245)
  ·
    refine ⟨1924488535593723785315717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5131969428249930094175245 1924488535593723785315717)
    ·
      refine ⟨360841600423823209746697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1924488535593723785315717 360841600423823209746697)
      ·
        refine ⟨270631200317867407310023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360841600423823209746697 270631200317867407310023)
        ·
          refine ⟨405946800476801110965035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270631200317867407310023 405946800476801110965035)
          ·
            refine ⟨608920200715201666447553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405946800476801110965035 608920200715201666447553)
            ·
              refine ⟨456690150536401249835665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608920200715201666447553 456690150536401249835665)
              ·
                refine ⟨342517612902300937376749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 456690150536401249835665 342517612902300937376749)
                ·
                  refine ⟨128444104838362851516281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342517612902300937376749 128444104838362851516281)
                  ·
                    rfl

theorem cell20_281412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_281412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281412 prefixEnd_281412 := by exact prefixLift 281412
  have htrace : WordTrace (prefixWord ++ tailWord_281412) baseStart_281412 baseEnd_281412 := by
    simpa [prefixWord, tailWord_281412, baseEnd_281412] using wordTrace_append hprefix tailTrace_281412
  have hstable : (prefixWord ++ tailWord_281412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281412).length < 2 ^ (prefixWord ++ tailWord_281412).sum := by decide
  have hdescent : baseEnd_281412 < baseStart_281412 := by decide
  rcases family_descends (prefixWord ++ tailWord_281412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281427 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_281427 : Nat := 118140960795 + 281427 * 2 ^ 59
def prefixEnd_281427 : Nat := 4983230072969 + 3 ^ 40 * 281427 * 2
def baseEnd_281427 : Nat := 128450951247089466016219

theorem tailTrace_281427 : CollatzResearch.WordTrace tailWord_281427 prefixEnd_281427 128450951247089466016219 := by
  unfold tailWord_281427
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264485951445517750146535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6842990634297011833431023 10264485951445517750146535)
  ·
    refine ⟨15396728927168276625219803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10264485951445517750146535 15396728927168276625219803)
    ·
      refine ⟨23095093390752414937829705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15396728927168276625219803 23095093390752414937829705)
      ·
        refine ⟨17321320043064311203372279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23095093390752414937829705 17321320043064311203372279)
        ·
          refine ⟨25981980064596466805058419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17321320043064311203372279 25981980064596466805058419)
          ·
            refine ⟨38972970096894700207587629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25981980064596466805058419 38972970096894700207587629)
            ·
              refine ⟨14614863786335512577845361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38972970096894700207587629 14614863786335512577845361)
              ·
                refine ⟨10961147839751634433384021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14614863786335512577845361 10961147839751634433384021)
                ·
                  refine ⟨128450951247089466016219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10961147839751634433384021 128450951247089466016219)
                  ·
                    rfl

theorem cell20_281427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_281427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281427 prefixEnd_281427 := by exact prefixLift 281427
  have htrace : WordTrace (prefixWord ++ tailWord_281427) baseStart_281427 baseEnd_281427 := by
    simpa [prefixWord, tailWord_281427, baseEnd_281427] using wordTrace_append hprefix tailTrace_281427
  have hstable : (prefixWord ++ tailWord_281427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281427).length < 2 ^ (prefixWord ++ tailWord_281427).sum := by decide
  have hdescent : baseEnd_281427 < baseStart_281427 := by decide
  rcases family_descends (prefixWord ++ tailWord_281427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281444 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_281444 : Nat := 118140960795 + 281444 * 2 ^ 59
def prefixEnd_281444 : Nat := 4983230072969 + 3 ^ 40 * 281444 * 2
def baseEnd_281444 : Nat := 128458710510312962449483

theorem tailTrace_281444 : CollatzResearch.WordTrace tailWord_281444 prefixEnd_281444 128458710510312962449483 := by
  unfold tailWord_281444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132552996191964826757693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6843403994922619769010257 5132552996191964826757693)
  ·
    refine ⟨1924707373571986810034135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5132552996191964826757693 1924707373571986810034135)
    ·
      refine ⟨2887061060357980215051203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1924707373571986810034135 2887061060357980215051203)
      ·
        refine ⟨4330591590536970322576805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2887061060357980215051203 4330591590536970322576805)
        ·
          refine ⟨811985923225681935483151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4330591590536970322576805 811985923225681935483151)
          ·
            refine ⟨1217978884838522903224727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811985923225681935483151 1217978884838522903224727)
            ·
              refine ⟨1826968327257784354837091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217978884838522903224727 1826968327257784354837091)
              ·
                refine ⟨2740452490886676532255637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1826968327257784354837091 2740452490886676532255637)
                ·
                  refine ⟨128458710510312962449483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2740452490886676532255637 128458710510312962449483)
                  ·
                    rfl

theorem cell20_281444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_281444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281444 prefixEnd_281444 := by exact prefixLift 281444
  have htrace : WordTrace (prefixWord ++ tailWord_281444) baseStart_281444 baseEnd_281444 := by
    simpa [prefixWord, tailWord_281444, baseEnd_281444] using wordTrace_append hprefix tailTrace_281444
  have hstable : (prefixWord ++ tailWord_281444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281444).length < 2 ^ (prefixWord ++ tailWord_281444).sum := by decide
  have hdescent : baseEnd_281444 < baseStart_281444 := by decide
  rcases family_descends (prefixWord ++ tailWord_281444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281506 : List Nat := [3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_281506 : Nat := 118140960795 + 281506 * 2 ^ 59
def prefixEnd_281506 : Nat := 4983230072969 + 3 ^ 40 * 281506 * 2
def baseEnd_281506 : Nat := 42829002999905434127521

theorem tailTrace_281506 : CollatzResearch.WordTrace tailWord_281506 prefixEnd_281506 42829002999905434127521 := by
  unfold tailWord_281506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566841829539828560568093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6844911545439542828181581 2566841829539828560568093)
  ·
    refine ⟨962565686077435710213035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2566841829539828560568093 962565686077435710213035)
    ·
      refine ⟨1443848529116153565319553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962565686077435710213035 1443848529116153565319553)
      ·
        refine ⟨1082886396837115173989665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1443848529116153565319553 1082886396837115173989665)
        ·
          refine ⟨812164797627836380492249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082886396837115173989665 812164797627836380492249)
          ·
            refine ⟨609123598220877285369187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812164797627836380492249 609123598220877285369187)
            ·
              refine ⟨913685397331315928053781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609123598220877285369187 913685397331315928053781)
              ·
                refine ⟨42829002999905434127521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 913685397331315928053781 42829002999905434127521)
                ·
                  rfl

theorem cell20_281506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_281506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281506 prefixEnd_281506 := by exact prefixLift 281506
  have htrace : WordTrace (prefixWord ++ tailWord_281506) baseStart_281506 baseEnd_281506 := by
    simpa [prefixWord, tailWord_281506, baseEnd_281506] using wordTrace_append hprefix tailTrace_281506
  have hstable : (prefixWord ++ tailWord_281506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281506).length < 2 ^ (prefixWord ++ tailWord_281506).sum := by decide
  have hdescent : baseEnd_281506 < baseStart_281506 := by decide
  rcases family_descends (prefixWord ++ tailWord_281506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281533 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 2]
def baseStart_281533 : Nat := 118140960795 + 281533 * 2 ^ 59
def prefixEnd_281533 : Nat := 4983230072969 + 3 ^ 40 * 281533 * 2
def baseEnd_281533 : Nat := 128499332535424208482453

theorem tailTrace_281533 : CollatzResearch.WordTrace tailWord_281533 prefixEnd_281533 128499332535424208482453 := by
  unfold tailWord_281533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268352089061497853505253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6845568059374331902336835 10268352089061497853505253)
  ·
    refine ⟨1925316016699030847532235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10268352089061497853505253 1925316016699030847532235)
    ·
      refine ⟨2887974025048546271298353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925316016699030847532235 2887974025048546271298353)
      ·
        refine ⟨2165980518786409703473765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2887974025048546271298353 2165980518786409703473765)
        ·
          refine ⟨406121347272451819401331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2165980518786409703473765 406121347272451819401331)
          ·
            refine ⟨609182020908677729101997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406121347272451819401331 609182020908677729101997)
            ·
              refine ⟨228443257840754148413249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609182020908677729101997 228443257840754148413249)
              ·
                refine ⟨171332443380565611309937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228443257840754148413249 171332443380565611309937)
                ·
                  refine ⟨128499332535424208482453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171332443380565611309937 128499332535424208482453)
                  ·
                    rfl

theorem cell20_281533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_281533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281533 prefixEnd_281533 := by exact prefixLift 281533
  have htrace : WordTrace (prefixWord ++ tailWord_281533) baseStart_281533 baseEnd_281533 := by
    simpa [prefixWord, tailWord_281533, baseEnd_281533] using wordTrace_append hprefix tailTrace_281533
  have hstable : (prefixWord ++ tailWord_281533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281533).length < 2 ^ (prefixWord ++ tailWord_281533).sum := by decide
  have hdescent : baseEnd_281533 < baseStart_281533 := by decide
  rcases family_descends (prefixWord ++ tailWord_281533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281544 : List Nat := [2, 1, 3, 1, 5, 1, 2, 5]
def baseStart_281544 : Nat := 118140960795 + 281544 * 2 ^ 59
def prefixEnd_281544 : Nat := 4983230072969 + 3 ^ 40 * 281544 * 2
def baseEnd_281544 : Nat := 42834784411719019705247

theorem tailTrace_281544 : CollatzResearch.WordTrace tailWord_281544 prefixEnd_281544 42834784411719019705247 := by
  unfold tailWord_281544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134376646010823366077843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6845835528014431154770457 5134376646010823366077843)
  ·
    refine ⟨7701564969016235049116765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5134376646010823366077843 7701564969016235049116765)
    ·
      refine ⟨2888086863381088143418787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7701564969016235049116765 2888086863381088143418787)
      ·
        refine ⟨4332130295071632215128181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888086863381088143418787 4332130295071632215128181)
        ·
          refine ⟨406137215162965520168267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4332130295071632215128181 406137215162965520168267)
          ·
            refine ⟨609205822744448280252401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406137215162965520168267 609205822744448280252401)
            ·
              refine ⟨456904367058336210189301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609205822744448280252401 456904367058336210189301)
              ·
                refine ⟨42834784411719019705247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 456904367058336210189301 42834784411719019705247)
                ·
                  rfl

theorem cell20_281544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_281544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281544 prefixEnd_281544 := by exact prefixLift 281544
  have htrace : WordTrace (prefixWord ++ tailWord_281544) baseStart_281544 baseEnd_281544 := by
    simpa [prefixWord, tailWord_281544, baseEnd_281544] using wordTrace_append hprefix tailTrace_281544
  have hstable : (prefixWord ++ tailWord_281544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281544).length < 2 ^ (prefixWord ++ tailWord_281544).sum := by decide
  have hdescent : baseEnd_281544 < baseStart_281544 := by decide
  rcases family_descends (prefixWord ++ tailWord_281544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281551 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 3]
def baseStart_281551 : Nat := 118140960795 + 281551 * 2 ^ 59
def prefixEnd_281551 : Nat := 4983230072969 + 3 ^ 40 * 281551 * 2
def baseEnd_281551 : Nat := 128507548225896145882379

theorem tailTrace_281551 : CollatzResearch.WordTrace tailWord_281551 prefixEnd_281551 128507548225896145882379 := by
  unfold tailWord_281551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10269008602996286927660507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6846005735330857951773671 10269008602996286927660507)
  ·
    refine ⟨15403512904494430391490761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10269008602996286927660507 15403512904494430391490761)
    ·
      refine ⟨11552634678370822793618071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15403512904494430391490761 11552634678370822793618071)
      ·
        refine ⟨17328952017556234190427107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11552634678370822793618071 17328952017556234190427107)
        ·
          refine ⟨25993428026334351285640661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17328952017556234190427107 25993428026334351285640661)
          ·
            refine ⟨609220969367211358257203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25993428026334351285640661 609220969367211358257203)
            ·
              refine ⟨913831454050817037385805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609220969367211358257203 913831454050817037385805)
              ·
                refine ⟨342686795269056389019677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 913831454050817037385805 342686795269056389019677)
                ·
                  refine ⟨128507548225896145882379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342686795269056389019677 128507548225896145882379)
                  ·
                    rfl

theorem cell20_281551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 3].length) (baseStart_281551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281551 prefixEnd_281551 := by exact prefixLift 281551
  have htrace : WordTrace (prefixWord ++ tailWord_281551) baseStart_281551 baseEnd_281551 := by
    simpa [prefixWord, tailWord_281551, baseEnd_281551] using wordTrace_append hprefix tailTrace_281551
  have hstable : (prefixWord ++ tailWord_281551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281551).length < 2 ^ (prefixWord ++ tailWord_281551).sum := by decide
  have hdescent : baseEnd_281551 < baseStart_281551 := by decide
  rcases family_descends (prefixWord ++ tailWord_281551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281572 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_281572 : Nat := 118140960795 + 281572 * 2 ^ 59
def prefixEnd_281572 : Nat := 4983230072969 + 3 ^ 40 * 281572 * 2
def baseEnd_281572 : Nat := 128517133198113406182293

theorem tailTrace_281572 : CollatzResearch.WordTrace tailWord_281572 prefixEnd_281572 128517133198113406182293 := by
  unfold tailWord_281572
  simp only [CollatzResearch.WordTrace]
  refine ⟨5134887267960103757087485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6846516357280138342783313 5134887267960103757087485)
  ·
    refine ⟨1925582725485038908907807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5134887267960103757087485 1925582725485038908907807)
    ·
      refine ⟨2888374088227558363361711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925582725485038908907807 2888374088227558363361711)
      ·
        refine ⟨4332561132341337545042567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888374088227558363361711 4332561132341337545042567)
        ·
          refine ⟨6498841698512006317563851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332561132341337545042567 6498841698512006317563851)
          ·
            refine ⟨9748262547768009476345777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6498841698512006317563851 9748262547768009476345777)
            ·
              refine ⟨7311196910826007107259333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9748262547768009476345777 7311196910826007107259333)
              ·
                refine ⟨1370849420779876332611125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7311196910826007107259333 1370849420779876332611125)
                ·
                  refine ⟨128517133198113406182293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1370849420779876332611125 128517133198113406182293)
                  ·
                    rfl

theorem cell20_281572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_281572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281572 prefixEnd_281572 := by exact prefixLift 281572
  have htrace : WordTrace (prefixWord ++ tailWord_281572) baseStart_281572 baseEnd_281572 := by
    simpa [prefixWord, tailWord_281572, baseEnd_281572] using wordTrace_append hprefix tailTrace_281572
  have hstable : (prefixWord ++ tailWord_281572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281572).length < 2 ^ (prefixWord ++ tailWord_281572).sum := by decide
  have hdescent : baseEnd_281572 < baseStart_281572 := by decide
  rcases family_descends (prefixWord ++ tailWord_281572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281582 : List Nat := [4, 1, 2, 1, 5, 7]
def baseStart_281582 : Nat := 118140960795 + 281582 * 2 ^ 59
def prefixEnd_281582 : Nat := 4983230072969 + 3 ^ 40 * 281582 * 2
def baseEnd_281582 : Nat := 4760062869281400586997

theorem tailTrace_281582 : CollatzResearch.WordTrace tailWord_281582 prefixEnd_281582 4760062869281400586997 := by
  unfold tailWord_281582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283767408235497402754875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6846759510589319481359333 1283767408235497402754875)
  ·
    refine ⟨1925651112353246104132313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283767408235497402754875 1925651112353246104132313)
    ·
      refine ⟨1444238334264934578099235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1925651112353246104132313 1444238334264934578099235)
      ·
        refine ⟨2166357501397401867148853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1444238334264934578099235 2166357501397401867148853)
        ·
          refine ⟨203096015756006425045205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2166357501397401867148853 203096015756006425045205)
          ·
            refine ⟨4760062869281400586997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 203096015756006425045205 4760062869281400586997)
            ·
              rfl

theorem cell20_281582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 7].length) (baseStart_281582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281582 prefixEnd_281582 := by exact prefixLift 281582
  have htrace : WordTrace (prefixWord ++ tailWord_281582) baseStart_281582 baseEnd_281582 := by
    simpa [prefixWord, tailWord_281582, baseEnd_281582] using wordTrace_append hprefix tailTrace_281582
  have hstable : (prefixWord ++ tailWord_281582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281582).length < 2 ^ (prefixWord ++ tailWord_281582).sum := by decide
  have hdescent : baseEnd_281582 < baseStart_281582 := by decide
  rcases family_descends (prefixWord ++ tailWord_281582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281648 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_281648 : Nat := 118140960795 + 281648 * 2 ^ 59
def prefixEnd_281648 : Nat := 4983230072969 + 3 ^ 40 * 281648 * 2
def baseEnd_281648 : Nat := 128551821668994919648649

theorem tailTrace_281648 : CollatzResearch.WordTrace tailWord_281648 prefixEnd_281648 128551821668994919648649 := by
  unfold tailWord_281648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136273241822436246970799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6848364322429914995961065 5136273241822436246970799)
  ·
    refine ⟨7704409862733654370456199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5136273241822436246970799 7704409862733654370456199)
    ·
      refine ⟨11556614794100481555684299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7704409862733654370456199 11556614794100481555684299)
      ·
        refine ⟨17334922191150722333526449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11556614794100481555684299 17334922191150722333526449)
        ·
          refine ⟨13001191643363041750144837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17334922191150722333526449 13001191643363041750144837)
          ·
            refine ⟨2437723433130570328152157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13001191643363041750144837 2437723433130570328152157)
            ·
              refine ⟨914146287423963873057059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2437723433130570328152157 914146287423963873057059)
              ·
                refine ⟨1371219431135945809585589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914146287423963873057059 1371219431135945809585589)
                ·
                  refine ⟨128551821668994919648649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1371219431135945809585589 128551821668994919648649)
                  ·
                    rfl

theorem cell20_281648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_281648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281648 prefixEnd_281648 := by exact prefixLift 281648
  have htrace : WordTrace (prefixWord ++ tailWord_281648) baseStart_281648 baseEnd_281648 := by
    simpa [prefixWord, tailWord_281648, baseEnd_281648] using wordTrace_append hprefix tailTrace_281648
  have hstable : (prefixWord ++ tailWord_281648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281648).length < 2 ^ (prefixWord ++ tailWord_281648).sum := by decide
  have hdescent : baseEnd_281648 < baseStart_281648 := by decide
  rcases family_descends (prefixWord ++ tailWord_281648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281731 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_281731 : Nat := 118140960795 + 281731 * 2 ^ 59
def prefixEnd_281731 : Nat := 4983230072969 + 3 ^ 40 * 281731 * 2
def baseEnd_281731 : Nat := 128589705130615519881643

theorem tailTrace_281731 : CollatzResearch.WordTrace tailWord_281731 prefixEnd_281731 128589705130615519881643 := by
  unfold tailWord_281731
  simp only [CollatzResearch.WordTrace]
  refine ⟨10275573742344177669213047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6850382494896118446142031 10275573742344177669213047)
  ·
    refine ⟨15413360613516266503819571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10275573742344177669213047 15413360613516266503819571)
    ·
      refine ⟨23120040920274399755729357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15413360613516266503819571 23120040920274399755729357)
      ·
        refine ⟨8670015345102899908398509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23120040920274399755729357 8670015345102899908398509)
        ·
          refine ⟨3251255754413587465649441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8670015345102899908398509 3251255754413587465649441)
          ·
            refine ⟨2438441815810190599237081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3251255754413587465649441 2438441815810190599237081)
            ·
              refine ⟨1828831361857642949427811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438441815810190599237081 1828831361857642949427811)
              ·
                refine ⟨2743247042786464424141717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828831361857642949427811 2743247042786464424141717)
                ·
                  refine ⟨128589705130615519881643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2743247042786464424141717 128589705130615519881643)
                  ·
                    rfl

theorem cell20_281731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_281731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281731 prefixEnd_281731 := by exact prefixLift 281731
  have htrace : WordTrace (prefixWord ++ tailWord_281731) baseStart_281731 baseEnd_281731 := by
    simpa [prefixWord, tailWord_281731, baseEnd_281731] using wordTrace_append hprefix tailTrace_281731
  have hstable : (prefixWord ++ tailWord_281731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281731).length < 2 ^ (prefixWord ++ tailWord_281731).sum := by decide
  have hdescent : baseEnd_281731 < baseStart_281731 := by decide
  rcases family_descends (prefixWord ++ tailWord_281731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281758 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_281758 : Nat := 118140960795 + 281758 * 2 ^ 59
def prefixEnd_281758 : Nat := 4983230072969 + 3 ^ 40 * 281758 * 2
def baseEnd_281758 : Nat := 128602028666323425981533

theorem tailTrace_281758 : CollatzResearch.WordTrace tailWord_281758 prefixEnd_281758 128602028666323425981533 := by
  unfold tailWord_281758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284569814155795160055741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6851039008830907520297285 1284569814155795160055741)
  ·
    refine ⟨481713680308423185020903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1284569814155795160055741 481713680308423185020903)
    ·
      refine ⟨722570520462634777531355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 481713680308423185020903 722570520462634777531355)
      ·
        refine ⟨1083855780693952166297033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722570520462634777531355 1083855780693952166297033)
        ·
          refine ⟨812891835520464124722775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083855780693952166297033 812891835520464124722775)
          ·
            refine ⟨1219337753280696187084163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812891835520464124722775 1219337753280696187084163)
            ·
              refine ⟨1829006629921044280626245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219337753280696187084163 1829006629921044280626245)
              ·
                refine ⟨342938743110195802617421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1829006629921044280626245 342938743110195802617421)
                ·
                  refine ⟨128602028666323425981533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 342938743110195802617421 128602028666323425981533)
                  ·
                    rfl

theorem cell20_281758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_281758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281758 prefixEnd_281758 := by exact prefixLift 281758
  have htrace : WordTrace (prefixWord ++ tailWord_281758) baseStart_281758 baseEnd_281758 := by
    simpa [prefixWord, tailWord_281758, baseEnd_281758] using wordTrace_append hprefix tailTrace_281758
  have hstable : (prefixWord ++ tailWord_281758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281758).length < 2 ^ (prefixWord ++ tailWord_281758).sum := by decide
  have hdescent : baseEnd_281758 < baseStart_281758 := by decide
  rcases family_descends (prefixWord ++ tailWord_281758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281765 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 2]
def baseStart_281765 : Nat := 118140960795 + 281765 * 2 ^ 59
def prefixEnd_281765 : Nat := 4983230072969 + 3 ^ 40 * 281765 * 2
def baseEnd_281765 : Nat := 128605223657062512748171

theorem tailTrace_281765 : CollatzResearch.WordTrace tailWord_281765 prefixEnd_281765 128605223657062512748171 := by
  unfold tailWord_281765
  simp only [CollatzResearch.WordTrace]
  refine ⟨10276813824221001475950749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6851209216147334317300499 10276813824221001475950749)
  ·
    refine ⟨3853805184082875553481531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10276813824221001475950749 3853805184082875553481531)
    ·
      refine ⟨5780707776124313330222297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853805184082875553481531 5780707776124313330222297)
      ·
        refine ⟨4335530832093234997666723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5780707776124313330222297 4335530832093234997666723)
        ·
          refine ⟨6503296248139852496500085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4335530832093234997666723 6503296248139852496500085)
          ·
            refine ⟨609684023263111171546883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6503296248139852496500085 609684023263111171546883)
            ·
              refine ⟨914526034894666757320325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609684023263111171546883 914526034894666757320325)
              ·
                refine ⟨171473631542750016997561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 914526034894666757320325 171473631542750016997561)
                ·
                  refine ⟨128605223657062512748171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171473631542750016997561 128605223657062512748171)
                  ·
                    rfl

theorem cell20_281765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_281765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281765 prefixEnd_281765 := by exact prefixLift 281765
  have htrace : WordTrace (prefixWord ++ tailWord_281765) baseStart_281765 baseEnd_281765 := by
    simpa [prefixWord, tailWord_281765, baseEnd_281765] using wordTrace_append hprefix tailTrace_281765
  have hstable : (prefixWord ++ tailWord_281765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281765).length < 2 ^ (prefixWord ++ tailWord_281765).sum := by decide
  have hdescent : baseEnd_281765 < baseStart_281765 := by decide
  rcases family_descends (prefixWord ++ tailWord_281765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281824 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_281824 : Nat := 118140960795 + 281824 * 2 ^ 59
def prefixEnd_281824 : Nat := 4983230072969 + 3 ^ 40 * 281824 * 2
def baseEnd_281824 : Nat := 128632152864720529781263

theorem tailTrace_281824 : CollatzResearch.WordTrace tailWord_281824 prefixEnd_281824 128632152864720529781263 := by
  unfold tailWord_281824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139482865503627276174263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6852643820671503034899017 5139482865503627276174263)
  ·
    refine ⟨7709224298255440914261395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5139482865503627276174263 7709224298255440914261395)
    ·
      refine ⟨11563836447383161371392093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7709224298255440914261395 11563836447383161371392093)
      ·
        refine ⟨4336438667768685514272035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11563836447383161371392093 4336438667768685514272035)
        ·
          refine ⟨6504658001653028271408053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4336438667768685514272035 6504658001653028271408053)
          ·
            refine ⟨609811687654971400444505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6504658001653028271408053 609811687654971400444505)
            ·
              refine ⟨457358765741228550333379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609811687654971400444505 457358765741228550333379)
              ·
                refine ⟨686038148611842825500069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457358765741228550333379 686038148611842825500069)
                ·
                  refine ⟨128632152864720529781263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686038148611842825500069 128632152864720529781263)
                  ·
                    rfl

theorem cell20_281824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_281824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281824 prefixEnd_281824 := by exact prefixLift 281824
  have htrace : WordTrace (prefixWord ++ tailWord_281824) baseStart_281824 baseEnd_281824 := by
    simpa [prefixWord, tailWord_281824, baseEnd_281824] using wordTrace_append hprefix tailTrace_281824
  have hstable : (prefixWord ++ tailWord_281824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281824).length < 2 ^ (prefixWord ++ tailWord_281824).sum := by decide
  have hdescent : baseEnd_281824 < baseStart_281824 := by decide
  rcases family_descends (prefixWord ++ tailWord_281824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281834 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_281834 : Nat := 118140960795 + 281834 * 2 ^ 59
def prefixEnd_281834 : Nat := 4983230072969 + 3 ^ 40 * 281834 * 2
def baseEnd_281834 : Nat := 128636717137204939447889

theorem tailTrace_281834 : CollatzResearch.WordTrace tailWord_281834 prefixEnd_281834 128636717137204939447889 := by
  unfold tailWord_281834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569832615242756565053139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6852886973980684173475037 2569832615242756565053139)
  ·
    refine ⟨3854748922864134847579709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569832615242756565053139 3854748922864134847579709)
    ·
      refine ⟨1445530846074050567842391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3854748922864134847579709 1445530846074050567842391)
      ·
        refine ⟨2168296269111075851763587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445530846074050567842391 2168296269111075851763587)
        ·
          refine ⟨3252444403666613777645381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168296269111075851763587 3252444403666613777645381)
          ·
            refine ⟨609833325687490083308509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3252444403666613777645381 609833325687490083308509)
            ·
              refine ⟨228687497132808781240691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 609833325687490083308509 228687497132808781240691)
              ·
                refine ⟨343031245699213171861037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228687497132808781240691 343031245699213171861037)
                ·
                  refine ⟨128636717137204939447889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343031245699213171861037 128636717137204939447889)
                  ·
                    rfl

theorem cell20_281834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_281834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281834 prefixEnd_281834 := by exact prefixLift 281834
  have htrace : WordTrace (prefixWord ++ tailWord_281834) baseStart_281834 baseEnd_281834 := by
    simpa [prefixWord, tailWord_281834, baseEnd_281834] using wordTrace_append hprefix tailTrace_281834
  have hstable : (prefixWord ++ tailWord_281834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281834).length < 2 ^ (prefixWord ++ tailWord_281834).sum := by decide
  have hdescent : baseEnd_281834 < baseStart_281834 := by decide
  rcases family_descends (prefixWord ++ tailWord_281834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281844 : List Nat := [2, 6, 1, 2, 1, 1, 1, 6]
def baseStart_281844 : Nat := 118140960795 + 281844 * 2 ^ 59
def prefixEnd_281844 : Nat := 4983230072969 + 3 ^ 40 * 281844 * 2
def baseEnd_281844 : Nat := 42880427136563116371505

theorem tailTrace_281844 : CollatzResearch.WordTrace tailWord_281844 prefixEnd_281844 42880427136563116371505 := by
  unfold tailWord_281844
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139847595467398984038293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6853130127289865312051057 5139847595467398984038293)
  ·
    refine ⟨240930356037534327376795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5139847595467398984038293 240930356037534327376795)
    ·
      refine ⟨361395534056301491065193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240930356037534327376795 361395534056301491065193)
      ·
        refine ⟨271046650542226118298895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361395534056301491065193 271046650542226118298895)
        ·
          refine ⟨406569975813339177448343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271046650542226118298895 406569975813339177448343)
          ·
            refine ⟨609854963720008766172515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406569975813339177448343 609854963720008766172515)
            ·
              refine ⟨914782445580013149258773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609854963720008766172515 914782445580013149258773)
              ·
                refine ⟨42880427136563116371505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 914782445580013149258773 42880427136563116371505)
                ·
                  rfl

theorem cell20_281844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_281844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281844 prefixEnd_281844 := by exact prefixLift 281844
  have htrace : WordTrace (prefixWord ++ tailWord_281844) baseStart_281844 baseEnd_281844 := by
    simpa [prefixWord, tailWord_281844, baseEnd_281844] using wordTrace_append hprefix tailTrace_281844
  have hstable : (prefixWord ++ tailWord_281844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281844).length < 2 ^ (prefixWord ++ tailWord_281844).sum := by decide
  have hdescent : baseEnd_281844 < baseStart_281844 := by decide
  rcases family_descends (prefixWord ++ tailWord_281844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281893 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 3]
def baseStart_281893 : Nat := 118140960795 + 281893 * 2 ^ 59
def prefixEnd_281893 : Nat := 4983230072969 + 3 ^ 40 * 281893 * 2
def baseEnd_281893 : Nat := 128663646344862956480981

theorem tailTrace_281893 : CollatzResearch.WordTrace tailWord_281893 prefixEnd_281893 128663646344862956480981 := by
  unfold tailWord_281893
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281482367757279336610333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6854321578504852891073555 10281482367757279336610333)
  ·
    refine ⟨3855555887908979751228875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10281482367757279336610333 3855555887908979751228875)
    ·
      refine ⟨5783333831863469626843313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855555887908979751228875 5783333831863469626843313)
      ·
        refine ⟨4337500373897602220132485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5783333831863469626843313 4337500373897602220132485)
        ·
          refine ⟨813281320105800416274841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4337500373897602220132485 813281320105800416274841)
          ·
            refine ⟨609960990079350312206131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 813281320105800416274841 609960990079350312206131)
            ·
              refine ⟨914941485119025468309197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 609960990079350312206131 914941485119025468309197)
              ·
                refine ⟨343103056919634550615949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 914941485119025468309197 343103056919634550615949)
                ·
                  refine ⟨128663646344862956480981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343103056919634550615949 128663646344862956480981)
                  ·
                    rfl

theorem cell20_281893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_281893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281893 prefixEnd_281893 := by exact prefixLift 281893
  have htrace : WordTrace (prefixWord ++ tailWord_281893) baseStart_281893 baseEnd_281893 := by
    simpa [prefixWord, tailWord_281893, baseEnd_281893] using wordTrace_append hprefix tailTrace_281893
  have hstable : (prefixWord ++ tailWord_281893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281893).length < 2 ^ (prefixWord ++ tailWord_281893).sum := by decide
  have hdescent : baseEnd_281893 < baseStart_281893 := by decide
  rcases family_descends (prefixWord ++ tailWord_281893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281926 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_281926 : Nat := 118140960795 + 281926 * 2 ^ 59
def prefixEnd_281926 : Nat := 4983230072969 + 3 ^ 40 * 281926 * 2
def baseEnd_281926 : Nat := 128678708444061508380847

theorem tailTrace_281926 : CollatzResearch.WordTrace tailWord_281926 prefixEnd_281926 128678708444061508380847 := by
  unfold tailWord_281926
  simp only [CollatzResearch.WordTrace]
  refine ⟨321333936769928936642551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6855123984425150648374421 321333936769928936642551)
  ·
    refine ⟨482000905154893404963827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 321333936769928936642551 482000905154893404963827)
    ·
      refine ⟨723001357732340107445741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482000905154893404963827 723001357732340107445741)
      ·
        refine ⟨271125509149627540292153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 723001357732340107445741 271125509149627540292153)
        ·
          refine ⟨203344131862220655219115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271125509149627540292153 203344131862220655219115)
          ·
            refine ⟨305016197793330982828673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203344131862220655219115 305016197793330982828673)
            ·
              refine ⟨228762148344998237121505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305016197793330982828673 228762148344998237121505)
              ·
                refine ⟨171571611258748677841129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228762148344998237121505 171571611258748677841129)
                ·
                  refine ⟨128678708444061508380847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171571611258748677841129 128678708444061508380847)
                  ·
                    rfl

theorem cell20_281926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_281926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281926 prefixEnd_281926 := by exact prefixLift 281926
  have htrace : WordTrace (prefixWord ++ tailWord_281926) baseStart_281926 baseEnd_281926 := by
    simpa [prefixWord, tailWord_281926, baseEnd_281926] using wordTrace_append hprefix tailTrace_281926
  have hstable : (prefixWord ++ tailWord_281926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281926).length < 2 ^ (prefixWord ++ tailWord_281926).sum := by decide
  have hdescent : baseEnd_281926 < baseStart_281926 := by decide
  rcases family_descends (prefixWord ++ tailWord_281926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281935 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_281935 : Nat := 118140960795 + 281935 * 2 ^ 59
def prefixEnd_281935 : Nat := 4983230072969 + 3 ^ 40 * 281935 * 2
def baseEnd_281935 : Nat := 128682816289297477080809

theorem tailTrace_281935 : CollatzResearch.WordTrace tailWord_281935 prefixEnd_281935 128682816289297477080809 := by
  unfold tailWord_281935
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283014233605120509639259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6855342822403413673092839 10283014233605120509639259)
  ·
    refine ⟨15424521350407680764458889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10283014233605120509639259 15424521350407680764458889)
    ·
      refine ⟨11568391012805760573344167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15424521350407680764458889 11568391012805760573344167)
      ·
        refine ⟨17352586519208640860016251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11568391012805760573344167 17352586519208640860016251)
        ·
          refine ⟨26028879778812961290024377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352586519208640860016251 26028879778812961290024377)
          ·
            refine ⟨19521659834109720967518283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26028879778812961290024377 19521659834109720967518283)
            ·
              refine ⟨29282489751164581451277425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19521659834109720967518283 29282489751164581451277425)
              ·
                refine ⟨21961867313373436088458069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29282489751164581451277425 21961867313373436088458069)
                ·
                  refine ⟨128682816289297477080809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21961867313373436088458069 128682816289297477080809)
                  ·
                    rfl

theorem cell20_281935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_281935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281935 prefixEnd_281935 := by exact prefixLift 281935
  have htrace : WordTrace (prefixWord ++ tailWord_281935) baseStart_281935 baseEnd_281935 := by
    simpa [prefixWord, tailWord_281935, baseEnd_281935] using wordTrace_append hprefix tailTrace_281935
  have hstable : (prefixWord ++ tailWord_281935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281935).length < 2 ^ (prefixWord ++ tailWord_281935).sum := by decide
  have hdescent : baseEnd_281935 < baseStart_281935 := by decide
  rcases family_descends (prefixWord ++ tailWord_281935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281982 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_281982 : Nat := 118140960795 + 281982 * 2 ^ 59
def prefixEnd_281982 : Nat := 4983230072969 + 3 ^ 40 * 281982 * 2
def baseEnd_281982 : Nat := 128704268369974202513951

theorem tailTrace_281982 : CollatzResearch.WordTrace tailWord_281982 prefixEnd_281982 128704268369974202513951 := by
  unfold tailWord_281982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285591058054355942075025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6856485642956565024400133 1285591058054355942075025)
  ·
    refine ⟨964193293540766956556269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1285591058054355942075025 964193293540766956556269)
    ·
      refine ⟨361572485077787608708601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 964193293540766956556269 361572485077787608708601)
      ·
        refine ⟨271179363808340706531451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361572485077787608708601 271179363808340706531451)
        ·
          refine ⟨406769045712511059797177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271179363808340706531451 406769045712511059797177)
          ·
            refine ⟨305076784284383294847883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406769045712511059797177 305076784284383294847883)
            ·
              refine ⟨457615176426574942271825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305076784284383294847883 457615176426574942271825)
              ·
                refine ⟨343211382319931206703869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457615176426574942271825 343211382319931206703869)
                ·
                  refine ⟨128704268369974202513951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343211382319931206703869 128704268369974202513951)
                  ·
                    rfl

theorem cell20_281982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_281982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281982 prefixEnd_281982 := by exact prefixLift 281982
  have htrace : WordTrace (prefixWord ++ tailWord_281982) baseStart_281982 baseEnd_281982 := by
    simpa [prefixWord, tailWord_281982, baseEnd_281982] using wordTrace_append hprefix tailTrace_281982
  have hstable : (prefixWord ++ tailWord_281982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281982).length < 2 ^ (prefixWord ++ tailWord_281982).sum := by decide
  have hdescent : baseEnd_281982 < baseStart_281982 := by decide
  rcases family_descends (prefixWord ++ tailWord_281982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_281986 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_281986 : Nat := 118140960795 + 281986 * 2 ^ 59
def prefixEnd_281986 : Nat := 4983230072969 + 3 ^ 40 * 281986 * 2
def baseEnd_281986 : Nat := 128706094078967966380601

theorem tailTrace_281986 : CollatzResearch.WordTrace tailWord_281986 prefixEnd_281986 128706094078967966380601 := by
  unfold tailWord_281986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2571218589105089054936453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6856582904280237479830541 2571218589105089054936453)
  ·
    refine ⟨482103485457204197800585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2571218589105089054936453 482103485457204197800585)
    ·
      refine ⟨361577614092903148350439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 482103485457204197800585 361577614092903148350439)
      ·
        refine ⟨542366421139354722525659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361577614092903148350439 542366421139354722525659)
        ·
          refine ⟨813549631709032083788489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542366421139354722525659 813549631709032083788489)
          ·
            refine ⟨610162223781774062841367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 813549631709032083788489 610162223781774062841367)
            ·
              refine ⟨915243335672661094262051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610162223781774062841367 915243335672661094262051)
              ·
                refine ⟨1372865003508991641393077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915243335672661094262051 1372865003508991641393077)
                ·
                  refine ⟨128706094078967966380601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1372865003508991641393077 128706094078967966380601)
                  ·
                    rfl

theorem cell20_281986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_281986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_281986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_281986 prefixEnd_281986 := by exact prefixLift 281986
  have htrace : WordTrace (prefixWord ++ tailWord_281986) baseStart_281986 baseEnd_281986 := by
    simpa [prefixWord, tailWord_281986, baseEnd_281986] using wordTrace_append hprefix tailTrace_281986
  have hstable : (prefixWord ++ tailWord_281986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_281986).length < 2 ^ (prefixWord ++ tailWord_281986).sum := by decide
  have hdescent : baseEnd_281986 < baseStart_281986 := by decide
  rcases family_descends (prefixWord ++ tailWord_281986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282104 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_282104 : Nat := 118140960795 + 282104 * 2 ^ 59
def prefixEnd_282104 : Nat := 4983230072969 + 3 ^ 40 * 282104 * 2
def baseEnd_282104 : Nat := 128759952494284000446785

theorem tailTrace_282104 : CollatzResearch.WordTrace tailWord_282104 prefixEnd_282104 128759952494284000446785 := by
  unfold tailWord_282104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144589084996431186270683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6859452113328574915027577 5144589084996431186270683)
  ·
    refine ⟨7716883627494646779406025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5144589084996431186270683 7716883627494646779406025)
    ·
      refine ⟨5787662720620985084554519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7716883627494646779406025 5787662720620985084554519)
      ·
        refine ⟨8681494080931477626831779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5787662720620985084554519 8681494080931477626831779)
        ·
          refine ⟨13022241121397216440247669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8681494080931477626831779 13022241121397216440247669)
          ·
            refine ⟨1220835105130989041273219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13022241121397216440247669 1220835105130989041273219)
            ·
              refine ⟨1831252657696483561909829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220835105130989041273219 1831252657696483561909829)
              ·
                refine ⟨343359873318090667858093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1831252657696483561909829 343359873318090667858093)
                ·
                  refine ⟨128759952494284000446785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343359873318090667858093 128759952494284000446785)
                  ·
                    rfl

theorem cell20_282104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_282104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282104 prefixEnd_282104 := by exact prefixLift 282104
  have htrace : WordTrace (prefixWord ++ tailWord_282104) baseStart_282104 baseEnd_282104 := by
    simpa [prefixWord, tailWord_282104, baseEnd_282104] using wordTrace_append hprefix tailTrace_282104
  have hstable : (prefixWord ++ tailWord_282104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282104).length < 2 ^ (prefixWord ++ tailWord_282104).sum := by decide
  have hdescent : baseEnd_282104 < baseStart_282104 := by decide
  rcases family_descends (prefixWord ++ tailWord_282104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282110 : List Nat := [4, 2, 2, 3, 2, 1, 1, 5]
def baseStart_282110 : Nat := 118140960795 + 282110 * 2 ^ 59
def prefixEnd_282110 : Nat := 4983230072969 + 3 ^ 40 * 282110 * 2
def baseEnd_282110 : Nat := 42920897019258215415587

theorem tailTrace_282110 : CollatzResearch.WordTrace tailWord_282110 prefixEnd_282110 42920897019258215415587 := by
  unfold tailWord_282110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286174625996390674657473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6859598005314083598173189 1286174625996390674657473)
  ·
    refine ⟨964630969497293005993105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1286174625996390674657473 964630969497293005993105)
    ·
      refine ⟨723473227122969754494829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 964630969497293005993105 723473227122969754494829)
      ·
        refine ⟨271302460171113657935561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 723473227122969754494829 271302460171113657935561)
        ·
          refine ⟨203476845128335243451671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271302460171113657935561 203476845128335243451671)
          ·
            refine ⟨305215267692502865177507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203476845128335243451671 305215267692502865177507)
            ·
              refine ⟨457822901538754297766261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305215267692502865177507 457822901538754297766261)
              ·
                refine ⟨42920897019258215415587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457822901538754297766261 42920897019258215415587)
                ·
                  rfl

theorem cell20_282110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_282110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282110 prefixEnd_282110 := by exact prefixLift 282110
  have htrace : WordTrace (prefixWord ++ tailWord_282110) baseStart_282110 baseEnd_282110 := by
    simpa [prefixWord, tailWord_282110, baseEnd_282110] using wordTrace_append hprefix tailTrace_282110
  have hstable : (prefixWord ++ tailWord_282110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282110).length < 2 ^ (prefixWord ++ tailWord_282110).sum := by decide
  have hdescent : baseEnd_282110 < baseStart_282110 := by decide
  rcases family_descends (prefixWord ++ tailWord_282110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282114 : List Nat := [3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_282114 : Nat := 118140960795 + 282114 * 2 ^ 59
def prefixEnd_282114 : Nat := 4983230072969 + 3 ^ 40 * 282114 * 2
def baseEnd_282114 : Nat := 42921505588922803371137

theorem tailTrace_282114 : CollatzResearch.WordTrace tailWord_282114 prefixEnd_282114 42921505588922803371137 := by
  unfold tailWord_282114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572385724989158520101349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6859695266637756053603597 2572385724989158520101349)
  ·
    refine ⟨482322323435467222519003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2572385724989158520101349 482322323435467222519003)
    ·
      refine ⟨723483485153200833778505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482322323435467222519003 723483485153200833778505)
      ·
        refine ⟨542612613864900625333879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 723483485153200833778505 542612613864900625333879)
        ·
          refine ⟨813918920797350938000819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542612613864900625333879 813918920797350938000819)
          ·
            refine ⟨1220878381196026407001229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813918920797350938000819 1220878381196026407001229)
            ·
              refine ⟨457829392948509902625461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220878381196026407001229 457829392948509902625461)
              ·
                refine ⟨42921505588922803371137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 457829392948509902625461 42921505588922803371137)
                ·
                  rfl

theorem cell20_282114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_282114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282114 prefixEnd_282114 := by exact prefixLift 282114
  have htrace : WordTrace (prefixWord ++ tailWord_282114) baseStart_282114 baseEnd_282114 := by
    simpa [prefixWord, tailWord_282114, baseEnd_282114] using wordTrace_append hprefix tailTrace_282114
  have hstable : (prefixWord ++ tailWord_282114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282114).length < 2 ^ (prefixWord ++ tailWord_282114).sum := by decide
  have hdescent : baseEnd_282114 < baseStart_282114 := by decide
  rcases family_descends (prefixWord ++ tailWord_282114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282145 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 2]
def baseStart_282145 : Nat := 118140960795 + 282145 * 2 ^ 59
def prefixEnd_282145 : Nat := 4983230072969 + 3 ^ 40 * 282145 * 2
def baseEnd_282145 : Nat := 128778666011470080079951

theorem tailTrace_282145 : CollatzResearch.WordTrace tailWord_282145 prefixEnd_282145 128778666011470080079951 := by
  unfold tailWord_282145
  simp only [CollatzResearch.WordTrace]
  refine ⟨10290673562844326374783889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6860449041896217583189259 10290673562844326374783889)
  ·
    refine ⟨7718005172133244781087917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10290673562844326374783889 7718005172133244781087917)
    ·
      refine ⟨2894251939549966792907969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7718005172133244781087917 2894251939549966792907969)
      ·
        refine ⟨2170688954662475094680977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2894251939549966792907969 2170688954662475094680977)
        ·
          refine ⟨1628016715996856321010733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2170688954662475094680977 1628016715996856321010733)
          ·
            refine ⟨610506268498821120379025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1628016715996856321010733 610506268498821120379025)
            ·
              refine ⟨457879701374115840284269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610506268498821120379025 457879701374115840284269)
              ·
                refine ⟨171704888015293440106601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457879701374115840284269 171704888015293440106601)
                ·
                  refine ⟨128778666011470080079951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171704888015293440106601 128778666011470080079951)
                  ·
                    rfl

theorem cell20_282145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_282145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282145 prefixEnd_282145 := by exact prefixLift 282145
  have htrace : WordTrace (prefixWord ++ tailWord_282145) baseStart_282145 baseEnd_282145 := by
    simpa [prefixWord, tailWord_282145, baseEnd_282145] using wordTrace_append hprefix tailTrace_282145
  have hstable : (prefixWord ++ tailWord_282145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282145).length < 2 ^ (prefixWord ++ tailWord_282145).sum := by decide
  have hdescent : baseEnd_282145 < baseStart_282145 := by decide
  rcases family_descends (prefixWord ++ tailWord_282145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282218 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_282218 : Nat := 118140960795 + 282218 * 2 ^ 59
def prefixEnd_282218 : Nat := 4983230072969 + 3 ^ 40 * 282218 * 2
def baseEnd_282218 : Nat := 128811985200606270646319

theorem tailTrace_282218 : CollatzResearch.WordTrace tailWord_282218 prefixEnd_282218 128811985200606270646319 := by
  unfold tailWord_282218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2573334022894964960547827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6862224061053239894794205 2573334022894964960547827)
  ·
    refine ⟨3860001034342447440821741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2573334022894964960547827 3860001034342447440821741)
    ·
      refine ⟨1447500387878417790308153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3860001034342447440821741 1447500387878417790308153)
      ·
        refine ⟨1085625290908813342731115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447500387878417790308153 1085625290908813342731115)
        ·
          refine ⟨1628437936363220014096673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085625290908813342731115 1628437936363220014096673)
          ·
            refine ⟨1221328452272415010572505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628437936363220014096673 1221328452272415010572505)
            ·
              refine ⟨915996339204311257929379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1221328452272415010572505 915996339204311257929379)
              ·
                refine ⟨1373994508806466886894069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915996339204311257929379 1373994508806466886894069)
                ·
                  refine ⟨128811985200606270646319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1373994508806466886894069 128811985200606270646319)
                  ·
                    rfl

theorem cell20_282218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_282218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282218 prefixEnd_282218 := by exact prefixLift 282218
  have htrace : WordTrace (prefixWord ++ tailWord_282218) baseStart_282218 baseEnd_282218 := by
    simpa [prefixWord, tailWord_282218, baseEnd_282218] using wordTrace_append hprefix tailTrace_282218
  have hstable : (prefixWord ++ tailWord_282218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282218).length < 2 ^ (prefixWord ++ tailWord_282218).sum := by decide
  have hdescent : baseEnd_282218 < baseStart_282218 := by decide
  rcases family_descends (prefixWord ++ tailWord_282218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282221 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 4]
def baseStart_282221 : Nat := 118140960795 + 282221 * 2 ^ 59
def prefixEnd_282221 : Nat := 4983230072969 + 3 ^ 40 * 282221 * 2
def baseEnd_282221 : Nat := 128813354482351593546307

theorem tailTrace_282221 : CollatzResearch.WordTrace tailWord_282221 prefixEnd_282221 128813354482351593546307 := by
  unfold tailWord_282221
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293445510568991354550517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6862297007045994236367011 10293445510568991354550517)
  ·
    refine ⟨965010516615842939489111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10293445510568991354550517 965010516615842939489111)
    ·
      refine ⟨1447515774923764409233667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965010516615842939489111 1447515774923764409233667)
      ·
        refine ⟨2171273662385646613850501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447515774923764409233667 2171273662385646613850501)
        ·
          refine ⟨407113811697308740096969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2171273662385646613850501 407113811697308740096969)
          ·
            refine ⟨305335358772981555072727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407113811697308740096969 305335358772981555072727)
            ·
              refine ⟨458003038159472332609091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305335358772981555072727 458003038159472332609091)
              ·
                refine ⟨687004557239208498913637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458003038159472332609091 687004557239208498913637)
                ·
                  refine ⟨128813354482351593546307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687004557239208498913637 128813354482351593546307)
                  ·
                    rfl

theorem cell20_282221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_282221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282221 prefixEnd_282221 := by exact prefixLift 282221
  have htrace : WordTrace (prefixWord ++ tailWord_282221) baseStart_282221 baseEnd_282221 := by
    simpa [prefixWord, tailWord_282221, baseEnd_282221] using wordTrace_append hprefix tailTrace_282221
  have hstable : (prefixWord ++ tailWord_282221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282221).length < 2 ^ (prefixWord ++ tailWord_282221).sum := by decide
  have hdescent : baseEnd_282221 < baseStart_282221 := by decide
  rcases family_descends (prefixWord ++ tailWord_282221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282273 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_282273 : Nat := 118140960795 + 282273 * 2 ^ 59
def prefixEnd_282273 : Nat := 4983230072969 + 3 ^ 40 * 282273 * 2
def baseEnd_282273 : Nat := 128837088699270523812761

theorem tailTrace_282273 : CollatzResearch.WordTrace tailWord_282273 prefixEnd_282273 128837088699270523812761 := by
  unfold tailWord_282273
  simp only [CollatzResearch.WordTrace]
  refine ⟨10295342106380604235443473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6863561404253736156962315 10295342106380604235443473)
  ·
    refine ⟨7721506579785453176582605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10295342106380604235443473 7721506579785453176582605)
    ·
      refine ⟨2895564967419544941218477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7721506579785453176582605 2895564967419544941218477)
      ·
        refine ⟨1085836862782329352956929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2895564967419544941218477 1085836862782329352956929)
        ·
          refine ⟨814377647086747014717697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085836862782329352956929 814377647086747014717697)
          ·
            refine ⟨610783235315060261038273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814377647086747014717697 610783235315060261038273)
            ·
              refine ⟨458087426486295195778705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610783235315060261038273 458087426486295195778705)
              ·
                refine ⟨343565569864721396834029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458087426486295195778705 343565569864721396834029)
                ·
                  refine ⟨128837088699270523812761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343565569864721396834029 128837088699270523812761)
                  ·
                    rfl

theorem cell20_282273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_282273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282273 prefixEnd_282273 := by exact prefixLift 282273
  have htrace : WordTrace (prefixWord ++ tailWord_282273) baseStart_282273 baseEnd_282273 := by
    simpa [prefixWord, tailWord_282273, baseEnd_282273] using wordTrace_append hprefix tailTrace_282273
  have hstable : (prefixWord ++ tailWord_282273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282273).length < 2 ^ (prefixWord ++ tailWord_282273).sum := by decide
  have hdescent : baseEnd_282273 < baseStart_282273 := by decide
  rcases family_descends (prefixWord ++ tailWord_282273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282276 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 2]
def baseStart_282276 : Nat := 118140960795 + 282276 * 2 ^ 59
def prefixEnd_282276 : Nat := 4983230072969 + 3 ^ 40 * 282276 * 2
def baseEnd_282276 : Nat := 128838457981015846712749

theorem tailTrace_282276 : CollatzResearch.WordTrace tailWord_282276 prefixEnd_282276 128838457981015846712749 := by
  unfold tailWord_282276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147725762684867873901341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6863634350246490498535121 5147725762684867873901341)
  ·
    refine ⟨1930397161006825452713003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5147725762684867873901341 1930397161006825452713003)
    ·
      refine ⟨2895595741510238179069505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1930397161006825452713003 2895595741510238179069505)
      ·
        refine ⟨2171696806132678634302129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2895595741510238179069505 2171696806132678634302129)
        ·
          refine ⟨1628772604599508975726597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2171696806132678634302129 1628772604599508975726597)
          ·
            refine ⟨305394863362407932948737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1628772604599508975726597 305394863362407932948737)
            ·
              refine ⟨229046147521805949711553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305394863362407932948737 229046147521805949711553)
              ·
                refine ⟨171784610641354462283665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229046147521805949711553 171784610641354462283665)
                ·
                  refine ⟨128838457981015846712749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171784610641354462283665 128838457981015846712749)
                  ·
                    rfl

theorem cell20_282276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_282276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282276 prefixEnd_282276 := by exact prefixLift 282276
  have htrace : WordTrace (prefixWord ++ tailWord_282276) baseStart_282276 baseEnd_282276 := by
    simpa [prefixWord, tailWord_282276, baseEnd_282276] using wordTrace_append hprefix tailTrace_282276
  have hstable : (prefixWord ++ tailWord_282276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282276).length < 2 ^ (prefixWord ++ tailWord_282276).sum := by decide
  have hdescent : baseEnd_282276 < baseStart_282276 := by decide
  rcases family_descends (prefixWord ++ tailWord_282276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282277 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_282277 : Nat := 118140960795 + 282277 * 2 ^ 59
def prefixEnd_282277 : Nat := 4983230072969 + 3 ^ 40 * 282277 * 2
def baseEnd_282277 : Nat := 128838914408264287679411

theorem tailTrace_282277 : CollatzResearch.WordTrace tailWord_282277 prefixEnd_282277 128838914408264287679411 := by
  unfold tailWord_282277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10295487998366112918589085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6863658665577408612392723 10295487998366112918589085)
  ·
    refine ⟨3860807999387292344470907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10295487998366112918589085 3860807999387292344470907)
    ·
      refine ⟨5791211999080938516706361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3860807999387292344470907 5791211999080938516706361)
      ·
        refine ⟨4343408999310703887529771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5791211999080938516706361 4343408999310703887529771)
        ·
          refine ⟨6515113498966055831294657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343408999310703887529771 6515113498966055831294657)
          ·
            refine ⟨4886335124224541873470993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6515113498966055831294657 4886335124224541873470993)
            ·
              refine ⟨3664751343168406405103245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4886335124224541873470993 3664751343168406405103245)
              ·
                refine ⟨1374281753688152401913717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3664751343168406405103245 1374281753688152401913717)
                ·
                  refine ⟨128838914408264287679411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1374281753688152401913717 128838914408264287679411)
                  ·
                    rfl

theorem cell20_282277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_282277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282277 prefixEnd_282277 := by exact prefixLift 282277
  have htrace : WordTrace (prefixWord ++ tailWord_282277) baseStart_282277 baseEnd_282277 := by
    simpa [prefixWord, tailWord_282277, baseEnd_282277] using wordTrace_append hprefix tailTrace_282277
  have hstable : (prefixWord ++ tailWord_282277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282277).length < 2 ^ (prefixWord ++ tailWord_282277).sum := by decide
  have hdescent : baseEnd_282277 < baseStart_282277 := by decide
  rcases family_descends (prefixWord ++ tailWord_282277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282284 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_282284 : Nat := 118140960795 + 282284 * 2 ^ 59
def prefixEnd_282284 : Nat := 4983230072969 + 3 ^ 40 * 282284 * 2
def baseEnd_282284 : Nat := 128842109399003374446049

theorem tailTrace_282284 : CollatzResearch.WordTrace tailWord_282284 prefixEnd_282284 128842109399003374446049 := by
  unfold tailWord_282284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147871654670376557046953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6863828872893835409395937 5147871654670376557046953)
  ·
    refine ⟨3860903741002782417785215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5147871654670376557046953 3860903741002782417785215)
    ·
      refine ⟨5791355611504173626677823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3860903741002782417785215 5791355611504173626677823)
      ·
        refine ⟨8687033417256260440016735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791355611504173626677823 8687033417256260440016735)
        ·
          refine ⟨13030550125884390660025103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8687033417256260440016735 13030550125884390660025103)
          ·
            refine ⟨19545825188826585990037655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13030550125884390660025103 19545825188826585990037655)
            ·
              refine ⟨29318737783239878985056483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19545825188826585990037655 29318737783239878985056483)
              ·
                refine ⟨43978106674859818477584725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29318737783239878985056483 43978106674859818477584725)
                ·
                  refine ⟨128842109399003374446049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43978106674859818477584725 128842109399003374446049)
                  ·
                    rfl

theorem cell20_282284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_282284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282284 prefixEnd_282284 := by exact prefixLift 282284
  have htrace : WordTrace (prefixWord ++ tailWord_282284) baseStart_282284 baseEnd_282284 := by
    simpa [prefixWord, tailWord_282284, baseEnd_282284] using wordTrace_append hprefix tailTrace_282284
  have hstable : (prefixWord ++ tailWord_282284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282284).length < 2 ^ (prefixWord ++ tailWord_282284).sum := by decide
  have hdescent : baseEnd_282284 < baseStart_282284 := by decide
  rcases family_descends (prefixWord ++ tailWord_282284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282301 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_282301 : Nat := 118140960795 + 282301 * 2 ^ 59
def prefixEnd_282301 : Nat := 4983230072969 + 3 ^ 40 * 282301 * 2
def baseEnd_282301 : Nat := 128849868662226870879313

theorem tailTrace_282301 : CollatzResearch.WordTrace tailWord_282301 prefixEnd_282301 128849868662226870879313 := by
  unfold tailWord_282301
  simp only [CollatzResearch.WordTrace]
  refine ⟨10296363350279165017462757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6864242233519443344975171 10296363350279165017462757)
  ·
    refine ⟨1930568128177343440774267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10296363350279165017462757 1930568128177343440774267)
    ·
      refine ⟨2895852192266015161161401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1930568128177343440774267 2895852192266015161161401)
      ·
        refine ⟨2171889144199511370871051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2895852192266015161161401 2171889144199511370871051)
        ·
          refine ⟨3257833716299267056306577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171889144199511370871051 3257833716299267056306577)
          ·
            refine ⟨2443375287224450292229933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3257833716299267056306577 2443375287224450292229933)
            ·
              refine ⟨916265732709168859586225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2443375287224450292229933 916265732709168859586225)
              ·
                refine ⟨687199299531876644689669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916265732709168859586225 687199299531876644689669)
                ·
                  refine ⟨128849868662226870879313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687199299531876644689669 128849868662226870879313)
                  ·
                    rfl

theorem cell20_282301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_282301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282301 prefixEnd_282301 := by exact prefixLift 282301
  have htrace : WordTrace (prefixWord ++ tailWord_282301) baseStart_282301 baseEnd_282301 := by
    simpa [prefixWord, tailWord_282301, baseEnd_282301] using wordTrace_append hprefix tailTrace_282301
  have hstable : (prefixWord ++ tailWord_282301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282301).length < 2 ^ (prefixWord ++ tailWord_282301).sum := by decide
  have hdescent : baseEnd_282301 < baseStart_282301 := by decide
  rcases family_descends (prefixWord ++ tailWord_282301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282360 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_282360 : Nat := 118140960795 + 282360 * 2 ^ 59
def prefixEnd_282360 : Nat := 4983230072969 + 3 ^ 40 * 282360 * 2
def baseEnd_282360 : Nat := 128876797869884887912405

theorem tailTrace_282360 : CollatzResearch.WordTrace tailWord_282360 prefixEnd_282360 128876797869884887912405 := by
  unfold tailWord_282360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149257628532709046930267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6865676838043612062573689 5149257628532709046930267)
  ·
    refine ⟨7723886442799063570395401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5149257628532709046930267 7723886442799063570395401)
    ·
      refine ⟨5792914832099297677796551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7723886442799063570395401 5792914832099297677796551)
      ·
        refine ⟨8689372248148946516694827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5792914832099297677796551 8689372248148946516694827)
        ·
          refine ⟨13034058372223419775042241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8689372248148946516694827 13034058372223419775042241)
          ·
            refine ⟨9775543779167564831281681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13034058372223419775042241 9775543779167564831281681)
            ·
              refine ⟨7331657834375673623461261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9775543779167564831281681 7331657834375673623461261)
              ·
                refine ⟨2749371687890877608797973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7331657834375673623461261 2749371687890877608797973)
                ·
                  refine ⟨128876797869884887912405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2749371687890877608797973 128876797869884887912405)
                  ·
                    rfl

theorem cell20_282360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_282360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282360 prefixEnd_282360 := by exact prefixLift 282360
  have htrace : WordTrace (prefixWord ++ tailWord_282360) baseStart_282360 baseEnd_282360 := by
    simpa [prefixWord, tailWord_282360, baseEnd_282360] using wordTrace_append hprefix tailTrace_282360
  have hstable : (prefixWord ++ tailWord_282360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282360).length < 2 ^ (prefixWord ++ tailWord_282360).sum := by decide
  have hdescent : baseEnd_282360 < baseStart_282360 := by decide
  rcases family_descends (prefixWord ++ tailWord_282360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282370 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_282370 : Nat := 118140960795 + 282370 * 2 ^ 59
def prefixEnd_282370 : Nat := 4983230072969 + 3 ^ 40 * 282370 * 2
def baseEnd_282370 : Nat := 128881362142369297579031

theorem tailTrace_282370 : CollatzResearch.WordTrace tailWord_282370 prefixEnd_282370 128881362142369297579031 := by
  unfold tailWord_282370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574719996757297450431141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6865919991352793201149709 2574719996757297450431141)
  ·
    refine ⟨482759999391993271955839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2574719996757297450431141 482759999391993271955839)
    ·
      refine ⟨724139999087989907933759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482759999391993271955839 724139999087989907933759)
      ·
        refine ⟨1086209998631984861900639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724139999087989907933759 1086209998631984861900639)
        ·
          refine ⟨1629314997947977292850959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086209998631984861900639 1629314997947977292850959)
          ·
            refine ⟨2443972496921965939276439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629314997947977292850959 2443972496921965939276439)
            ·
              refine ⟨3665958745382948908914659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443972496921965939276439 3665958745382948908914659)
              ·
                refine ⟨5498938118074423363371989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3665958745382948908914659 5498938118074423363371989)
                ·
                  refine ⟨128881362142369297579031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5498938118074423363371989 128881362142369297579031)
                  ·
                    rfl

theorem cell20_282370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_282370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282370 prefixEnd_282370 := by exact prefixLift 282370
  have htrace : WordTrace (prefixWord ++ tailWord_282370) baseStart_282370 baseEnd_282370 := by
    simpa [prefixWord, tailWord_282370, baseEnd_282370] using wordTrace_append hprefix tailTrace_282370
  have hstable : (prefixWord ++ tailWord_282370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282370).length < 2 ^ (prefixWord ++ tailWord_282370).sum := by decide
  have hdescent : baseEnd_282370 < baseStart_282370 := by decide
  rcases family_descends (prefixWord ++ tailWord_282370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282394 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_282394 : Nat := 118140960795 + 282394 * 2 ^ 59
def prefixEnd_282394 : Nat := 4983230072969 + 3 ^ 40 * 282394 * 2
def baseEnd_282394 : Nat := 128892316396331880778933

theorem tailTrace_282394 : CollatzResearch.WordTrace tailWord_282394 prefixEnd_282394 128892316396331880778933 := by
  unfold tailWord_282394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574938834735560475149559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6866503559294827933732157 2574938834735560475149559)
  ·
    refine ⟨3862408252103340712724339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2574938834735560475149559 3862408252103340712724339)
    ·
      refine ⟨5793612378155011069086509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3862408252103340712724339 5793612378155011069086509)
      ·
        refine ⟨2172604641808129150907441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5793612378155011069086509 2172604641808129150907441)
        ·
          refine ⟨1629453481356096863180581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2172604641808129150907441 1629453481356096863180581)
          ·
            refine ⟨305522527754268161846359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1629453481356096863180581 305522527754268161846359)
            ·
              refine ⟨458283791631402242769539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305522527754268161846359 458283791631402242769539)
              ·
                refine ⟨687425687447103364154309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458283791631402242769539 687425687447103364154309)
                ·
                  refine ⟨128892316396331880778933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687425687447103364154309 128892316396331880778933)
                  ·
                    rfl

theorem cell20_282394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_282394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282394 prefixEnd_282394 := by exact prefixLift 282394
  have htrace : WordTrace (prefixWord ++ tailWord_282394) baseStart_282394 baseEnd_282394 := by
    simpa [prefixWord, tailWord_282394, baseEnd_282394] using wordTrace_append hprefix tailTrace_282394
  have hstable : (prefixWord ++ tailWord_282394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282394).length < 2 ^ (prefixWord ++ tailWord_282394).sum := by decide
  have hdescent : baseEnd_282394 < baseStart_282394 := by decide
  rcases family_descends (prefixWord ++ tailWord_282394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282404 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_282404 : Nat := 118140960795 + 282404 * 2 ^ 59
def prefixEnd_282404 : Nat := 4983230072969 + 3 ^ 40 * 282404 * 2
def baseEnd_282404 : Nat := 128896880668816290445559

theorem tailTrace_282404 : CollatzResearch.WordTrace tailWord_282404 prefixEnd_282404 128896880668816290445559 := by
  unfold tailWord_282404
  simp only [CollatzResearch.WordTrace]
  refine ⟨5150060034453006804231133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6866746712604009072308177 5150060034453006804231133)
  ·
    refine ⟨1931272512919877551586675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5150060034453006804231133 1931272512919877551586675)
    ·
      refine ⟨2896908769379816327380013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931272512919877551586675 2896908769379816327380013)
      ·
        refine ⟨1086340788517431122767505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2896908769379816327380013 1086340788517431122767505)
        ·
          refine ⟨814755591388073342075629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086340788517431122767505 814755591388073342075629)
          ·
            refine ⟨305533346770527503278361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 814755591388073342075629 305533346770527503278361)
            ·
              refine ⟨229150010077895627458771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305533346770527503278361 229150010077895627458771)
              ·
                refine ⟨343725015116843441188157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229150010077895627458771 343725015116843441188157)
                ·
                  refine ⟨128896880668816290445559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343725015116843441188157 128896880668816290445559)
                  ·
                    rfl

theorem cell20_282404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_282404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282404 prefixEnd_282404 := by exact prefixLift 282404
  have htrace : WordTrace (prefixWord ++ tailWord_282404) baseStart_282404 baseEnd_282404 := by
    simpa [prefixWord, tailWord_282404, baseEnd_282404] using wordTrace_append hprefix tailTrace_282404
  have hstable : (prefixWord ++ tailWord_282404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282404).length < 2 ^ (prefixWord ++ tailWord_282404).sum := by decide
  have hdescent : baseEnd_282404 < baseStart_282404 := by decide
  rcases family_descends (prefixWord ++ tailWord_282404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282445 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 2]
def baseStart_282445 : Nat := 118140960795 + 282445 * 2 ^ 59
def prefixEnd_282445 : Nat := 4983230072969 + 3 ^ 40 * 282445 * 2
def baseEnd_282445 : Nat := 128915594186002370078725

theorem tailTrace_282445 : CollatzResearch.WordTrace tailWord_282445 prefixEnd_282445 128915594186002370078725 := by
  unfold tailWord_282445
  simp only [CollatzResearch.WordTrace]
  refine ⟨10301615461757477610704789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6867743641171651740469859 10301615461757477610704789)
  ·
    refine ⟨482888224769881763001787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10301615461757477610704789 482888224769881763001787)
    ·
      refine ⟨724332337154822644502681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482888224769881763001787 724332337154822644502681)
      ·
        refine ⟨543249252866116983377011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724332337154822644502681 543249252866116983377011)
        ·
          refine ⟨814873879299175475065517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543249252866116983377011 814873879299175475065517)
          ·
            refine ⟨305577704737190803149569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 814873879299175475065517 305577704737190803149569)
            ·
              refine ⟨229183278552893102362177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305577704737190803149569 229183278552893102362177)
              ·
                refine ⟨171887458914669826771633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229183278552893102362177 171887458914669826771633)
                ·
                  refine ⟨128915594186002370078725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171887458914669826771633 128915594186002370078725)
                  ·
                    rfl

theorem cell20_282445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_282445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282445 prefixEnd_282445 := by exact prefixLift 282445
  have htrace : WordTrace (prefixWord ++ tailWord_282445) baseStart_282445 baseEnd_282445 := by
    simpa [prefixWord, tailWord_282445, baseEnd_282445] using wordTrace_append hprefix tailTrace_282445
  have hstable : (prefixWord ++ tailWord_282445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282445).length < 2 ^ (prefixWord ++ tailWord_282445).sum := by decide
  have hdescent : baseEnd_282445 < baseStart_282445 := by decide
  rcases family_descends (prefixWord ++ tailWord_282445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282449 : List Nat := [1, 2, 2, 1, 5, 1, 4, 2, 2]
def baseStart_282449 : Nat := 118140960795 + 282449 * 2 ^ 59
def prefixEnd_282449 : Nat := 4983230072969 + 3 ^ 40 * 282449 * 2
def baseEnd_282449 : Nat := 128917419894996133945375

theorem tailTrace_282449 : CollatzResearch.WordTrace tailWord_282449 prefixEnd_282449 128917419894996133945375 := by
  unfold tailWord_282449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10301761353742986293850401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6867840902495324195900267 10301761353742986293850401)
  ·
    refine ⟨7726321015307239720387801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10301761353742986293850401 7726321015307239720387801)
    ·
      refine ⟨5794740761480429790290851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7726321015307239720387801 5794740761480429790290851)
      ·
        refine ⟨8692111142220644685436277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5794740761480429790290851 8692111142220644685436277)
        ·
          refine ⟨814885419583185439259651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8692111142220644685436277 814885419583185439259651)
          ·
            refine ⟨1222328129374778158889477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814885419583185439259651 1222328129374778158889477)
            ·
              refine ⟨229186524257770904791777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1222328129374778158889477 229186524257770904791777)
              ·
                refine ⟨171889893193328178593833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229186524257770904791777 171889893193328178593833)
                ·
                  refine ⟨128917419894996133945375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171889893193328178593833 128917419894996133945375)
                  ·
                    rfl

theorem cell20_282449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_282449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282449 prefixEnd_282449 := by exact prefixLift 282449
  have htrace : WordTrace (prefixWord ++ tailWord_282449) baseStart_282449 baseEnd_282449 := by
    simpa [prefixWord, tailWord_282449, baseEnd_282449] using wordTrace_append hprefix tailTrace_282449
  have hstable : (prefixWord ++ tailWord_282449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282449).length < 2 ^ (prefixWord ++ tailWord_282449).sum := by decide
  have hdescent : baseEnd_282449 < baseStart_282449 := by decide
  rcases family_descends (prefixWord ++ tailWord_282449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282497 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 3]
def baseStart_282497 : Nat := 118140960795 + 282497 * 2 ^ 59
def prefixEnd_282497 : Nat := 4983230072969 + 3 ^ 40 * 282497 * 2
def baseEnd_282497 : Nat := 128939328402921300345179

theorem tailTrace_282497 : CollatzResearch.WordTrace tailWord_282497 prefixEnd_282497 128939328402921300345179 := by
  unfold tailWord_282497
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303512057569090491597745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6869008038379393661065163 10303512057569090491597745)
  ·
    refine ⟨7727634043176817868698309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10303512057569090491597745 7727634043176817868698309)
    ·
      refine ⟨1448931383095653350380933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7727634043176817868698309 1448931383095653350380933)
      ·
        refine ⟨271674634330435003196425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1448931383095653350380933 271674634330435003196425)
        ·
          refine ⟨203755975747826252397319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271674634330435003196425 203755975747826252397319)
          ·
            refine ⟨305633963621739378595979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203755975747826252397319 305633963621739378595979)
            ·
              refine ⟨458450945432609067893969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305633963621739378595979 458450945432609067893969)
              ·
                refine ⟨343838209074456800920477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458450945432609067893969 343838209074456800920477)
                ·
                  refine ⟨128939328402921300345179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343838209074456800920477 128939328402921300345179)
                  ·
                    rfl

theorem cell20_282497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_282497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282497 prefixEnd_282497 := by exact prefixLift 282497
  have htrace : WordTrace (prefixWord ++ tailWord_282497) baseStart_282497 baseEnd_282497 := by
    simpa [prefixWord, tailWord_282497, baseEnd_282497] using wordTrace_append hprefix tailTrace_282497
  have hstable : (prefixWord ++ tailWord_282497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282497).length < 2 ^ (prefixWord ++ tailWord_282497).sum := by decide
  have hdescent : baseEnd_282497 < baseStart_282497 := by decide
  rcases family_descends (prefixWord ++ tailWord_282497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282505 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_282505 : Nat := 118140960795 + 282505 * 2 ^ 59
def prefixEnd_282505 : Nat := 4983230072969 + 3 ^ 40 * 282505 * 2
def baseEnd_282505 : Nat := 128942979820908828078479

theorem tailTrace_282505 : CollatzResearch.WordTrace tailWord_282505 prefixEnd_282505 128942979820908828078479 := by
  unfold tailWord_282505
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303803841540107857888969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6869202561026738571925979 10303803841540107857888969)
  ·
    refine ⟨7727852881155080893416727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10303803841540107857888969 7727852881155080893416727)
    ·
      refine ⟨11591779321732621340125091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727852881155080893416727 11591779321732621340125091)
      ·
        refine ⟨17387668982598932010187637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11591779321732621340125091 17387668982598932010187637)
        ·
          refine ⟨1630093967118649875955091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17387668982598932010187637 1630093967118649875955091)
          ·
            refine ⟨2445140950677974813932637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630093967118649875955091 2445140950677974813932637)
            ·
              refine ⟨916927856504240555224739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2445140950677974813932637 916927856504240555224739)
              ·
                refine ⟨1375391784756360832837109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 916927856504240555224739 1375391784756360832837109)
                ·
                  refine ⟨128942979820908828078479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1375391784756360832837109 128942979820908828078479)
                  ·
                    rfl

theorem cell20_282505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_282505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282505 prefixEnd_282505 := by exact prefixLift 282505
  have htrace : WordTrace (prefixWord ++ tailWord_282505) baseStart_282505 baseEnd_282505 := by
    simpa [prefixWord, tailWord_282505, baseEnd_282505] using wordTrace_append hprefix tailTrace_282505
  have hstable : (prefixWord ++ tailWord_282505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282505).length < 2 ^ (prefixWord ++ tailWord_282505).sum := by decide
  have hdescent : baseEnd_282505 < baseStart_282505 := by decide
  rcases family_descends (prefixWord ++ tailWord_282505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282512 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_282512 : Nat := 118140960795 + 282512 * 2 ^ 59
def prefixEnd_282512 : Nat := 4983230072969 + 3 ^ 40 * 282512 * 2
def baseEnd_282512 : Nat := 128946174811647914845117

theorem tailTrace_282512 : CollatzResearch.WordTrace tailWord_282512 prefixEnd_282512 128946174811647914845117 := by
  unfold tailWord_282512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152029576257374026696895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6869372768343165368929193 5152029576257374026696895)
  ·
    refine ⟨7728044364386061040045343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152029576257374026696895 7728044364386061040045343)
    ·
      refine ⟨11592066546579091560068015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7728044364386061040045343 11592066546579091560068015)
      ·
        refine ⟨17388099819868637340102023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11592066546579091560068015 17388099819868637340102023)
        ·
          refine ⟨26082149729802956010153035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17388099819868637340102023 26082149729802956010153035)
          ·
            refine ⟨39123224594704434015229553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26082149729802956010153035 39123224594704434015229553)
            ·
              refine ⟨29342418446028325511422165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39123224594704434015229553 29342418446028325511422165)
              ·
                refine ⟨687712932328788879173957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29342418446028325511422165 687712932328788879173957)
                ·
                  refine ⟨128946174811647914845117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 687712932328788879173957 128946174811647914845117)
                  ·
                    rfl

theorem cell20_282512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_282512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282512 prefixEnd_282512 := by exact prefixLift 282512
  have htrace : WordTrace (prefixWord ++ tailWord_282512) baseStart_282512 baseEnd_282512 := by
    simpa [prefixWord, tailWord_282512, baseEnd_282512] using wordTrace_append hprefix tailTrace_282512
  have hstable : (prefixWord ++ tailWord_282512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282512).length < 2 ^ (prefixWord ++ tailWord_282512).sum := by decide
  have hdescent : baseEnd_282512 < baseStart_282512 := by decide
  rcases family_descends (prefixWord ++ tailWord_282512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282574 : List Nat := [4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_282574 : Nat := 118140960795 + 282574 * 2 ^ 59
def prefixEnd_282574 : Nat := 4983230072969 + 3 ^ 40 * 282574 * 2
def baseEnd_282574 : Nat := 42991491100350418259399

theorem tailTrace_282574 : CollatzResearch.WordTrace tailWord_282574 prefixEnd_282574 42991491100350418259399 := by
  unfold tailWord_282574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288290059786266580268847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6870880318860088428100517 1288290059786266580268847)
  ·
    refine ⟨1932435089679399870403271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1288290059786266580268847 1932435089679399870403271)
    ·
      refine ⟨2898652634519099805604907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932435089679399870403271 2898652634519099805604907)
      ·
        refine ⟨4347978951778649708407361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898652634519099805604907 4347978951778649708407361)
        ·
          refine ⟨3260984213833987281305521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4347978951778649708407361 3260984213833987281305521)
          ·
            refine ⟨2445738160375490460979141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3260984213833987281305521 2445738160375490460979141)
            ·
              refine ⟨458575905070404461433589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2445738160375490460979141 458575905070404461433589)
              ·
                refine ⟨42991491100350418259399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 458575905070404461433589 42991491100350418259399)
                ·
                  rfl

theorem cell20_282574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_282574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282574 prefixEnd_282574 := by exact prefixLift 282574
  have htrace : WordTrace (prefixWord ++ tailWord_282574) baseStart_282574 baseEnd_282574 := by
    simpa [prefixWord, tailWord_282574, baseEnd_282574] using wordTrace_append hprefix tailTrace_282574
  have hstable : (prefixWord ++ tailWord_282574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282574).length < 2 ^ (prefixWord ++ tailWord_282574).sum := by decide
  have hdescent : baseEnd_282574 < baseStart_282574 := by decide
  rcases family_descends (prefixWord ++ tailWord_282574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282619 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_282619 : Nat := 118140960795 + 282619 * 2 ^ 59
def prefixEnd_282619 : Nat := 4983230072969 + 3 ^ 40 * 282619 * 2
def baseEnd_282619 : Nat := 128995012527231098278013

theorem tailTrace_282619 : CollatzResearch.WordTrace tailWord_282619 prefixEnd_282619 128995012527231098278013 := by
  unfold tailWord_282619
  simp only [CollatzResearch.WordTrace]
  refine ⟨10307961763127105327538911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6871974508751403551692607 10307961763127105327538911)
  ·
    refine ⟨15461942644690657991308367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10307961763127105327538911 15461942644690657991308367)
    ·
      refine ⟨23192913967035986986962551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15461942644690657991308367 23192913967035986986962551)
      ·
        refine ⟨34789370950553980480443827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23192913967035986986962551 34789370950553980480443827)
        ·
          refine ⟨52184056425830970720665741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34789370950553980480443827 52184056425830970720665741)
          ·
            refine ⟨19569021159686614020249653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52184056425830970720665741 19569021159686614020249653)
            ·
              refine ⟨1834595733720620064398405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19569021159686614020249653 1834595733720620064398405)
              ·
                refine ⟨343986700072616262074701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1834595733720620064398405 343986700072616262074701)
                ·
                  refine ⟨128995012527231098278013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343986700072616262074701 128995012527231098278013)
                  ·
                    rfl

theorem cell20_282619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_282619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282619 prefixEnd_282619 := by exact prefixLift 282619
  have htrace : WordTrace (prefixWord ++ tailWord_282619) baseStart_282619 baseEnd_282619 := by
    simpa [prefixWord, tailWord_282619, baseEnd_282619] using wordTrace_append hprefix tailTrace_282619
  have hstable : (prefixWord ++ tailWord_282619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282619).length < 2 ^ (prefixWord ++ tailWord_282619).sum := by decide
  have hdescent : baseEnd_282619 < baseStart_282619 := by decide
  rcases family_descends (prefixWord ++ tailWord_282619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282674 : List Nat := [3, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_282674 : Nat := 118140960795 + 282674 * 2 ^ 59
def prefixEnd_282674 : Nat := 4983230072969 + 3 ^ 40 * 282674 * 2
def baseEnd_282674 : Nat := 129020116025895351444455

theorem tailTrace_282674 : CollatzResearch.WordTrace tailWord_282674 prefixEnd_282674 129020116025895351444455 := by
  unfold tailWord_282674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577491944481962430197769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6873311851951899813860717 2577491944481962430197769)
  ·
    refine ⟨1933118958361471822648327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2577491944481962430197769 1933118958361471822648327)
    ·
      refine ⟨2899678437542207733972491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933118958361471822648327 2899678437542207733972491)
      ·
        refine ⟨4349517656313311600958737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2899678437542207733972491 4349517656313311600958737)
        ·
          refine ⟨3262138242234983700719053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4349517656313311600958737 3262138242234983700719053)
          ·
            refine ⟨1223301840838118887769645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3262138242234983700719053 1223301840838118887769645)
            ·
              refine ⟨458738190314294582913617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1223301840838118887769645 458738190314294582913617)
              ·
                refine ⟨344053642735720937185213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458738190314294582913617 344053642735720937185213)
                ·
                  refine ⟨129020116025895351444455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344053642735720937185213 129020116025895351444455)
                  ·
                    rfl

theorem cell20_282674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_282674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282674 prefixEnd_282674 := by exact prefixLift 282674
  have htrace : WordTrace (prefixWord ++ tailWord_282674) baseStart_282674 baseEnd_282674 := by
    simpa [prefixWord, tailWord_282674, baseEnd_282674] using wordTrace_append hprefix tailTrace_282674
  have hstable : (prefixWord ++ tailWord_282674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282674).length < 2 ^ (prefixWord ++ tailWord_282674).sum := by decide
  have hdescent : baseEnd_282674 < baseStart_282674 := by decide
  rcases family_descends (prefixWord ++ tailWord_282674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282719 : List Nat := [1, 1, 2, 3, 1, 1, 2, 7, 2]
def baseStart_282719 : Nat := 118140960795 + 282719 * 2 ^ 59
def prefixEnd_282719 : Nat := 4983230072969 + 3 ^ 40 * 282719 * 2
def baseEnd_282719 : Nat := 129040655252075194944271

theorem tailTrace_282719 : CollatzResearch.WordTrace tailWord_282719 prefixEnd_282719 129040655252075194944271 := by
  unfold tailWord_282719
  simp only [CollatzResearch.WordTrace]
  refine ⟨10311609062764822406179211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6874406041843214937452807 10311609062764822406179211)
  ·
    refine ⟨15467413594147233609268817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10311609062764822406179211 15467413594147233609268817)
    ·
      refine ⟨11600560195610425206951613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15467413594147233609268817 11600560195610425206951613)
      ·
        refine ⟨4350210073353909452606855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11600560195610425206951613 4350210073353909452606855)
        ·
          refine ⟨6525315110030864178910283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4350210073353909452606855 6525315110030864178910283)
          ·
            refine ⟨9787972665046296268365425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6525315110030864178910283 9787972665046296268365425)
            ·
              refine ⟨7340979498784722201274069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9787972665046296268365425 7340979498784722201274069)
              ·
                refine ⟨172054207002766926592361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7340979498784722201274069 172054207002766926592361)
                ·
                  refine ⟨129040655252075194944271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172054207002766926592361 129040655252075194944271)
                  ·
                    rfl

theorem cell20_282719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 2].length) (baseStart_282719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282719 prefixEnd_282719 := by exact prefixLift 282719
  have htrace : WordTrace (prefixWord ++ tailWord_282719) baseStart_282719 baseEnd_282719 := by
    simpa [prefixWord, tailWord_282719, baseEnd_282719] using wordTrace_append hprefix tailTrace_282719
  have hstable : (prefixWord ++ tailWord_282719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282719).length < 2 ^ (prefixWord ++ tailWord_282719).sum := by decide
  have hdescent : baseEnd_282719 < baseStart_282719 := by decide
  rcases family_descends (prefixWord ++ tailWord_282719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282722 : List Nat := [3, 3, 2, 2, 3, 1, 6]
def baseStart_282722 : Nat := 118140960795 + 282722 * 2 ^ 59
def prefixEnd_282722 : Nat := 4983230072969 + 3 ^ 40 * 282722 * 2
def baseEnd_282722 : Nat := 14338002725980057538251

theorem tailTrace_282722 : CollatzResearch.WordTrace tailWord_282722 prefixEnd_282722 14338002725980057538251 := by
  unfold tailWord_282722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577929620438488479634605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6874478987835969279025613 2577929620438488479634605)
  ·
    refine ⟨966723607664433179862977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2577929620438488479634605 966723607664433179862977)
    ·
      refine ⟨725042705748324884897233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 966723607664433179862977 725042705748324884897233)
      ·
        refine ⟨543782029311243663672925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725042705748324884897233 543782029311243663672925)
        ·
          refine ⟨203918260991716373877347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543782029311243663672925 203918260991716373877347)
          ·
            refine ⟨305877391487574560816021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203918260991716373877347 305877391487574560816021)
            ·
              refine ⟨14338002725980057538251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 305877391487574560816021 14338002725980057538251)
              ·
                rfl

theorem cell20_282722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 6].length) (baseStart_282722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282722 prefixEnd_282722 := by exact prefixLift 282722
  have htrace : WordTrace (prefixWord ++ tailWord_282722) baseStart_282722 baseEnd_282722 := by
    simpa [prefixWord, tailWord_282722, baseEnd_282722] using wordTrace_append hprefix tailTrace_282722
  have hstable : (prefixWord ++ tailWord_282722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282722).length < 2 ^ (prefixWord ++ tailWord_282722).sum := by decide
  have hdescent : baseEnd_282722 < baseStart_282722 := by decide
  rcases family_descends (prefixWord ++ tailWord_282722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282733 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_282733 : Nat := 118140960795 + 282733 * 2 ^ 59
def prefixEnd_282733 : Nat := 4983230072969 + 3 ^ 40 * 282733 * 2
def baseEnd_282733 : Nat := 129047045233553368477547

theorem tailTrace_282733 : CollatzResearch.WordTrace tailWord_282733 prefixEnd_282733 129047045233553368477547 := by
  unfold tailWord_282733
  simp only [CollatzResearch.WordTrace]
  refine ⟨10312119684714102797188853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6874746456476068531459235 10312119684714102797188853)
  ·
    refine ⟨966761220441947137236455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10312119684714102797188853 966761220441947137236455)
    ·
      refine ⟨1450141830662920705854683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 966761220441947137236455 1450141830662920705854683)
      ·
        refine ⟨2175212745994381058782025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450141830662920705854683 2175212745994381058782025)
        ·
          refine ⟨1631409559495785794086519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2175212745994381058782025 1631409559495785794086519)
          ·
            refine ⟨2447114339243678691129779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631409559495785794086519 2447114339243678691129779)
            ·
              refine ⟨3670671508865518036694669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447114339243678691129779 3670671508865518036694669)
              ·
                refine ⟨1376501815824569263760501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3670671508865518036694669 1376501815824569263760501)
                ·
                  refine ⟨129047045233553368477547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1376501815824569263760501 129047045233553368477547)
                  ·
                    rfl

theorem cell20_282733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_282733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282733 prefixEnd_282733 := by exact prefixLift 282733
  have htrace : WordTrace (prefixWord ++ tailWord_282733) baseStart_282733 baseEnd_282733 := by
    simpa [prefixWord, tailWord_282733, baseEnd_282733] using wordTrace_append hprefix tailTrace_282733
  have hstable : (prefixWord ++ tailWord_282733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282733).length < 2 ^ (prefixWord ++ tailWord_282733).sum := by decide
  have hdescent : baseEnd_282733 < baseStart_282733 := by decide
  rcases family_descends (prefixWord ++ tailWord_282733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282785 : List Nat := [1, 2, 3, 3, 1, 10]
def baseStart_282785 : Nat := 118140960795 + 282785 * 2 ^ 59
def prefixEnd_282785 : Nat := 4983230072969 + 3 ^ 40 * 282785 * 2
def baseEnd_282785 : Nat := 4780399238906381434963

theorem tailTrace_282785 : CollatzResearch.WordTrace tailWord_282785 prefixEnd_282785 4780399238906381434963 := by
  unfold tailWord_282785
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314016280525715678081809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6876010853683810452054539 10314016280525715678081809)
  ·
    refine ⟨7735512210394286758561357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10314016280525715678081809 7735512210394286758561357)
    ·
      refine ⟨2900817078897857534460509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7735512210394286758561357 2900817078897857534460509)
      ·
        refine ⟨1087806404586696575422691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2900817078897857534460509 1087806404586696575422691)
        ·
          refine ⟨1631709606880044863134037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087806404586696575422691 1631709606880044863134037)
          ·
            refine ⟨4780399238906381434963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1631709606880044863134037 4780399238906381434963)
            ·
              rfl

theorem cell20_282785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 10].length) (baseStart_282785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282785 prefixEnd_282785 := by exact prefixLift 282785
  have htrace : WordTrace (prefixWord ++ tailWord_282785) baseStart_282785 baseEnd_282785 := by
    simpa [prefixWord, tailWord_282785, baseEnd_282785] using wordTrace_append hprefix tailTrace_282785
  have hstable : (prefixWord ++ tailWord_282785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282785).length < 2 ^ (prefixWord ++ tailWord_282785).sum := by decide
  have hdescent : baseEnd_282785 < baseStart_282785 := by decide
  rcases family_descends (prefixWord ++ tailWord_282785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282791 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 2]
def baseStart_282791 : Nat := 118140960795 + 282791 * 2 ^ 59
def prefixEnd_282791 : Nat := 4983230072969 + 3 ^ 40 * 282791 * 2
def baseEnd_282791 : Nat := 129073518013962944543977

theorem tailTrace_282791 : CollatzResearch.WordTrace tailWord_282791 prefixEnd_282791 129073518013962944543977 := by
  unfold tailWord_282791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314235118503978702800227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6876156745669319135200151 10314235118503978702800227)
  ·
    refine ⟨15471352677755968054200341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10314235118503978702800227 15471352677755968054200341)
    ·
      refine ⟨725219656769811002540641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15471352677755968054200341 725219656769811002540641)
      ·
        refine ⟨543914742577358251905481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725219656769811002540641 543914742577358251905481)
        ·
          refine ⟨407936056933018688929111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543914742577358251905481 407936056933018688929111)
          ·
            refine ⟨611904085399528033393667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407936056933018688929111 611904085399528033393667)
            ·
              refine ⟨917856128099292050090501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611904085399528033393667 917856128099292050090501)
              ·
                refine ⟨172098024018617259391969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 917856128099292050090501 172098024018617259391969)
                ·
                  refine ⟨129073518013962944543977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172098024018617259391969 129073518013962944543977)
                  ·
                    rfl

theorem cell20_282791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 2].length) (baseStart_282791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282791 prefixEnd_282791 := by exact prefixLift 282791
  have htrace : WordTrace (prefixWord ++ tailWord_282791) baseStart_282791 baseEnd_282791 := by
    simpa [prefixWord, tailWord_282791, baseEnd_282791] using wordTrace_append hprefix tailTrace_282791
  have hstable : (prefixWord ++ tailWord_282791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282791).length < 2 ^ (prefixWord ++ tailWord_282791).sum := by decide
  have hdescent : baseEnd_282791 < baseStart_282791 := by decide
  rcases family_descends (prefixWord ++ tailWord_282791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282809 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_282809 : Nat := 118140960795 + 282809 * 2 ^ 59
def prefixEnd_282809 : Nat := 4983230072969 + 3 ^ 40 * 282809 * 2
def baseEnd_282809 : Nat := 129081733704434881943903

theorem tailTrace_282809 : CollatzResearch.WordTrace tailWord_282809 prefixEnd_282809 129081733704434881943903 := by
  unfold tailWord_282809
  simp only [CollatzResearch.WordTrace]
  refine ⟨10314891632438767776955481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6876594421625845184636987 10314891632438767776955481)
  ·
    refine ⟨7736168724329075832716611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10314891632438767776955481 7736168724329075832716611)
    ·
      refine ⟨11604253086493613749074917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7736168724329075832716611 11604253086493613749074917)
      ·
        refine ⟨2175797453717552577951547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11604253086493613749074917 2175797453717552577951547)
        ·
          refine ⟨3263696180576328866927321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175797453717552577951547 3263696180576328866927321)
          ·
            refine ⟨2447772135432246650195491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3263696180576328866927321 2447772135432246650195491)
            ·
              refine ⟨3671658203148369975293237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447772135432246650195491 3671658203148369975293237)
              ·
                refine ⟨344217956545159685183741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3671658203148369975293237 344217956545159685183741)
                ·
                  refine ⟨129081733704434881943903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344217956545159685183741 129081733704434881943903)
                  ·
                    rfl

theorem cell20_282809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_282809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282809 prefixEnd_282809 := by exact prefixLift 282809
  have htrace : WordTrace (prefixWord ++ tailWord_282809) baseStart_282809 baseEnd_282809 := by
    simpa [prefixWord, tailWord_282809, baseEnd_282809] using wordTrace_append hprefix tailTrace_282809
  have hstable : (prefixWord ++ tailWord_282809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282809).length < 2 ^ (prefixWord ++ tailWord_282809).sum := by decide
  have hdescent : baseEnd_282809 < baseStart_282809 := by decide
  rcases family_descends (prefixWord ++ tailWord_282809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282816 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_282816 : Nat := 118140960795 + 282816 * 2 ^ 59
def prefixEnd_282816 : Nat := 4983230072969 + 3 ^ 40 * 282816 * 2
def baseEnd_282816 : Nat := 129084928695173968710541

theorem tailTrace_282816 : CollatzResearch.WordTrace tailWord_282816 prefixEnd_282816 129084928695173968710541 := by
  unfold tailWord_282816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157573471706703986230151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6876764628942271981640201 5157573471706703986230151)
  ·
    refine ⟨7736360207560055979345227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5157573471706703986230151 7736360207560055979345227)
    ·
      refine ⟨11604540311340083969017841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7736360207560055979345227 11604540311340083969017841)
      ·
        refine ⟨8703405233505062976763381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11604540311340083969017841 8703405233505062976763381)
        ·
          refine ⟨815944240641099654071567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8703405233505062976763381 815944240641099654071567)
          ·
            refine ⟨1223916360961649481107351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815944240641099654071567 1223916360961649481107351)
            ·
              refine ⟨1835874541442474221661027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223916360961649481107351 1835874541442474221661027)
              ·
                refine ⟨2753811812163711332491541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835874541442474221661027 2753811812163711332491541)
                ·
                  refine ⟨129084928695173968710541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2753811812163711332491541 129084928695173968710541)
                  ·
                    rfl

theorem cell20_282816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_282816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282816 prefixEnd_282816 := by exact prefixLift 282816
  have htrace : WordTrace (prefixWord ++ tailWord_282816) baseStart_282816 baseEnd_282816 := by
    simpa [prefixWord, tailWord_282816, baseEnd_282816] using wordTrace_append hprefix tailTrace_282816
  have hstable : (prefixWord ++ tailWord_282816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282816).length < 2 ^ (prefixWord ++ tailWord_282816).sum := by decide
  have hdescent : baseEnd_282816 < baseStart_282816 := by decide
  rcases family_descends (prefixWord ++ tailWord_282816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282833 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 2]
def baseStart_282833 : Nat := 118140960795 + 282833 * 2 ^ 59
def prefixEnd_282833 : Nat := 4983230072969 + 3 ^ 40 * 282833 * 2
def baseEnd_282833 : Nat := 129092687958397465143805

theorem tailTrace_282833 : CollatzResearch.WordTrace tailWord_282833 prefixEnd_282833 129092687958397465143805 := by
  unfold tailWord_282833
  simp only [CollatzResearch.WordTrace]
  refine ⟨10315766984351819875829153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6877177989567879917219435 10315766984351819875829153)
  ·
    refine ⟨7736825238263864906871865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10315766984351819875829153 7736825238263864906871865)
    ·
      refine ⟨5802618928697898680153899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7736825238263864906871865 5802618928697898680153899)
      ·
        refine ⟨8703928393046848020230849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802618928697898680153899 8703928393046848020230849)
        ·
          refine ⟨6527946294785136015173137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8703928393046848020230849 6527946294785136015173137)
          ·
            refine ⟨4895959721088852011379853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6527946294785136015173137 4895959721088852011379853)
            ·
              refine ⟨1835984895408319504267445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4895959721088852011379853 1835984895408319504267445)
              ·
                refine ⟨172123583944529953525073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1835984895408319504267445 172123583944529953525073)
                ·
                  refine ⟨129092687958397465143805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172123583944529953525073 129092687958397465143805)
                  ·
                    rfl

theorem cell20_282833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_282833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282833 prefixEnd_282833 := by exact prefixLift 282833
  have htrace : WordTrace (prefixWord ++ tailWord_282833) baseStart_282833 baseEnd_282833 := by
    simpa [prefixWord, tailWord_282833, baseEnd_282833] using wordTrace_append hprefix tailTrace_282833
  have hstable : (prefixWord ++ tailWord_282833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282833).length < 2 ^ (prefixWord ++ tailWord_282833).sum := by decide
  have hdescent : baseEnd_282833 < baseStart_282833 := by decide
  rcases family_descends (prefixWord ++ tailWord_282833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282878 : List Nat := [4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_282878 : Nat := 118140960795 + 282878 * 2 ^ 59
def prefixEnd_282878 : Nat := 4983230072969 + 3 ^ 40 * 282878 * 2
def baseEnd_282878 : Nat := 43037742394859102881207

theorem tailTrace_282878 : CollatzResearch.WordTrace tailWord_282878 prefixEnd_282878 43037742394859102881207 := by
  unfold tailWord_282878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289676033648599070152161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6878272179459195040811525 1289676033648599070152161)
  ·
    refine ⟨967257025236449302614121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1289676033648599070152161 967257025236449302614121)
    ·
      refine ⟨725442768927336976960591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 967257025236449302614121 725442768927336976960591)
      ·
        refine ⟨1088164153391005465440887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725442768927336976960591 1088164153391005465440887)
        ·
          refine ⟨1632246230086508198161331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088164153391005465440887 1632246230086508198161331)
          ·
            refine ⟨2448369345129762297241997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632246230086508198161331 2448369345129762297241997)
            ·
              refine ⟨918138504423660861465749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2448369345129762297241997 918138504423660861465749)
              ·
                refine ⟨43037742394859102881207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 918138504423660861465749 43037742394859102881207)
                ·
                  rfl

theorem cell20_282878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_282878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282878 prefixEnd_282878 := by exact prefixLift 282878
  have htrace : WordTrace (prefixWord ++ tailWord_282878) baseStart_282878 baseEnd_282878 := by
    simpa [prefixWord, tailWord_282878, baseEnd_282878] using wordTrace_append hprefix tailTrace_282878
  have hstable : (prefixWord ++ tailWord_282878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282878).length < 2 ^ (prefixWord ++ tailWord_282878).sum := by decide
  have hdescent : baseEnd_282878 < baseStart_282878 := by decide
  rcases family_descends (prefixWord ++ tailWord_282878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282884 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 2]
def baseStart_282884 : Nat := 118140960795 + 282884 * 2 ^ 59
def prefixEnd_282884 : Nat := 4983230072969 + 3 ^ 40 * 282884 * 2
def baseEnd_282884 : Nat := 129115965748067954443597

theorem tailTrace_282884 : CollatzResearch.WordTrace tailWord_282884 prefixEnd_282884 129115965748067954443597 := by
  unfold tailWord_282884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158813553583527792967853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6878418071444703723957137 5158813553583527792967853)
  ·
    refine ⟨1934555082593822922362945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5158813553583527792967853 1934555082593822922362945)
    ·
      refine ⟨1450916311945367191772209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1934555082593822922362945 1450916311945367191772209)
      ·
        refine ⟨1088187233959025393829157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1450916311945367191772209 1088187233959025393829157)
        ·
          refine ⟨204035106367317261342967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1088187233959025393829157 204035106367317261342967)
          ·
            refine ⟨306052659550975892014451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204035106367317261342967 306052659550975892014451)
            ·
              refine ⟨459078989326463838021677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306052659550975892014451 459078989326463838021677)
              ·
                refine ⟨172154620997423939258129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459078989326463838021677 172154620997423939258129)
                ·
                  refine ⟨129115965748067954443597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172154620997423939258129 129115965748067954443597)
                  ·
                    rfl

theorem cell20_282884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_282884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282884 prefixEnd_282884 := by exact prefixLift 282884
  have htrace : WordTrace (prefixWord ++ tailWord_282884) baseStart_282884 baseEnd_282884 := by
    simpa [prefixWord, tailWord_282884, baseEnd_282884] using wordTrace_append hprefix tailTrace_282884
  have hstable : (prefixWord ++ tailWord_282884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282884).length < 2 ^ (prefixWord ++ tailWord_282884).sum := by decide
  have hdescent : baseEnd_282884 < baseStart_282884 := by decide
  rcases family_descends (prefixWord ++ tailWord_282884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282888 : List Nat := [2, 1, 3, 2, 3, 1, 3, 3, 2]
def baseStart_282888 : Nat := 118140960795 + 282888 * 2 ^ 59
def prefixEnd_282888 : Nat := 4983230072969 + 3 ^ 40 * 282888 * 2
def baseEnd_282888 : Nat := 129117791457061718310247

theorem tailTrace_282888 : CollatzResearch.WordTrace tailWord_282888 prefixEnd_282888 129117791457061718310247 := by
  unfold tailWord_282888
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158886499576282134540659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6878515332768376179387545 5158886499576282134540659)
  ·
    refine ⟨7738329749364423201810989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5158886499576282134540659 7738329749364423201810989)
    ·
      refine ⟨2901873656011658700679121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7738329749364423201810989 2901873656011658700679121)
      ·
        refine ⟨2176405242008744025509341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2901873656011658700679121 2176405242008744025509341)
        ·
          refine ⟨816151965753279009566003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2176405242008744025509341 816151965753279009566003)
          ·
            refine ⟨1224227948629918514349005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816151965753279009566003 1224227948629918514349005)
            ·
              refine ⟨459085480736219442880877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1224227948629918514349005 459085480736219442880877)
              ·
                refine ⟨172157055276082291080329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459085480736219442880877 172157055276082291080329)
                ·
                  refine ⟨129117791457061718310247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172157055276082291080329 129117791457061718310247)
                  ·
                    rfl

theorem cell20_282888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 2].length) (baseStart_282888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282888 prefixEnd_282888 := by exact prefixLift 282888
  have htrace : WordTrace (prefixWord ++ tailWord_282888) baseStart_282888 baseEnd_282888 := by
    simpa [prefixWord, tailWord_282888, baseEnd_282888] using wordTrace_append hprefix tailTrace_282888
  have hstable : (prefixWord ++ tailWord_282888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282888).length < 2 ^ (prefixWord ++ tailWord_282888).sum := by decide
  have hdescent : baseEnd_282888 < baseStart_282888 := by decide
  rcases family_descends (prefixWord ++ tailWord_282888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282916 : List Nat := [2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_282916 : Nat := 118140960795 + 282916 * 2 ^ 59
def prefixEnd_282916 : Nat := 4983230072969 + 3 ^ 40 * 282916 * 2
def baseEnd_282916 : Nat := 43043523806672688458933

theorem tailTrace_282916 : CollatzResearch.WordTrace tailWord_282916 prefixEnd_282916 43043523806672688458933 := by
  unfold tailWord_282916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159397121525562525550301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6879196162034083367400401 5159397121525562525550301)
  ·
    refine ⟨1934773920572085947081363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5159397121525562525550301 1934773920572085947081363)
    ·
      refine ⟨2902160880858128920622045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934773920572085947081363 2902160880858128920622045)
      ·
        refine ⟨1088310330321798345233267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2902160880858128920622045 1088310330321798345233267)
        ·
          refine ⟨1632465495482697517849901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088310330321798345233267 1632465495482697517849901)
          ·
            refine ⟨612174560806011569193713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1632465495482697517849901 612174560806011569193713)
            ·
              refine ⟨459130920604508676895285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612174560806011569193713 459130920604508676895285)
              ·
                refine ⟨43043523806672688458933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459130920604508676895285 43043523806672688458933)
                ·
                  rfl

theorem cell20_282916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_282916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282916 prefixEnd_282916 := by exact prefixLift 282916
  have htrace : WordTrace (prefixWord ++ tailWord_282916) baseStart_282916 baseEnd_282916 := by
    simpa [prefixWord, tailWord_282916, baseEnd_282916] using wordTrace_append hprefix tailTrace_282916
  have hstable : (prefixWord ++ tailWord_282916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282916).length < 2 ^ (prefixWord ++ tailWord_282916).sum := by decide
  have hdescent : baseEnd_282916 < baseStart_282916 := by decide
  rcases family_descends (prefixWord ++ tailWord_282916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282944 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_282944 : Nat := 118140960795 + 282944 * 2 ^ 59
def prefixEnd_282944 : Nat := 4983230072969 + 3 ^ 40 * 282944 * 2
def baseEnd_282944 : Nat := 129143351382974412443351

theorem tailTrace_282944 : CollatzResearch.WordTrace tailWord_282944 prefixEnd_282944 129143351382974412443351 := by
  unfold tailWord_282944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159907743474842916559943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6879876991299790555413257 5159907743474842916559943)
  ·
    refine ⟨7739861615212264374839915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5159907743474842916559943 7739861615212264374839915)
    ·
      refine ⟨11609792422818396562259873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7739861615212264374839915 11609792422818396562259873)
      ·
        refine ⟨8707344317113797421694905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11609792422818396562259873 8707344317113797421694905)
        ·
          refine ⟨6530508237835348066271179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8707344317113797421694905 6530508237835348066271179)
          ·
            refine ⟨9795762356753022099406769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6530508237835348066271179 9795762356753022099406769)
            ·
              refine ⟨7346821767564766574555077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9795762356753022099406769 7346821767564766574555077)
              ·
                refine ⟨1377529081418393732729077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7346821767564766574555077 1377529081418393732729077)
                ·
                  refine ⟨129143351382974412443351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1377529081418393732729077 129143351382974412443351)
                  ·
                    rfl

theorem cell20_282944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_282944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282944 prefixEnd_282944 := by exact prefixLift 282944
  have htrace : WordTrace (prefixWord ++ tailWord_282944) baseStart_282944 baseEnd_282944 := by
    simpa [prefixWord, tailWord_282944, baseEnd_282944] using wordTrace_append hprefix tailTrace_282944
  have hstable : (prefixWord ++ tailWord_282944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282944).length < 2 ^ (prefixWord ++ tailWord_282944).sum := by decide
  have hdescent : baseEnd_282944 < baseStart_282944 := by decide
  rcases family_descends (prefixWord ++ tailWord_282944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282961 : List Nat := [1, 2, 2, 1, 4, 2, 1, 4, 3]
def baseStart_282961 : Nat := 118140960795 + 282961 * 2 ^ 59
def prefixEnd_282961 : Nat := 4983230072969 + 3 ^ 40 * 282961 * 2
def baseEnd_282961 : Nat := 129151110646197908876615

theorem tailTrace_282961 : CollatzResearch.WordTrace tailWord_282961 prefixEnd_282961 129151110646197908876615 := by
  unfold tailWord_282961
  simp only [CollatzResearch.WordTrace]
  refine ⟨10320435527888097736488737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6880290351925398490992491 10320435527888097736488737)
  ·
    refine ⟨7740326645916073302366553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10320435527888097736488737 7740326645916073302366553)
    ·
      refine ⟨5805244984437054976774915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7740326645916073302366553 5805244984437054976774915)
      ·
        refine ⟨8707867476655582465162373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5805244984437054976774915 8707867476655582465162373)
        ·
          refine ⟨1632725151872921712217945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8707867476655582465162373 1632725151872921712217945)
          ·
            refine ⟨1224543863904691284163459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632725151872921712217945 1224543863904691284163459)
            ·
              refine ⟨1836815795857036926245189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224543863904691284163459 1836815795857036926245189)
              ·
                refine ⟨344402961723194423670973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1836815795857036926245189 344402961723194423670973)
                ·
                  refine ⟨129151110646197908876615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344402961723194423670973 129151110646197908876615)
                  ·
                    rfl

theorem cell20_282961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_282961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282961 prefixEnd_282961 := by exact prefixLift 282961
  have htrace : WordTrace (prefixWord ++ tailWord_282961) baseStart_282961 baseEnd_282961 := by
    simpa [prefixWord, tailWord_282961, baseEnd_282961] using wordTrace_append hprefix tailTrace_282961
  have hstable : (prefixWord ++ tailWord_282961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282961).length < 2 ^ (prefixWord ++ tailWord_282961).sum := by decide
  have hdescent : baseEnd_282961 < baseStart_282961 := by decide
  rcases family_descends (prefixWord ++ tailWord_282961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282964 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 2]
def baseStart_282964 : Nat := 118140960795 + 282964 * 2 ^ 59
def prefixEnd_282964 : Nat := 4983230072969 + 3 ^ 40 * 282964 * 2
def baseEnd_282964 : Nat := 129152479927943231776603

theorem tailTrace_282964 : CollatzResearch.WordTrace tailWord_282964 prefixEnd_282964 129152479927943231776603 := by
  unfold tailWord_282964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160272473438614624423973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6880363297918152832565297 5160272473438614624423973)
  ·
    refine ⟨967551088769740242079495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5160272473438614624423973 967551088769740242079495)
    ·
      refine ⟨1451326633154610363119243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967551088769740242079495 1451326633154610363119243)
      ·
        refine ⟨2176989949731915544678865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451326633154610363119243 2176989949731915544678865)
        ·
          refine ⟨1632742462298936658509149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2176989949731915544678865 1632742462298936658509149)
          ·
            refine ⟨612278423362101246940931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1632742462298936658509149 612278423362101246940931)
            ·
              refine ⟨918417635043151870411397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612278423362101246940931 918417635043151870411397)
              ·
                refine ⟨172203306570590975702137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 918417635043151870411397 172203306570590975702137)
                ·
                  refine ⟨129152479927943231776603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172203306570590975702137 129152479927943231776603)
                  ·
                    rfl

theorem cell20_282964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_282964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282964 prefixEnd_282964 := by exact prefixLift 282964
  have htrace : WordTrace (prefixWord ++ tailWord_282964) baseStart_282964 baseEnd_282964 := by
    simpa [prefixWord, tailWord_282964, baseEnd_282964] using wordTrace_append hprefix tailTrace_282964
  have hstable : (prefixWord ++ tailWord_282964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282964).length < 2 ^ (prefixWord ++ tailWord_282964).sum := by decide
  have hdescent : baseEnd_282964 < baseStart_282964 := by decide
  rcases family_descends (prefixWord ++ tailWord_282964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282975 : List Nat := [1, 1, 2, 3, 1, 2, 5, 5]
def baseStart_282975 : Nat := 118140960795 + 282975 * 2 ^ 59
def prefixEnd_282975 : Nat := 4983230072969 + 3 ^ 40 * 282975 * 2
def baseEnd_282975 : Nat := 43052500209225360803297

theorem tailTrace_282975 : CollatzResearch.WordTrace tailWord_282975 prefixEnd_282975 43052500209225360803297 := by
  unfold tailWord_282975
  simp only [CollatzResearch.WordTrace]
  refine ⟨10320946149837378127498379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6880630766558252084998919 10320946149837378127498379)
  ·
    refine ⟨15481419224756067191247569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10320946149837378127498379 15481419224756067191247569)
    ·
      refine ⟨11611064418567050393435677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15481419224756067191247569 11611064418567050393435677)
      ·
        refine ⟨4354149156962643897538379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11611064418567050393435677 4354149156962643897538379)
        ·
          refine ⟨6531223735443965846307569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4354149156962643897538379 6531223735443965846307569)
          ·
            refine ⟨4898417801582974384730677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6531223735443965846307569 4898417801582974384730677)
            ·
              refine ⟨459226668898403848568501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4898417801582974384730677 459226668898403848568501)
              ·
                refine ⟨43052500209225360803297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459226668898403848568501 43052500209225360803297)
                ·
                  rfl

theorem cell20_282975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_282975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282975 prefixEnd_282975 := by exact prefixLift 282975
  have htrace : WordTrace (prefixWord ++ tailWord_282975) baseStart_282975 baseEnd_282975 := by
    simpa [prefixWord, tailWord_282975, baseEnd_282975] using wordTrace_append hprefix tailTrace_282975
  have hstable : (prefixWord ++ tailWord_282975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282975).length < 2 ^ (prefixWord ++ tailWord_282975).sum := by decide
  have hdescent : baseEnd_282975 < baseStart_282975 := by decide
  rcases family_descends (prefixWord ++ tailWord_282975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282978 : List Nat := [3, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_282978 : Nat := 118140960795 + 282978 * 2 ^ 59
def prefixEnd_282978 : Nat := 4983230072969 + 3 ^ 40 * 282978 * 2
def baseEnd_282978 : Nat := 129158869909421405309879

theorem tailTrace_282978 : CollatzResearch.WordTrace tailWord_282978 prefixEnd_282978 129158869909421405309879 := by
  unfold tailWord_282978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580263892206627409964397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6880703712551006426571725 2580263892206627409964397)
  ·
    refine ⟨967598959577485278736649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2580263892206627409964397 967598959577485278736649)
    ·
      refine ⟨725699219683113959052487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 967598959577485278736649 725699219683113959052487)
      ·
        refine ⟨1088548829524670938578731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725699219683113959052487 1088548829524670938578731)
        ·
          refine ⟨1632823244287006407868097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088548829524670938578731 1632823244287006407868097)
          ·
            refine ⟨1224617433215254805901073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632823244287006407868097 1224617433215254805901073)
            ·
              refine ⟨918463074911441104425805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1224617433215254805901073 918463074911441104425805)
              ·
                refine ⟨344423653091790414159677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918463074911441104425805 344423653091790414159677)
                ·
                  refine ⟨129158869909421405309879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344423653091790414159677 129158869909421405309879)
                  ·
                    rfl

theorem cell20_282978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_282978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282978 prefixEnd_282978 := by exact prefixLift 282978
  have htrace : WordTrace (prefixWord ++ tailWord_282978) baseStart_282978 baseEnd_282978 := by
    simpa [prefixWord, tailWord_282978, baseEnd_282978] using wordTrace_append hprefix tailTrace_282978
  have hstable : (prefixWord ++ tailWord_282978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282978).length < 2 ^ (prefixWord ++ tailWord_282978).sum := by decide
  have hdescent : baseEnd_282978 < baseStart_282978 := by decide
  rcases family_descends (prefixWord ++ tailWord_282978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282992 : List Nat := [2, 1, 1, 1, 4, 4, 3, 4]
def baseStart_282992 : Nat := 118140960795 + 282992 * 2 ^ 59
def prefixEnd_282992 : Nat := 4983230072969 + 3 ^ 40 * 282992 * 2
def baseEnd_282992 : Nat := 43055086630299859614385

theorem tailTrace_282992 : CollatzResearch.WordTrace tailWord_282992 prefixEnd_282992 43055086630299859614385 := by
  unfold tailWord_282992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160783095387895015433615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6881044127183860020578153 5160783095387895015433615)
  ·
    refine ⟨7741174643081842523150423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5160783095387895015433615 7741174643081842523150423)
    ·
      refine ⟨11611761964622763784725635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7741174643081842523150423 11611761964622763784725635)
      ·
        refine ⟨17417642946934145677088453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11611761964622763784725635 17417642946934145677088453)
        ·
          refine ⟨3265808052550152314454085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17417642946934145677088453 3265808052550152314454085)
          ·
            refine ⟨612339009853153558960141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3265808052550152314454085 612339009853153558960141)
            ·
              refine ⟨229627128694932584610053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 612339009853153558960141 229627128694932584610053)
              ·
                refine ⟨43055086630299859614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229627128694932584610053 43055086630299859614385)
                ·
                  rfl

theorem cell20_282992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_282992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282992 prefixEnd_282992 := by exact prefixLift 282992
  have htrace : WordTrace (prefixWord ++ tailWord_282992) baseStart_282992 baseEnd_282992 := by
    simpa [prefixWord, tailWord_282992, baseEnd_282992] using wordTrace_append hprefix tailTrace_282992
  have hstable : (prefixWord ++ tailWord_282992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282992).length < 2 ^ (prefixWord ++ tailWord_282992).sum := by decide
  have hdescent : baseEnd_282992 < baseStart_282992 := by decide
  rcases family_descends (prefixWord ++ tailWord_282992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_282998 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_282998 : Nat := 118140960795 + 282998 * 2 ^ 59
def prefixEnd_282998 : Nat := 4983230072969 + 3 ^ 40 * 282998 * 2
def baseEnd_282998 : Nat := 129167998454390224643131

theorem tailTrace_282998 : CollatzResearch.WordTrace tailWord_282998 prefixEnd_282998 129167998454390224643131 := by
  unfold tailWord_282998
  simp only [CollatzResearch.WordTrace]
  refine ⟨645111564297128315974103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6881190019169368703723765 645111564297128315974103)
  ·
    refine ⟨967667346445692473961155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 645111564297128315974103 967667346445692473961155)
    ·
      refine ⟨1451501019668538710941733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967667346445692473961155 1451501019668538710941733)
      ·
        refine ⟨272156441187851008301575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1451501019668538710941733 272156441187851008301575)
        ·
          refine ⟨408234661781776512452363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272156441187851008301575 408234661781776512452363)
          ·
            refine ⟨612351992672664768678545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408234661781776512452363 612351992672664768678545)
            ·
              refine ⟨459263994504498576508909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612351992672664768678545 459263994504498576508909)
              ·
                refine ⟨172223997939186966190841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459263994504498576508909 172223997939186966190841)
                ·
                  refine ⟨129167998454390224643131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172223997939186966190841 129167998454390224643131)
                  ·
                    rfl

theorem cell20_282998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_282998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_282998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_282998 prefixEnd_282998 := by exact prefixLift 282998
  have htrace : WordTrace (prefixWord ++ tailWord_282998) baseStart_282998 baseEnd_282998 := by
    simpa [prefixWord, tailWord_282998, baseEnd_282998] using wordTrace_append hprefix tailTrace_282998
  have hstable : (prefixWord ++ tailWord_282998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_282998).length < 2 ^ (prefixWord ++ tailWord_282998).sum := by decide
  have hdescent : baseEnd_282998 < baseStart_282998 := by decide
  rcases family_descends (prefixWord ++ tailWord_282998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283044 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_283044 : Nat := 118140960795 + 283044 * 2 ^ 59
def prefixEnd_283044 : Nat := 4983230072969 + 3 ^ 40 * 283044 * 2
def baseEnd_283044 : Nat := 129188994107818509109609

theorem tailTrace_283044 : CollatzResearch.WordTrace tailWord_283044 prefixEnd_283044 129188994107818509109609 := by
  unfold tailWord_283044
  simp only [CollatzResearch.WordTrace]
  refine ⟨5161731393293701455880093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6882308524391601941173457 5161731393293701455880093)
  ·
    refine ⟨1935649272485138045955035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5161731393293701455880093 1935649272485138045955035)
    ·
      refine ⟨2903473908727707068932553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935649272485138045955035 2903473908727707068932553)
      ·
        refine ⟨2177605431545780301699415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903473908727707068932553 2177605431545780301699415)
        ·
          refine ⟨3266408147318670452549123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2177605431545780301699415 3266408147318670452549123)
          ·
            refine ⟨4899612220978005678823685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3266408147318670452549123 4899612220978005678823685)
            ·
              refine ⟨918677291433376064779441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4899612220978005678823685 918677291433376064779441)
              ·
                refine ⟨689007968575032048584581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918677291433376064779441 689007968575032048584581)
                ·
                  refine ⟨129188994107818509109609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689007968575032048584581 129188994107818509109609)
                  ·
                    rfl

theorem cell20_283044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_283044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283044 prefixEnd_283044 := by exact prefixLift 283044
  have htrace : WordTrace (prefixWord ++ tailWord_283044) baseStart_283044 baseEnd_283044 := by
    simpa [prefixWord, tailWord_283044, baseEnd_283044] using wordTrace_append hprefix tailTrace_283044
  have hstable : (prefixWord ++ tailWord_283044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283044).length < 2 ^ (prefixWord ++ tailWord_283044).sum := by decide
  have hdescent : baseEnd_283044 < baseStart_283044 := by decide
  rcases family_descends (prefixWord ++ tailWord_283044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283047 : List Nat := [1, 1, 6, 1, 1, 4, 2, 4]
def baseStart_283047 : Nat := 118140960795 + 283047 * 2 ^ 59
def prefixEnd_283047 : Nat := 4983230072969 + 3 ^ 40 * 283047 * 2
def baseEnd_283047 : Nat := 43063454463187944003199

theorem tailTrace_283047 : CollatzResearch.WordTrace tailWord_283047 prefixEnd_283047 43063454463187944003199 := by
  unfold tailWord_283047
  simp only [CollatzResearch.WordTrace]
  refine ⟨10323572205576534424119395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6882381470384356282746263 10323572205576534424119395)
  ·
    refine ⟨15485358308364801636179093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10323572205576534424119395 15485358308364801636179093)
    ·
      refine ⟨725876170704600076695895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15485358308364801636179093 725876170704600076695895)
      ·
        refine ⟨1088814256056900115043843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725876170704600076695895 1088814256056900115043843)
        ·
          refine ⟨1633221384085350172565765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088814256056900115043843 1633221384085350172565765)
          ·
            refine ⟨306229009516003157356081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1633221384085350172565765 306229009516003157356081)
            ·
              refine ⟨229671757137002368017061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306229009516003157356081 229671757137002368017061)
              ·
                refine ⟨43063454463187944003199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229671757137002368017061 43063454463187944003199)
                ·
                  rfl

theorem cell20_283047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_283047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283047 prefixEnd_283047 := by exact prefixLift 283047
  have htrace : WordTrace (prefixWord ++ tailWord_283047) baseStart_283047 baseEnd_283047 := by
    simpa [prefixWord, tailWord_283047, baseEnd_283047] using wordTrace_append hprefix tailTrace_283047
  have hstable : (prefixWord ++ tailWord_283047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283047).length < 2 ^ (prefixWord ++ tailWord_283047).sum := by decide
  have hdescent : baseEnd_283047 < baseStart_283047 := by decide
  rcases family_descends (prefixWord ++ tailWord_283047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283058 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_283058 : Nat := 118140960795 + 283058 * 2 ^ 59
def prefixEnd_283058 : Nat := 4983230072969 + 3 ^ 40 * 283058 * 2
def baseEnd_283058 : Nat := 129195384089296682642885

theorem tailTrace_283058 : CollatzResearch.WordTrace tailWord_283058 prefixEnd_283058 129195384089296682642885 := by
  unfold tailWord_283058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580993352134170825692457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6882648939024455535179885 2580993352134170825692457)
  ·
    refine ⟨1935745014100628119269343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2580993352134170825692457 1935745014100628119269343)
    ·
      refine ⟨2903617521150942178904015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935745014100628119269343 2903617521150942178904015)
      ·
        refine ⟨4355426281726413268356023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2903617521150942178904015 4355426281726413268356023)
        ·
          refine ⟨6533139422589619902534035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355426281726413268356023 6533139422589619902534035)
          ·
            refine ⟨9799709133884429853801053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6533139422589619902534035 9799709133884429853801053)
            ·
              refine ⟨3674890925206661195175395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9799709133884429853801053 3674890925206661195175395)
              ·
                refine ⟨5512336387809991792763093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3674890925206661195175395 5512336387809991792763093)
                ·
                  refine ⟨129195384089296682642885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5512336387809991792763093 129195384089296682642885)
                  ·
                    rfl

theorem cell20_283058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_283058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283058 prefixEnd_283058 := by exact prefixLift 283058
  have htrace : WordTrace (prefixWord ++ tailWord_283058) baseStart_283058 baseEnd_283058 := by
    simpa [prefixWord, tailWord_283058, baseEnd_283058] using wordTrace_append hprefix tailTrace_283058
  have hstable : (prefixWord ++ tailWord_283058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283058).length < 2 ^ (prefixWord ++ tailWord_283058).sum := by decide
  have hdescent : baseEnd_283058 < baseStart_283058 := by decide
  rcases family_descends (prefixWord ++ tailWord_283058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283068 : List Nat := [2, 2, 2, 4, 1, 3, 6]
def baseStart_283068 : Nat := 118140960795 + 283068 * 2 ^ 59
def prefixEnd_283068 : Nat := 4983230072969 + 3 ^ 40 * 283068 * 2
def baseEnd_283068 : Nat := 14355549817975676923279

theorem tailTrace_283068 : CollatzResearch.WordTrace tailWord_283068 prefixEnd_283068 14355549817975676923279 := by
  unfold tailWord_283068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162169069250227505316929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6882892092333636673755905 5162169069250227505316929)
  ·
    refine ⟨3871626801937670628987697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5162169069250227505316929 3871626801937670628987697)
    ·
      refine ⟨2903720101453252971740773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3871626801937670628987697 2903720101453252971740773)
      ·
        refine ⟨544447519022484932201395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2903720101453252971740773 544447519022484932201395)
        ·
          refine ⟨816671278533727398302093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544447519022484932201395 816671278533727398302093)
          ·
            refine ⟨306251729450147774363285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 816671278533727398302093 306251729450147774363285)
            ·
              refine ⟨14355549817975676923279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 306251729450147774363285 14355549817975676923279)
              ·
                rfl

theorem cell20_283068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 6].length) (baseStart_283068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283068 prefixEnd_283068 := by exact prefixLift 283068
  have htrace : WordTrace (prefixWord ++ tailWord_283068) baseStart_283068 baseEnd_283068 := by
    simpa [prefixWord, tailWord_283068, baseEnd_283068] using wordTrace_append hprefix tailTrace_283068
  have hstable : (prefixWord ++ tailWord_283068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283068).length < 2 ^ (prefixWord ++ tailWord_283068).sum := by decide
  have hdescent : baseEnd_283068 < baseStart_283068 := by decide
  rcases family_descends (prefixWord ++ tailWord_283068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283092 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_283092 : Nat := 118140960795 + 283092 * 2 ^ 59
def prefixEnd_283092 : Nat := 4983230072969 + 3 ^ 40 * 283092 * 2
def baseEnd_283092 : Nat := 129210902615743675509413

theorem tailTrace_283092 : CollatzResearch.WordTrace tailWord_283092 prefixEnd_283092 129210902615743675509413 := by
  unfold tailWord_283092
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162606745206753554753765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6883475660275671406338353 5162606745206753554753765)
  ·
    refine ⟨967988764726266291516331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5162606745206753554753765 967988764726266291516331)
    ·
      refine ⟨1451983147089399437274497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967988764726266291516331 1451983147089399437274497)
      ·
        refine ⟨1088987360317049577955873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451983147089399437274497 1088987360317049577955873)
        ·
          refine ⟨816740520237787183466905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088987360317049577955873 816740520237787183466905)
          ·
            refine ⟨612555390178340387600179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816740520237787183466905 612555390178340387600179)
            ·
              refine ⟨918833085267510581400269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612555390178340387600179 918833085267510581400269)
              ·
                refine ⟨344562406975316468025101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918833085267510581400269 344562406975316468025101)
                ·
                  refine ⟨129210902615743675509413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344562406975316468025101 129210902615743675509413)
                  ·
                    rfl

theorem cell20_283092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_283092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283092 prefixEnd_283092 := by exact prefixLift 283092
  have htrace : WordTrace (prefixWord ++ tailWord_283092) baseStart_283092 baseEnd_283092 := by
    simpa [prefixWord, tailWord_283092, baseEnd_283092] using wordTrace_append hprefix tailTrace_283092
  have hstable : (prefixWord ++ tailWord_283092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283092).length < 2 ^ (prefixWord ++ tailWord_283092).sum := by decide
  have hdescent : baseEnd_283092 < baseStart_283092 := by decide
  rcases family_descends (prefixWord ++ tailWord_283092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283181 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 3]
def baseStart_283181 : Nat := 118140960795 + 283181 * 2 ^ 59
def prefixEnd_283181 : Nat := 4983230072969 + 3 ^ 40 * 283181 * 2
def baseEnd_283181 : Nat := 129251524640854921542383

theorem tailTrace_283181 : CollatzResearch.WordTrace tailWord_283181 prefixEnd_283181 129251524640854921542383 := by
  unfold tailWord_283181
  simp only [CollatzResearch.WordTrace]
  refine ⟨10328459587091075309497397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6885639724727383539664931 10328459587091075309497397)
  ·
    refine ⟨968293086289788310265381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10328459587091075309497397 968293086289788310265381)
    ·
      refine ⟨181554953679335308174759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 968293086289788310265381 181554953679335308174759)
      ·
        refine ⟨272332430519002962262139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181554953679335308174759 272332430519002962262139)
        ·
          refine ⟨408498645778504443393209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272332430519002962262139 408498645778504443393209)
          ·
            refine ⟨306373984333878332544907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408498645778504443393209 306373984333878332544907)
            ·
              refine ⟨459560976500817498817361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306373984333878332544907 459560976500817498817361)
              ·
                refine ⟨344670732375613124113021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459560976500817498817361 344670732375613124113021)
                ·
                  refine ⟨129251524640854921542383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344670732375613124113021 129251524640854921542383)
                  ·
                    rfl

theorem cell20_283181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_283181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283181 prefixEnd_283181 := by exact prefixLift 283181
  have htrace : WordTrace (prefixWord ++ tailWord_283181) baseStart_283181 baseEnd_283181 := by
    simpa [prefixWord, tailWord_283181, baseEnd_283181] using wordTrace_append hprefix tailTrace_283181
  have hstable : (prefixWord ++ tailWord_283181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283181).length < 2 ^ (prefixWord ++ tailWord_283181).sum := by decide
  have hdescent : baseEnd_283181 < baseStart_283181 := by decide
  rcases family_descends (prefixWord ++ tailWord_283181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283182 : List Nat := [4, 1, 3, 1, 3, 1, 7]
def baseStart_283182 : Nat := 118140960795 + 283182 * 2 ^ 59
def prefixEnd_283182 : Nat := 4983230072969 + 3 ^ 40 * 283182 * 2
def baseEnd_283182 : Nat := 14361331229789262501005

theorem tailTrace_283182 : CollatzResearch.WordTrace tailWord_283182 prefixEnd_283182 14361331229789262501005 := by
  unfold tailWord_283182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291062007510931560035475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6885664040058301653522533 1291062007510931560035475)
  ·
    refine ⟨1936593011266397340053213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1291062007510931560035475 1936593011266397340053213)
    ·
      refine ⟨726222379224899002519955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1936593011266397340053213 726222379224899002519955)
      ·
        refine ⟨1089333568837348503779933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726222379224899002519955 1089333568837348503779933)
        ·
          refine ⟨408500088314005688917475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1089333568837348503779933 408500088314005688917475)
          ·
            refine ⟨612750132471008533376213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408500088314005688917475 612750132471008533376213)
            ·
              refine ⟨14361331229789262501005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 612750132471008533376213 14361331229789262501005)
              ·
                rfl

theorem cell20_283182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 7].length) (baseStart_283182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283182 prefixEnd_283182 := by exact prefixLift 283182
  have htrace : WordTrace (prefixWord ++ tailWord_283182) baseStart_283182 baseEnd_283182 := by
    simpa [prefixWord, tailWord_283182, baseEnd_283182] using wordTrace_append hprefix tailTrace_283182
  have hstable : (prefixWord ++ tailWord_283182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283182).length < 2 ^ (prefixWord ++ tailWord_283182).sum := by decide
  have hdescent : baseEnd_283182 < baseStart_283182 := by decide
  rcases family_descends (prefixWord ++ tailWord_283182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283196 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_283196 : Nat := 118140960795 + 283196 * 2 ^ 59
def prefixEnd_283196 : Nat := 4983230072969 + 3 ^ 40 * 283196 * 2
def baseEnd_283196 : Nat := 129258371049581536042321

theorem tailTrace_283196 : CollatzResearch.WordTrace tailWord_283196 prefixEnd_283196 129258371049581536042321 := by
  unfold tailWord_283196
  simp only [CollatzResearch.WordTrace]
  refine ⟨5164503341018366435646721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6886004454691155247528961 5164503341018366435646721)
  ·
    refine ⟨3873377505763774826735041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5164503341018366435646721 3873377505763774826735041)
    ·
      refine ⟨2905033129322831120051281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3873377505763774826735041 2905033129322831120051281)
      ·
        refine ⟨2178774846992123340038461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2905033129322831120051281 2178774846992123340038461)
        ·
          refine ⟨817040567622046252514423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2178774846992123340038461 817040567622046252514423)
          ·
            refine ⟨1225560851433069378771635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817040567622046252514423 1225560851433069378771635)
            ·
              refine ⟨1838341277149604068157453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225560851433069378771635 1838341277149604068157453)
              ·
                refine ⟨689377978931101525559045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1838341277149604068157453 689377978931101525559045)
                ·
                  refine ⟨129258371049581536042321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689377978931101525559045 129258371049581536042321)
                  ·
                    rfl

theorem cell20_283196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_283196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283196 prefixEnd_283196 := by exact prefixLift 283196
  have htrace : WordTrace (prefixWord ++ tailWord_283196) baseStart_283196 baseEnd_283196 := by
    simpa [prefixWord, tailWord_283196, baseEnd_283196] using wordTrace_append hprefix tailTrace_283196
  have hstable : (prefixWord ++ tailWord_283196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283196).length < 2 ^ (prefixWord ++ tailWord_283196).sum := by decide
  have hdescent : baseEnd_283196 < baseStart_283196 := by decide
  rcases family_descends (prefixWord ++ tailWord_283196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283213 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_283213 : Nat := 118140960795 + 283213 * 2 ^ 59
def prefixEnd_283213 : Nat := 4983230072969 + 3 ^ 40 * 283213 * 2
def baseEnd_283213 : Nat := 129266130312805032475585

theorem tailTrace_283213 : CollatzResearch.WordTrace tailWord_283213 prefixEnd_283213 129266130312805032475585 := by
  unfold tailWord_283213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329626722975144774662293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6886417815316763183108195 10329626722975144774662293)
  ·
    refine ⟨484201252639459911312295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10329626722975144774662293 484201252639459911312295)
    ·
      refine ⟨726301878959189866968443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484201252639459911312295 726301878959189866968443)
      ·
        refine ⟨1089452818438784800452665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726301878959189866968443 1089452818438784800452665)
        ·
          refine ⟨817089613829088600339499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089452818438784800452665 817089613829088600339499)
          ·
            refine ⟨1225634420743632900509249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817089613829088600339499 1225634420743632900509249)
            ·
              refine ⟨919225815557724675381937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225634420743632900509249 919225815557724675381937)
              ·
                refine ⟨689419361668293506536453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919225815557724675381937 689419361668293506536453)
                ·
                  refine ⟨129266130312805032475585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689419361668293506536453 129266130312805032475585)
                  ·
                    rfl

theorem cell20_283213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_283213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283213 prefixEnd_283213 := by exact prefixLift 283213
  have htrace : WordTrace (prefixWord ++ tailWord_283213) baseStart_283213 baseEnd_283213 := by
    simpa [prefixWord, tailWord_283213, baseEnd_283213] using wordTrace_append hprefix tailTrace_283213
  have hstable : (prefixWord ++ tailWord_283213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283213).length < 2 ^ (prefixWord ++ tailWord_283213).sum := by decide
  have hdescent : baseEnd_283213 < baseStart_283213 := by decide
  rcases family_descends (prefixWord ++ tailWord_283213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283220 : List Nat := [2, 4, 1, 1, 1, 3, 4, 4]
def baseStart_283220 : Nat := 118140960795 + 283220 * 2 ^ 59
def prefixEnd_283220 : Nat := 4983230072969 + 3 ^ 40 * 283220 * 2
def baseEnd_283220 : Nat := 43089775101181373080741

theorem tailTrace_283220 : CollatzResearch.WordTrace tailWord_283220 prefixEnd_283220 43089775101181373080741 := by
  unfold tailWord_283220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5164941016974892485083557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6886588022633189980111409 5164941016974892485083557)
  ·
    refine ⟨968426440682792340953167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5164941016974892485083557 968426440682792340953167)
    ·
      refine ⟨1452639661024188511429751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968426440682792340953167 1452639661024188511429751)
      ·
        refine ⟨2178959491536282767144627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1452639661024188511429751 2178959491536282767144627)
        ·
          refine ⟨3268439237304424150716941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178959491536282767144627 3268439237304424150716941)
          ·
            refine ⟨1225664713989159056518853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3268439237304424150716941 1225664713989159056518853)
            ·
              refine ⟨229812133872967323097285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1225664713989159056518853 229812133872967323097285)
              ·
                refine ⟨43089775101181373080741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229812133872967323097285 43089775101181373080741)
                ·
                  rfl

theorem cell20_283220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_283220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283220 prefixEnd_283220 := by exact prefixLift 283220
  have htrace : WordTrace (prefixWord ++ tailWord_283220) baseStart_283220 baseEnd_283220 := by
    simpa [prefixWord, tailWord_283220, baseEnd_283220] using wordTrace_append hprefix tailTrace_283220
  have hstable : (prefixWord ++ tailWord_283220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283220).length < 2 ^ (prefixWord ++ tailWord_283220).sum := by decide
  have hdescent : baseEnd_283220 < baseStart_283220 := by decide
  rcases family_descends (prefixWord ++ tailWord_283220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283261 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 3]
def baseStart_283261 : Nat := 118140960795 + 283261 * 2 ^ 59
def prefixEnd_283261 : Nat := 4983230072969 + 3 ^ 40 * 283261 * 2
def baseEnd_283261 : Nat := 129288038820730198875389

theorem tailTrace_283261 : CollatzResearch.WordTrace tailWord_283261 prefixEnd_283261 129288038820730198875389 := by
  unfold tailWord_283261
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331377426801248972409637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6887584951200832648273091 10331377426801248972409637)
  ·
    refine ⟨1937133267525234182326807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10331377426801248972409637 1937133267525234182326807)
    ·
      refine ⟨2905699901287851273490211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1937133267525234182326807 2905699901287851273490211)
      ·
        refine ⟨4358549851931776910235317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905699901287851273490211 4358549851931776910235317)
        ·
          refine ⟨408614048618604085334561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4358549851931776910235317 408614048618604085334561)
          ·
            refine ⟨306460536463953064000921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408614048618604085334561 306460536463953064000921)
            ·
              refine ⟨229845402347964798000691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306460536463953064000921 229845402347964798000691)
              ·
                refine ⟨344768103521947197001037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229845402347964798000691 344768103521947197001037)
                ·
                  refine ⟨129288038820730198875389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344768103521947197001037 129288038820730198875389)
                  ·
                    rfl

theorem cell20_283261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_283261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283261 prefixEnd_283261 := by exact prefixLift 283261
  have htrace : WordTrace (prefixWord ++ tailWord_283261) baseStart_283261 baseEnd_283261 := by
    simpa [prefixWord, tailWord_283261, baseEnd_283261] using wordTrace_append hprefix tailTrace_283261
  have hstable : (prefixWord ++ tailWord_283261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283261).length < 2 ^ (prefixWord ++ tailWord_283261).sum := by decide
  have hdescent : baseEnd_283261 < baseStart_283261 := by decide
  rcases family_descends (prefixWord ++ tailWord_283261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283265 : List Nat := [1, 2, 4, 2, 1, 1, 3, 3, 3]
def baseStart_283265 : Nat := 118140960795 + 283265 * 2 ^ 59
def prefixEnd_283265 : Nat := 4983230072969 + 3 ^ 40 * 283265 * 2
def baseEnd_283265 : Nat := 129289864529723962742039

theorem tailTrace_283265 : CollatzResearch.WordTrace tailWord_283265 prefixEnd_283265 129289864529723962742039 := by
  unfold tailWord_283265
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331523318786757655555249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6887682212524505103703499 10331523318786757655555249)
  ·
    refine ⟨7748642489090068241666437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10331523318786757655555249 7748642489090068241666437)
    ·
      refine ⟨1452870466704387795312457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7748642489090068241666437 1452870466704387795312457)
      ·
        refine ⟨1089652850028290846484343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1452870466704387795312457 1089652850028290846484343)
        ·
          refine ⟨1634479275042436269726515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089652850028290846484343 1634479275042436269726515)
          ·
            refine ⟨2451718912563654404589773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634479275042436269726515 2451718912563654404589773)
            ·
              refine ⟨919394592211370401721165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2451718912563654404589773 919394592211370401721165)
              ·
                refine ⟨344772972079263900645437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 919394592211370401721165 344772972079263900645437)
                ·
                  refine ⟨129289864529723962742039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344772972079263900645437 129289864529723962742039)
                  ·
                    rfl

theorem cell20_283265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_283265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283265 prefixEnd_283265 := by exact prefixLift 283265
  have htrace : WordTrace (prefixWord ++ tailWord_283265) baseStart_283265 baseEnd_283265 := by
    simpa [prefixWord, tailWord_283265, baseEnd_283265] using wordTrace_append hprefix tailTrace_283265
  have hstable : (prefixWord ++ tailWord_283265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283265).length < 2 ^ (prefixWord ++ tailWord_283265).sum := by decide
  have hdescent : baseEnd_283265 < baseStart_283265 := by decide
  rcases family_descends (prefixWord ++ tailWord_283265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283313 : List Nat := [1, 2, 2, 6, 1, 2, 1, 5]
def baseStart_283313 : Nat := 118140960795 + 283313 * 2 ^ 59
def prefixEnd_283313 : Nat := 4983230072969 + 3 ^ 40 * 283313 * 2
def baseEnd_283313 : Nat := 43103924345883043047281

theorem tailTrace_283313 : CollatzResearch.WordTrace tailWord_283313 prefixEnd_283313 43103924345883043047281 := by
  unfold tailWord_283313
  simp only [CollatzResearch.WordTrace]
  refine ⟨10333274022612861853302593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6888849348408574568868395 10333274022612861853302593)
  ·
    refine ⟨7749955516959646389976945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10333274022612861853302593 7749955516959646389976945)
    ·
      refine ⟨5812466637719734792482709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7749955516959646389976945 5812466637719734792482709)
      ·
        refine ⟨272459373643112568397627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5812466637719734792482709 272459373643112568397627)
        ·
          refine ⟨408689060464668852596441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272459373643112568397627 408689060464668852596441)
          ·
            refine ⟨306516795348501639447331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408689060464668852596441 306516795348501639447331)
            ·
              refine ⟨459775193022752459170997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306516795348501639447331 459775193022752459170997)
              ·
                refine ⟨43103924345883043047281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459775193022752459170997 43103924345883043047281)
                ·
                  rfl

theorem cell20_283313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_283313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283313 prefixEnd_283313 := by exact prefixLift 283313
  have htrace : WordTrace (prefixWord ++ tailWord_283313) baseStart_283313 baseEnd_283313 := by
    simpa [prefixWord, tailWord_283313, baseEnd_283313] using wordTrace_append hprefix tailTrace_283313
  have hstable : (prefixWord ++ tailWord_283313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283313).length < 2 ^ (prefixWord ++ tailWord_283313).sum := by decide
  have hdescent : baseEnd_283313 < baseStart_283313 := by decide
  rcases family_descends (prefixWord ++ tailWord_283313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283365 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 2]
def baseStart_283365 : Nat := 118140960795 + 283365 * 2 ^ 59
def prefixEnd_283365 : Nat := 4983230072969 + 3 ^ 40 * 283365 * 2
def baseEnd_283365 : Nat := 129335507254568059408297

theorem tailTrace_283365 : CollatzResearch.WordTrace tailWord_283365 prefixEnd_283365 129335507254568059408297 := by
  unfold tailWord_283365
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335170618424474734195549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6890113745616316489463699 10335170618424474734195549)
  ·
    refine ⟨3875688981909178025323331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10335170618424474734195549 3875688981909178025323331)
    ·
      refine ⟨5813533472863767037984997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875688981909178025323331 5813533472863767037984997)
      ·
        refine ⟨1090037526161956319622187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5813533472863767037984997 1090037526161956319622187)
        ·
          refine ⟨1635056289242934479433281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090037526161956319622187 1635056289242934479433281)
          ·
            refine ⟨1226292216932200859574961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635056289242934479433281 1226292216932200859574961)
            ·
              refine ⟨919719162699150644681221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226292216932200859574961 919719162699150644681221)
              ·
                refine ⟨172447343006090745877729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 919719162699150644681221 172447343006090745877729)
                ·
                  refine ⟨129335507254568059408297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172447343006090745877729 129335507254568059408297)
                  ·
                    rfl

theorem cell20_283365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_283365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283365 prefixEnd_283365 := by exact prefixLift 283365
  have htrace : WordTrace (prefixWord ++ tailWord_283365) baseStart_283365 baseEnd_283365 := by
    simpa [prefixWord, tailWord_283365, baseEnd_283365] using wordTrace_append hprefix tailTrace_283365
  have hstable : (prefixWord ++ tailWord_283365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283365).length < 2 ^ (prefixWord ++ tailWord_283365).sum := by decide
  have hdescent : baseEnd_283365 < baseStart_283365 := by decide
  rcases family_descends (prefixWord ++ tailWord_283365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283369 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_283369 : Nat := 118140960795 + 283369 * 2 ^ 59
def prefixEnd_283369 : Nat := 4983230072969 + 3 ^ 40 * 283369 * 2
def baseEnd_283369 : Nat := 129337332963561823274947

theorem tailTrace_283369 : CollatzResearch.WordTrace tailWord_283369 prefixEnd_283369 129337332963561823274947 := by
  unfold tailWord_283369
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335316510409983417341161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6890211006939988944894107 10335316510409983417341161)
  ·
    refine ⟨7751487382807487563005871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10335316510409983417341161 7751487382807487563005871)
    ·
      refine ⟨11627231074211231344508807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7751487382807487563005871 11627231074211231344508807)
      ·
        refine ⟨17440846611316847016763211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11627231074211231344508807 17440846611316847016763211)
        ·
          refine ⟨26161269916975270525144817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17440846611316847016763211 26161269916975270525144817)
          ·
            refine ⟨19620952437731452893858613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26161269916975270525144817 19620952437731452893858613)
            ·
              refine ⟨1839464291037323708799245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19620952437731452893858613 1839464291037323708799245)
              ·
                refine ⟨689799109138996390799717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1839464291037323708799245 689799109138996390799717)
                ·
                  refine ⟨129337332963561823274947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689799109138996390799717 129337332963561823274947)
                  ·
                    rfl

theorem cell20_283369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_283369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283369 prefixEnd_283369 := by exact prefixLift 283369
  have htrace : WordTrace (prefixWord ++ tailWord_283369) baseStart_283369 baseEnd_283369 := by
    simpa [prefixWord, tailWord_283369, baseEnd_283369] using wordTrace_append hprefix tailTrace_283369
  have hstable : (prefixWord ++ tailWord_283369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283369).length < 2 ^ (prefixWord ++ tailWord_283369).sum := by decide
  have hdescent : baseEnd_283369 < baseStart_283369 := by decide
  rcases family_descends (prefixWord ++ tailWord_283369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283376 : List Nat := [2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_283376 : Nat := 118140960795 + 283376 * 2 ^ 59
def prefixEnd_283376 : Nat := 4983230072969 + 3 ^ 40 * 283376 * 2
def baseEnd_283376 : Nat := 43113509318100303347195

theorem tailTrace_283376 : CollatzResearch.WordTrace tailWord_283376 prefixEnd_283376 43113509318100303347195 := by
  unfold tailWord_283376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167785910692311806422991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6890381214256415741897321 5167785910692311806422991)
  ·
    refine ⟨7751678866038467709634487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5167785910692311806422991 7751678866038467709634487)
    ·
      refine ⟨11627518299057701564451731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7751678866038467709634487 11627518299057701564451731)
      ·
        refine ⟨17441277448586552346677597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11627518299057701564451731 17441277448586552346677597)
        ·
          refine ⟨6540479043219957130004099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17441277448586552346677597 6540479043219957130004099)
          ·
            refine ⟨9810718564829935695006149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6540479043219957130004099 9810718564829935695006149)
            ·
              refine ⟨1839509730905612942813653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9810718564829935695006149 1839509730905612942813653)
              ·
                refine ⟨43113509318100303347195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1839509730905612942813653 43113509318100303347195)
                ·
                  rfl

theorem cell20_283376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_283376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283376 prefixEnd_283376 := by exact prefixLift 283376
  have htrace : WordTrace (prefixWord ++ tailWord_283376) baseStart_283376 baseEnd_283376 := by
    simpa [prefixWord, tailWord_283376, baseEnd_283376] using wordTrace_append hprefix tailTrace_283376
  have hstable : (prefixWord ++ tailWord_283376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283376).length < 2 ^ (prefixWord ++ tailWord_283376).sum := by decide
  have hdescent : baseEnd_283376 < baseStart_283376 := by decide
  rcases family_descends (prefixWord ++ tailWord_283376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283400 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_283400 : Nat := 118140960795 + 283400 * 2 ^ 59
def prefixEnd_283400 : Nat := 4983230072969 + 3 ^ 40 * 283400 * 2
def baseEnd_283400 : Nat := 129351482208263493241487

theorem tailTrace_283400 : CollatzResearch.WordTrace tailWord_283400 prefixEnd_283400 129351482208263493241487 := by
  unfold tailWord_283400
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168223586648837855859827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6890964782198450474479769 5168223586648837855859827)
  ·
    refine ⟨7752335379973256783789741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168223586648837855859827 7752335379973256783789741)
    ·
      refine ⟨2907125767489971293921153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7752335379973256783789741 2907125767489971293921153)
      ·
        refine ⟨2180344325617478470440865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2907125767489971293921153 2180344325617478470440865)
        ·
          refine ⟨1635258244213108852830649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180344325617478470440865 1635258244213108852830649)
          ·
            refine ⟨1226443683159831639622987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635258244213108852830649 1226443683159831639622987)
            ·
              refine ⟨1839665524739747459434481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226443683159831639622987 1839665524739747459434481)
              ·
                refine ⟨1379749143554810594575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839665524739747459434481 1379749143554810594575861)
                ·
                  refine ⟨129351482208263493241487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1379749143554810594575861 129351482208263493241487)
                  ·
                    rfl

theorem cell20_283400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_283400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283400 prefixEnd_283400 := by exact prefixLift 283400
  have htrace : WordTrace (prefixWord ++ tailWord_283400) baseStart_283400 baseEnd_283400 := by
    simpa [prefixWord, tailWord_283400, baseEnd_283400] using wordTrace_append hprefix tailTrace_283400
  have hstable : (prefixWord ++ tailWord_283400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283400).length < 2 ^ (prefixWord ++ tailWord_283400).sum := by decide
  have hdescent : baseEnd_283400 < baseStart_283400 := by decide
  rcases family_descends (prefixWord ++ tailWord_283400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283420 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 2]
def baseStart_283420 : Nat := 118140960795 + 283420 * 2 ^ 59
def prefixEnd_283420 : Nat := 4983230072969 + 3 ^ 40 * 283420 * 2
def baseEnd_283420 : Nat := 129360610753232312574739

theorem tailTrace_283420 : CollatzResearch.WordTrace tailWord_283420 prefixEnd_283420 129360610753232312574739 := by
  unfold tailWord_283420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168588316612609563723857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6891451088816812751631809 5168588316612609563723857)
  ·
    refine ⟨3876441237459457172792893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5168588316612609563723857 3876441237459457172792893)
    ·
      refine ⟨1453665464047296439797335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3876441237459457172792893 1453665464047296439797335)
      ·
        refine ⟨2180498196070944659696003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453665464047296439797335 2180498196070944659696003)
        ·
          refine ⟨3270747294106416989544005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180498196070944659696003 3270747294106416989544005)
          ·
            refine ⟨613265117644953185539501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3270747294106416989544005 613265117644953185539501)
            ·
              refine ⟨229974419116857444577313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 613265117644953185539501 229974419116857444577313)
              ·
                refine ⟨172480814337643083432985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229974419116857444577313 172480814337643083432985)
                ·
                  refine ⟨129360610753232312574739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172480814337643083432985 129360610753232312574739)
                  ·
                    rfl

theorem cell20_283420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_283420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283420 prefixEnd_283420 := by exact prefixLift 283420
  have htrace : WordTrace (prefixWord ++ tailWord_283420) baseStart_283420 baseEnd_283420 := by
    simpa [prefixWord, tailWord_283420, baseEnd_283420] using wordTrace_append hprefix tailTrace_283420
  have hstable : (prefixWord ++ tailWord_283420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283420).length < 2 ^ (prefixWord ++ tailWord_283420).sum := by decide
  have hdescent : baseEnd_283420 < baseStart_283420 := by decide
  rcases family_descends (prefixWord ++ tailWord_283420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283424 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_283424 : Nat := 118140960795 + 283424 * 2 ^ 59
def prefixEnd_283424 : Nat := 4983230072969 + 3 ^ 40 * 283424 * 2
def baseEnd_283424 : Nat := 129362436462226076441389

theorem tailTrace_283424 : CollatzResearch.WordTrace tailWord_283424 prefixEnd_283424 129362436462226076441389 := by
  unfold tailWord_283424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168661262605363905296663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6891548350140485207062217 5168661262605363905296663)
  ·
    refine ⟨7752991893908045857944995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168661262605363905296663 7752991893908045857944995)
    ·
      refine ⟨11629487840862068786917493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7752991893908045857944995 11629487840862068786917493)
      ·
        refine ⟨1090264485080818948773515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11629487840862068786917493 1090264485080818948773515)
        ·
          refine ⟨1635396727621228423160273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090264485080818948773515 1635396727621228423160273)
          ·
            refine ⟨1226547545715921317370205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635396727621228423160273 1226547545715921317370205)
            ·
              refine ⟨459955329643470494013827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1226547545715921317370205 459955329643470494013827)
              ·
                refine ⟨689932994465205741020741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459955329643470494013827 689932994465205741020741)
                ·
                  refine ⟨129362436462226076441389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 689932994465205741020741 129362436462226076441389)
                  ·
                    rfl

theorem cell20_283424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_283424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283424 prefixEnd_283424 := by exact prefixLift 283424
  have htrace : WordTrace (prefixWord ++ tailWord_283424) baseStart_283424 baseEnd_283424 := by
    simpa [prefixWord, tailWord_283424, baseEnd_283424] using wordTrace_append hprefix tailTrace_283424
  have hstable : (prefixWord ++ tailWord_283424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283424).length < 2 ^ (prefixWord ++ tailWord_283424).sum := by decide
  have hdescent : baseEnd_283424 < baseStart_283424 := by decide
  rcases family_descends (prefixWord ++ tailWord_283424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283469 : List Nat := [1, 6, 1, 2, 10]
def baseStart_283469 : Nat := 118140960795 + 283469 * 2 ^ 59
def prefixEnd_283469 : Nat := 4983230072969 + 3 ^ 40 * 283469 * 2
def baseEnd_283469 : Nat := 1597320687511184196805

theorem tailTrace_283469 : CollatzResearch.WordTrace tailWord_283469 prefixEnd_283469 1597320687511184196805 := by
  unfold tailWord_283469
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338963810047700495981461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6892642540031800330654307 10338963810047700495981461)
  ·
    refine ⟨484638928595985960749131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10338963810047700495981461 484638928595985960749131)
    ·
      refine ⟨726958392893978941123697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484638928595985960749131 726958392893978941123697)
      ·
        refine ⟨545218794670484205842773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 726958392893978941123697 545218794670484205842773)
        ·
          refine ⟨1597320687511184196805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 545218794670484205842773 1597320687511184196805)
          ·
            rfl

theorem cell20_283469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 10].length) (baseStart_283469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283469 prefixEnd_283469 := by exact prefixLift 283469
  have htrace : WordTrace (prefixWord ++ tailWord_283469) baseStart_283469 baseEnd_283469 := by
    simpa [prefixWord, tailWord_283469, baseEnd_283469] using wordTrace_append hprefix tailTrace_283469
  have hstable : (prefixWord ++ tailWord_283469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283469).length < 2 ^ (prefixWord ++ tailWord_283469).sum := by decide
  have hdescent : baseEnd_283469 < baseStart_283469 := by decide
  rcases family_descends (prefixWord ++ tailWord_283469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283479 : List Nat := [1, 1, 3, 2, 4, 2, 1, 4, 2]
def baseStart_283479 : Nat := 118140960795 + 283479 * 2 ^ 59
def prefixEnd_283479 : Nat := 4983230072969 + 3 ^ 40 * 283479 * 2
def baseEnd_283479 : Nat := 129387539960890329607831

theorem tailTrace_283479 : CollatzResearch.WordTrace tailWord_283479 prefixEnd_283479 129387539960890329607831 := by
  unfold tailWord_283479
  simp only [CollatzResearch.WordTrace]
  refine ⟨10339328540011472203845491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6892885693340981469230327 10339328540011472203845491)
  ·
    refine ⟨15508992810017208305768237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10339328540011472203845491 15508992810017208305768237)
    ·
      refine ⟨5815872303756453114663089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15508992810017208305768237 5815872303756453114663089)
      ·
        refine ⟨4361904227817339835997317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5815872303756453114663089 4361904227817339835997317)
        ·
          refine ⟨817857042715751219249497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4361904227817339835997317 817857042715751219249497)
          ·
            refine ⟨613392782036813414437123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817857042715751219249497 613392782036813414437123)
            ·
              refine ⟨920089173055220121655685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613392782036813414437123 920089173055220121655685)
              ·
                refine ⟨172516719947853772810441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 920089173055220121655685 172516719947853772810441)
                ·
                  refine ⟨129387539960890329607831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172516719947853772810441 129387539960890329607831)
                  ·
                    rfl

theorem cell20_283479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4, 2].length) (baseStart_283479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283479 prefixEnd_283479 := by exact prefixLift 283479
  have htrace : WordTrace (prefixWord ++ tailWord_283479) baseStart_283479 baseEnd_283479 := by
    simpa [prefixWord, tailWord_283479, baseEnd_283479] using wordTrace_append hprefix tailTrace_283479
  have hstable : (prefixWord ++ tailWord_283479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283479).length < 2 ^ (prefixWord ++ tailWord_283479).sum := by decide
  have hdescent : baseEnd_283479 < baseStart_283479 := by decide
  rcases family_descends (prefixWord ++ tailWord_283479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283497 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_283497 : Nat := 118140960795 + 283497 * 2 ^ 59
def prefixEnd_283497 : Nat := 4983230072969 + 3 ^ 40 * 283497 * 2
def baseEnd_283497 : Nat := 129395755651362267007757

theorem tailTrace_283497 : CollatzResearch.WordTrace tailWord_283497 prefixEnd_283497 129395755651362267007757 := by
  unfold tailWord_283497
  simp only [CollatzResearch.WordTrace]
  refine ⟨10339985053946261278000745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6893323369297507518667163 10339985053946261278000745)
  ·
    refine ⟨7754988790459695958500559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10339985053946261278000745 7754988790459695958500559)
    ·
      refine ⟨11632483185689543937750839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7754988790459695958500559 11632483185689543937750839)
      ·
        refine ⟨17448724778534315906626259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11632483185689543937750839 17448724778534315906626259)
        ·
          refine ⟨26173087167801473859939389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17448724778534315906626259 26173087167801473859939389)
          ·
            refine ⟨9814907687925552697477271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26173087167801473859939389 9814907687925552697477271)
            ·
              refine ⟨14722361531888329046215907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9814907687925552697477271 14722361531888329046215907)
              ·
                refine ⟨22083542297832493569323861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14722361531888329046215907 22083542297832493569323861)
                ·
                  refine ⟨129395755651362267007757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22083542297832493569323861 129395755651362267007757)
                  ·
                    rfl

theorem cell20_283497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_283497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283497 prefixEnd_283497 := by exact prefixLift 283497
  have htrace : WordTrace (prefixWord ++ tailWord_283497) baseStart_283497 baseEnd_283497 := by
    simpa [prefixWord, tailWord_283497, baseEnd_283497] using wordTrace_append hprefix tailTrace_283497
  have hstable : (prefixWord ++ tailWord_283497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283497).length < 2 ^ (prefixWord ++ tailWord_283497).sum := by decide
  have hdescent : baseEnd_283497 < baseStart_283497 := by decide
  rcases family_descends (prefixWord ++ tailWord_283497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283552 : List Nat := [2, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_283552 : Nat := 118140960795 + 283552 * 2 ^ 59
def prefixEnd_283552 : Nat := 4983230072969 + 3 ^ 40 * 283552 * 2
def baseEnd_283552 : Nat := 129420859150026520174199

theorem tailTrace_283552 : CollatzResearch.WordTrace tailWord_283552 prefixEnd_283552 129420859150026520174199 := by
  unfold tailWord_283552
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170995534373502835626455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6894660712498003780835273 5170995534373502835626455)
  ·
    refine ⟨7756493301560254253439683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5170995534373502835626455 7756493301560254253439683)
    ·
      refine ⟨11634739952340381380159525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7756493301560254253439683 11634739952340381380159525)
      ·
        refine ⟨2181513741063821508779911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11634739952340381380159525 2181513741063821508779911)
        ·
          refine ⟨3272270611595732263169867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181513741063821508779911 3272270611595732263169867)
          ·
            refine ⟨4908405917393598394754801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272270611595732263169867 4908405917393598394754801)
            ·
              refine ⟨3681304438045198796066101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4908405917393598394754801 3681304438045198796066101)
              ·
                refine ⟨345122291066737387131197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3681304438045198796066101 345122291066737387131197)
                ·
                  refine ⟨129420859150026520174199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345122291066737387131197 129420859150026520174199)
                  ·
                    rfl

theorem cell20_283552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_283552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283552 prefixEnd_283552 := by exact prefixLift 283552
  have htrace : WordTrace (prefixWord ++ tailWord_283552) baseStart_283552 baseEnd_283552 := by
    simpa [prefixWord, tailWord_283552, baseEnd_283552] using wordTrace_append hprefix tailTrace_283552
  have hstable : (prefixWord ++ tailWord_283552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283552).length < 2 ^ (prefixWord ++ tailWord_283552).sum := by decide
  have hdescent : baseEnd_283552 < baseStart_283552 := by decide
  rcases family_descends (prefixWord ++ tailWord_283552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283659 : List Nat := [1, 1, 1, 1, 6, 4, 1, 5]
def baseStart_283659 : Nat := 118140960795 + 283659 * 2 ^ 59
def prefixEnd_283659 : Nat := 4983230072969 + 3 ^ 40 * 283659 * 2
def baseEnd_283659 : Nat := 43156565621869901202365

theorem tailTrace_283659 : CollatzResearch.WordTrace tailWord_283659 prefixEnd_283659 43156565621869901202365 := by
  unfold tailWord_283659
  simp only [CollatzResearch.WordTrace]
  refine ⟨10345893679359362945398031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6897262452906241963598687 10345893679359362945398031)
  ·
    refine ⟨15518840519039044418097047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10345893679359362945398031 15518840519039044418097047)
    ·
      refine ⟨23278260778558566627145571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15518840519039044418097047 23278260778558566627145571)
      ·
        refine ⟨34917391167837849940718357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23278260778558566627145571 34917391167837849940718357)
        ·
          refine ⟨1636752710992399215971173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34917391167837849940718357 1636752710992399215971173)
          ·
            refine ⟨306891133311074852994595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1636752710992399215971173 306891133311074852994595)
            ·
              refine ⟨460336699966612279491893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306891133311074852994595 460336699966612279491893)
              ·
                refine ⟨43156565621869901202365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 460336699966612279491893 43156565621869901202365)
                ·
                  rfl

theorem cell20_283659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_283659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283659 prefixEnd_283659 := by exact prefixLift 283659
  have htrace : WordTrace (prefixWord ++ tailWord_283659) baseStart_283659 baseEnd_283659 := by
    simpa [prefixWord, tailWord_283659, baseEnd_283659] using wordTrace_append hprefix tailTrace_283659
  have hstable : (prefixWord ++ tailWord_283659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283659).length < 2 ^ (prefixWord ++ tailWord_283659).sum := by decide
  have hdescent : baseEnd_283659 < baseStart_283659 := by decide
  rcases family_descends (prefixWord ++ tailWord_283659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283676 : List Nat := [2, 2, 3, 1, 4, 1, 3, 4]
def baseStart_283676 : Nat := 118140960795 + 283676 * 2 ^ 59
def prefixEnd_283676 : Nat := 4983230072969 + 3 ^ 40 * 283676 * 2
def baseEnd_283676 : Nat := 43159152042944400013453

theorem tailTrace_283676 : CollatzResearch.WordTrace tailWord_283676 prefixEnd_283676 43159152042944400013453 := by
  unfold tailWord_283676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173256860148887424383441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6897675813531849899177921 5173256860148887424383441)
  ·
    refine ⟨3879942645111665568287581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5173256860148887424383441 3879942645111665568287581)
    ·
      refine ⟨1454978491916874588107843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3879942645111665568287581 1454978491916874588107843)
      ·
        refine ⟨2182467737875311882161765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454978491916874588107843 2182467737875311882161765)
        ·
          refine ⟨409212700851620977905331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2182467737875311882161765 409212700851620977905331)
          ·
            refine ⟨613819051277431466857997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409212700851620977905331 613819051277431466857997)
            ·
              refine ⟨230182144229036800071749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 613819051277431466857997 230182144229036800071749)
              ·
                refine ⟨43159152042944400013453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230182144229036800071749 43159152042944400013453)
                ·
                  rfl

theorem cell20_283676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_283676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283676 prefixEnd_283676 := by exact prefixLift 283676
  have htrace : WordTrace (prefixWord ++ tailWord_283676) baseStart_283676 baseEnd_283676 := by
    simpa [prefixWord, tailWord_283676, baseEnd_283676] using wordTrace_append hprefix tailTrace_283676
  have hstable : (prefixWord ++ tailWord_283676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283676).length < 2 ^ (prefixWord ++ tailWord_283676).sum := by decide
  have hdescent : baseEnd_283676 < baseStart_283676 := by decide
  rcases family_descends (prefixWord ++ tailWord_283676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283700 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_283700 : Nat := 118140960795 + 283700 * 2 ^ 59
def prefixEnd_283700 : Nat := 4983230072969 + 3 ^ 40 * 283700 * 2
def baseEnd_283700 : Nat := 129488410382795783240261

theorem tailTrace_283700 : CollatzResearch.WordTrace tailWord_283700 prefixEnd_283700 129488410382795783240261 := by
  unfold tailWord_283700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173694536105413473820277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6898259381473884631760369 5173694536105413473820277)
  ·
    refine ⟨485033862759882513170651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5173694536105413473820277 485033862759882513170651)
    ·
      refine ⟨727550794139823769755977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485033862759882513170651 727550794139823769755977)
      ·
        refine ⟨545663095604867827316983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727550794139823769755977 545663095604867827316983)
        ·
          refine ⟨818494643407301740975475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545663095604867827316983 818494643407301740975475)
          ·
            refine ⟨1227741965110952611463213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818494643407301740975475 1227741965110952611463213)
            ·
              refine ⟨460403236916607229298705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1227741965110952611463213 460403236916607229298705)
              ·
                refine ⟨345302427687455421974029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460403236916607229298705 345302427687455421974029)
                ·
                  refine ⟨129488410382795783240261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345302427687455421974029 129488410382795783240261)
                  ·
                    rfl

theorem cell20_283700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_283700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283700 prefixEnd_283700 := by exact prefixLift 283700
  have htrace : WordTrace (prefixWord ++ tailWord_283700) baseStart_283700 baseEnd_283700 := by
    simpa [prefixWord, tailWord_283700, baseEnd_283700] using wordTrace_append hprefix tailTrace_283700
  have hstable : (prefixWord ++ tailWord_283700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283700).length < 2 ^ (prefixWord ++ tailWord_283700).sum := by decide
  have hdescent : baseEnd_283700 < baseStart_283700 := by decide
  rcases family_descends (prefixWord ++ tailWord_283700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283704 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_283704 : Nat := 118140960795 + 283704 * 2 ^ 59
def prefixEnd_283704 : Nat := 4983230072969 + 3 ^ 40 * 283704 * 2
def baseEnd_283704 : Nat := 129490236091789547106911

theorem tailTrace_283704 : CollatzResearch.WordTrace tailWord_283704 prefixEnd_283704 129490236091789547106911 := by
  unfold tailWord_283704
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173767482098167815393083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6898356642797557087190777 5173767482098167815393083)
  ·
    refine ⟨7760651223147251723089625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5173767482098167815393083 7760651223147251723089625)
    ·
      refine ⟨5820488417360438792317219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7760651223147251723089625 5820488417360438792317219)
      ·
        refine ⟨8730732626040658188475829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820488417360438792317219 8730732626040658188475829)
        ·
          refine ⟨818506183691311705169609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8730732626040658188475829 818506183691311705169609)
          ·
            refine ⟨613879637768483778877207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818506183691311705169609 613879637768483778877207)
            ·
              refine ⟨920819456652725668315811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613879637768483778877207 920819456652725668315811)
              ·
                refine ⟨1381229184979088502473717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920819456652725668315811 1381229184979088502473717)
                ·
                  refine ⟨129490236091789547106911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1381229184979088502473717 129490236091789547106911)
                  ·
                    rfl

theorem cell20_283704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_283704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283704 prefixEnd_283704 := by exact prefixLift 283704
  have htrace : WordTrace (prefixWord ++ tailWord_283704) baseStart_283704 baseEnd_283704 := by
    simpa [prefixWord, tailWord_283704, baseEnd_283704] using wordTrace_append hprefix tailTrace_283704
  have hstable : (prefixWord ++ tailWord_283704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283704).length < 2 ^ (prefixWord ++ tailWord_283704).sum := by decide
  have hdescent : baseEnd_283704 < baseStart_283704 := by decide
  rcases family_descends (prefixWord ++ tailWord_283704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283741 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 2]
def baseStart_283741 : Nat := 118140960795 + 283741 * 2 ^ 59
def prefixEnd_283741 : Nat := 4983230072969 + 3 ^ 40 * 283741 * 2
def baseEnd_283741 : Nat := 129507123899981862873427

theorem tailTrace_283741 : CollatzResearch.WordTrace tailWord_283741 prefixEnd_283741 129507123899981862873427 := by
  unfold tailWord_283741
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348884465062290949883077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6899256310041527299922051 10348884465062290949883077)
  ·
    refine ⟨1940415837199179553103077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10348884465062290949883077 1940415837199179553103077)
    ·
      refine ⟨363827969474846166206827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1940415837199179553103077 363827969474846166206827)
      ·
        refine ⟨545741954212269249310241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363827969474846166206827 545741954212269249310241)
        ·
          refine ⟨409306465659201936982681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545741954212269249310241 409306465659201936982681)
          ·
            refine ⟨306979849244401452737011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409306465659201936982681 306979849244401452737011)
            ·
              refine ⟨460469773866602179105517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306979849244401452737011 460469773866602179105517)
              ·
                refine ⟨172676165199975817164569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 460469773866602179105517 172676165199975817164569)
                ·
                  refine ⟨129507123899981862873427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172676165199975817164569 129507123899981862873427)
                  ·
                    rfl

theorem cell20_283741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_283741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283741 prefixEnd_283741 := by exact prefixLift 283741
  have htrace : WordTrace (prefixWord ++ tailWord_283741) baseStart_283741 baseEnd_283741 := by
    simpa [prefixWord, tailWord_283741, baseEnd_283741] using wordTrace_append hprefix tailTrace_283741
  have hstable : (prefixWord ++ tailWord_283741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283741).length < 2 ^ (prefixWord ++ tailWord_283741).sum := by decide
  have hdescent : baseEnd_283741 < baseStart_283741 := by decide
  rcases family_descends (prefixWord ++ tailWord_283741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283752 : List Nat := [2, 1, 4, 4, 1, 2, 6]
def baseStart_283752 : Nat := 118140960795 + 283752 * 2 ^ 59
def prefixEnd_283752 : Nat := 4983230072969 + 3 ^ 40 * 283752 * 2
def baseEnd_283752 : Nat := 14390238288857190389635

theorem tailTrace_283752 : CollatzResearch.WordTrace tailWord_283752 prefixEnd_283752 14390238288857190389635 := by
  unfold tailWord_283752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174642834011219914266755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6899523778681626552355673 5174642834011219914266755)
  ·
    refine ⟨7761964251016829871400133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174642834011219914266755 7761964251016829871400133)
    ·
      refine ⟨1455368297065655600887525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7761964251016829871400133 1455368297065655600887525)
      ·
        refine ⟨272881555699810425166411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1455368297065655600887525 272881555699810425166411)
        ·
          refine ⟨409322333549715637749617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272881555699810425166411 409322333549715637749617)
          ·
            refine ⟨306991750162286728312213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409322333549715637749617 306991750162286728312213)
            ·
              refine ⟨14390238288857190389635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 306991750162286728312213 14390238288857190389635)
              ·
                rfl

theorem cell20_283752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 6].length) (baseStart_283752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283752 prefixEnd_283752 := by exact prefixLift 283752
  have htrace : WordTrace (prefixWord ++ tailWord_283752) baseStart_283752 baseEnd_283752 := by
    simpa [prefixWord, tailWord_283752, baseEnd_283752] using wordTrace_append hprefix tailTrace_283752
  have hstable : (prefixWord ++ tailWord_283752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283752).length < 2 ^ (prefixWord ++ tailWord_283752).sum := by decide
  have hdescent : baseEnd_283752 < baseStart_283752 := by decide
  rcases family_descends (prefixWord ++ tailWord_283752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283869 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 3]
def baseStart_283869 : Nat := 118140960795 + 283869 * 2 ^ 59
def prefixEnd_283869 : Nat := 4983230072969 + 3 ^ 40 * 283869 * 2
def baseEnd_283869 : Nat := 129565546587782306606237

theorem tailTrace_283869 : CollatzResearch.WordTrace tailWord_283869 prefixEnd_283869 129565546587782306606237 := by
  unfold tailWord_283869
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353553008598568810542661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6902368672399045873695107 10353553008598568810542661)
  ·
    refine ⟨1941291189112231651976749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10353553008598568810542661 1941291189112231651976749)
    ·
      refine ⟨727984195917086869491281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1941291189112231651976749 727984195917086869491281)
      ·
        refine ⟨545988146937815152118461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727984195917086869491281 545988146937815152118461)
        ·
          refine ⟨204745555101680682044423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 545988146937815152118461 204745555101680682044423)
          ·
            refine ⟨307118332652521023066635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204745555101680682044423 307118332652521023066635)
            ·
              refine ⟨460677498978781534599953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307118332652521023066635 460677498978781534599953)
              ·
                refine ⟨345508124234086150949965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460677498978781534599953 345508124234086150949965)
                ·
                  refine ⟨129565546587782306606237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345508124234086150949965 129565546587782306606237)
                  ·
                    rfl

theorem cell20_283869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_283869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283869 prefixEnd_283869 := by exact prefixLift 283869
  have htrace : WordTrace (prefixWord ++ tailWord_283869) baseStart_283869 baseEnd_283869 := by
    simpa [prefixWord, tailWord_283869, baseEnd_283869] using wordTrace_append hprefix tailTrace_283869
  have hstable : (prefixWord ++ tailWord_283869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283869).length < 2 ^ (prefixWord ++ tailWord_283869).sum := by decide
  have hdescent : baseEnd_283869 < baseStart_283869 := by decide
  rcases family_descends (prefixWord ++ tailWord_283869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283873 : List Nat := [1, 2, 3, 1, 3, 4, 1, 2, 3]
def baseStart_283873 : Nat := 118140960795 + 283873 * 2 ^ 59
def prefixEnd_283873 : Nat := 4983230072969 + 3 ^ 40 * 283873 * 2
def baseEnd_283873 : Nat := 129567372296776070472887

theorem tailTrace_283873 : CollatzResearch.WordTrace tailWord_283873 prefixEnd_283873 129567372296776070472887 := by
  unfold tailWord_283873
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353698900584077493688273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6902465933722718329125515 10353698900584077493688273)
  ·
    refine ⟨7765274175438058120266205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10353698900584077493688273 7765274175438058120266205)
    ·
      refine ⟨2911977815789271795099827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7765274175438058120266205 2911977815789271795099827)
      ·
        refine ⟨4367966723683907692649741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911977815789271795099827 4367966723683907692649741)
        ·
          refine ⟨1637987521381465384743653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4367966723683907692649741 1637987521381465384743653)
          ·
            refine ⟨307122660259024759639435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1637987521381465384743653 307122660259024759639435)
            ·
              refine ⟨460683990388537139459153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307122660259024759639435 460683990388537139459153)
              ·
                refine ⟨345512992791402854594365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460683990388537139459153 345512992791402854594365)
                ·
                  refine ⟨129567372296776070472887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345512992791402854594365 129567372296776070472887)
                  ·
                    rfl

theorem cell20_283873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_283873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283873 prefixEnd_283873 := by exact prefixLift 283873
  have htrace : WordTrace (prefixWord ++ tailWord_283873) baseStart_283873 baseEnd_283873 := by
    simpa [prefixWord, tailWord_283873, baseEnd_283873] using wordTrace_append hprefix tailTrace_283873
  have hstable : (prefixWord ++ tailWord_283873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283873).length < 2 ^ (prefixWord ++ tailWord_283873).sum := by decide
  have hdescent : baseEnd_283873 < baseStart_283873 := by decide
  rcases family_descends (prefixWord ++ tailWord_283873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283880 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 2]
def baseStart_283880 : Nat := 118140960795 + 283880 * 2 ^ 59
def prefixEnd_283880 : Nat := 4983230072969 + 3 ^ 40 * 283880 * 2
def baseEnd_283880 : Nat := 129570567287515157239525

theorem tailTrace_283880 : CollatzResearch.WordTrace tailWord_283880 prefixEnd_283880 129570567287515157239525 := by
  unfold tailWord_283880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5176977105779358844596547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6902636141039145126128729 5176977105779358844596547)
  ·
    refine ⟨7765465658669038266894821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5176977105779358844596547 7765465658669038266894821)
    ·
      refine ⟨1456024811000444675042779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7765465658669038266894821 1456024811000444675042779)
      ·
        refine ⟨2184037216500667012564169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456024811000444675042779 2184037216500667012564169)
        ·
          refine ⟨1638027912375500259423127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184037216500667012564169 1638027912375500259423127)
          ·
            refine ⟨2457041868563250389134691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638027912375500259423127 2457041868563250389134691)
            ·
              refine ⟨3685562802844875583702037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457041868563250389134691 3685562802844875583702037)
              ·
                refine ⟨172760756383353542986033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3685562802844875583702037 172760756383353542986033)
                ·
                  refine ⟨129570567287515157239525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172760756383353542986033 129570567287515157239525)
                  ·
                    rfl

theorem cell20_283880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_283880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283880 prefixEnd_283880 := by exact prefixLift 283880
  have htrace : WordTrace (prefixWord ++ tailWord_283880) baseStart_283880 baseEnd_283880 := by
    simpa [prefixWord, tailWord_283880, baseEnd_283880] using wordTrace_append hprefix tailTrace_283880
  have hstable : (prefixWord ++ tailWord_283880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283880).length < 2 ^ (prefixWord ++ tailWord_283880).sum := by decide
  have hdescent : baseEnd_283880 < baseStart_283880 := by decide
  rcases family_descends (prefixWord ++ tailWord_283880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283890 : List Nat := [3, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_283890 : Nat := 118140960795 + 283890 * 2 ^ 59
def prefixEnd_283890 : Nat := 4983230072969 + 3 ^ 40 * 283890 * 2
def baseEnd_283890 : Nat := 129575131559999566906151

theorem tailTrace_283890 : CollatzResearch.WordTrace tailWord_283890 prefixEnd_283890 129575131559999566906151 := by
  unfold tailWord_283890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588579735380622349264281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6902879294348326264704749 2588579735380622349264281)
  ·
    refine ⟨1941434801535466761948211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2588579735380622349264281 1941434801535466761948211)
    ·
      refine ⟨2912152202303200142922317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941434801535466761948211 2912152202303200142922317)
      ·
        refine ⟨1092057075863700053595869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2912152202303200142922317 1092057075863700053595869)
        ·
          refine ⟨409521403448887520098451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1092057075863700053595869 409521403448887520098451)
          ·
            refine ⟨614282105173331280147677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409521403448887520098451 614282105173331280147677)
            ·
              refine ⟨230355789439999230055379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 614282105173331280147677 230355789439999230055379)
              ·
                refine ⟨345533684159998845083069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230355789439999230055379 345533684159998845083069)
                ·
                  refine ⟨129575131559999566906151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345533684159998845083069 129575131559999566906151)
                  ·
                    rfl

theorem cell20_283890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_283890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283890 prefixEnd_283890 := by exact prefixLift 283890
  have htrace : WordTrace (prefixWord ++ tailWord_283890) baseStart_283890 baseEnd_283890 := by
    simpa [prefixWord, tailWord_283890, baseEnd_283890] using wordTrace_append hprefix tailTrace_283890
  have hstable : (prefixWord ++ tailWord_283890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283890).length < 2 ^ (prefixWord ++ tailWord_283890).sum := by decide
  have hdescent : baseEnd_283890 < baseStart_283890 := by decide
  rcases family_descends (prefixWord ++ tailWord_283890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283915 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_283915 : Nat := 118140960795 + 283915 * 2 ^ 59
def prefixEnd_283915 : Nat := 4983230072969 + 3 ^ 40 * 283915 * 2
def baseEnd_283915 : Nat := 129586542241210591072715

theorem tailTrace_283915 : CollatzResearch.WordTrace tailWord_283915 prefixEnd_283915 129586542241210591072715 := by
  unfold tailWord_283915
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355230766431918666717199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6903487177621279111144799 10355230766431918666717199)
  ·
    refine ⟨15532846149647878000075799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10355230766431918666717199 15532846149647878000075799)
    ·
      refine ⟨23299269224471817000113699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15532846149647878000075799 23299269224471817000113699)
      ·
        refine ⟨34948903836707725500170549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23299269224471817000113699 34948903836707725500170549)
        ·
          refine ⟨3276459734691349265640989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34948903836707725500170549 3276459734691349265640989)
          ·
            refine ⟨1228672400509255974615371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3276459734691349265640989 1228672400509255974615371)
            ·
              refine ⟨1843008600763883961923057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228672400509255974615371 1843008600763883961923057)
              ·
                refine ⟨1382256450572912971442293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843008600763883961923057 1382256450572912971442293)
                ·
                  refine ⟨129586542241210591072715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382256450572912971442293 129586542241210591072715)
                  ·
                    rfl

theorem cell20_283915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_283915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283915 prefixEnd_283915 := by exact prefixLift 283915
  have htrace : WordTrace (prefixWord ++ tailWord_283915) baseStart_283915 baseEnd_283915 := by
    simpa [prefixWord, tailWord_283915, baseEnd_283915] using wordTrace_append hprefix tailTrace_283915
  have hstable : (prefixWord ++ tailWord_283915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283915).length < 2 ^ (prefixWord ++ tailWord_283915).sum := by decide
  have hdescent : baseEnd_283915 < baseStart_283915 := by decide
  rcases family_descends (prefixWord ++ tailWord_283915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283935 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 4]
def baseStart_283935 : Nat := 118140960795 + 283935 * 2 ^ 59
def prefixEnd_283935 : Nat := 4983230072969 + 3 ^ 40 * 283935 * 2
def baseEnd_283935 : Nat := 129595670786179410405967

theorem tailTrace_283935 : CollatzResearch.WordTrace tailWord_283935 prefixEnd_283935 129595670786179410405967 := by
  unfold tailWord_283935
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355960226359462082445259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6903973484239641388296839 10355960226359462082445259)
  ·
    refine ⟨15533940339539193123667889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10355960226359462082445259 15533940339539193123667889)
    ·
      refine ⟨11650455254654394842750917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15533940339539193123667889 11650455254654394842750917)
      ·
        refine ⟨2184460360247699033015797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11650455254654394842750917 2184460360247699033015797)
        ·
          refine ⟨204793158773221784345231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2184460360247699033015797 204793158773221784345231)
          ·
            refine ⟨307189738159832676517847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204793158773221784345231 307189738159832676517847)
            ·
              refine ⟨460784607239749014776771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307189738159832676517847 460784607239749014776771)
              ·
                refine ⟨691176910859623522165157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460784607239749014776771 691176910859623522165157)
                ·
                  refine ⟨129595670786179410405967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691176910859623522165157 129595670786179410405967)
                  ·
                    rfl

theorem cell20_283935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 4].length) (baseStart_283935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283935 prefixEnd_283935 := by exact prefixLift 283935
  have htrace : WordTrace (prefixWord ++ tailWord_283935) baseStart_283935 baseEnd_283935 := by
    simpa [prefixWord, tailWord_283935, baseEnd_283935] using wordTrace_append hprefix tailTrace_283935
  have hstable : (prefixWord ++ tailWord_283935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283935).length < 2 ^ (prefixWord ++ tailWord_283935).sum := by decide
  have hdescent : baseEnd_283935 < baseStart_283935 := by decide
  rcases family_descends (prefixWord ++ tailWord_283935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283939 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_283939 : Nat := 118140960795 + 283939 * 2 ^ 59
def prefixEnd_283939 : Nat := 4983230072969 + 3 ^ 40 * 283939 * 2
def baseEnd_283939 : Nat := 129597496495173174272617

theorem tailTrace_283939 : CollatzResearch.WordTrace tailWord_283939 prefixEnd_283939 129597496495173174272617 := by
  unfold tailWord_283939
  simp only [CollatzResearch.WordTrace]
  refine ⟨10356106118344970765590871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6904070745563313843727247 10356106118344970765590871)
  ·
    refine ⟨15534159177517456148386307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10356106118344970765590871 15534159177517456148386307)
    ·
      refine ⟨23301238766276184222579461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15534159177517456148386307 23301238766276184222579461)
      ·
        refine ⟨4368982268676784541733649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23301238766276184222579461 4368982268676784541733649)
        ·
          refine ⟨3276736701507588406300237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368982268676784541733649 3276736701507588406300237)
          ·
            refine ⟨1228776263065345652362589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3276736701507588406300237 1228776263065345652362589)
            ·
              refine ⟨460791098649504619635971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1228776263065345652362589 460791098649504619635971)
              ·
                refine ⟨691186647974256929453957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460791098649504619635971 691186647974256929453957)
                ·
                  refine ⟨129597496495173174272617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691186647974256929453957 129597496495173174272617)
                  ·
                    rfl

theorem cell20_283939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_283939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283939 prefixEnd_283939 := by exact prefixLift 283939
  have htrace : WordTrace (prefixWord ++ tailWord_283939) baseStart_283939 baseEnd_283939 := by
    simpa [prefixWord, tailWord_283939, baseEnd_283939] using wordTrace_append hprefix tailTrace_283939
  have hstable : (prefixWord ++ tailWord_283939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283939).length < 2 ^ (prefixWord ++ tailWord_283939).sum := by decide
  have hdescent : baseEnd_283939 < baseStart_283939 := by decide
  rcases family_descends (prefixWord ++ tailWord_283939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_283960 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_283960 : Nat := 118140960795 + 283960 * 2 ^ 59
def prefixEnd_283960 : Nat := 4983230072969 + 3 ^ 40 * 283960 * 2
def baseEnd_283960 : Nat := 129607081467390434572531

theorem tailTrace_283960 : CollatzResearch.WordTrace tailWord_283960 prefixEnd_283960 129607081467390434572531 := by
  unfold tailWord_283960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178436025634445676052667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6904581367512594234736889 5178436025634445676052667)
  ·
    refine ⟨7767654038451668514079001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178436025634445676052667 7767654038451668514079001)
    ·
      refine ⟨5825740528838751385559251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7767654038451668514079001 5825740528838751385559251)
      ·
        refine ⟨8738610793258127078338877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825740528838751385559251 8738610793258127078338877)
        ·
          refine ⟨3276979047471797654377079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8738610793258127078338877 3276979047471797654377079)
          ·
            refine ⟨4915468571207696481565619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276979047471797654377079 4915468571207696481565619)
            ·
              refine ⟨7373202856811544722348429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4915468571207696481565619 7373202856811544722348429)
              ·
                refine ⟨2764951071304329270880661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7373202856811544722348429 2764951071304329270880661)
                ·
                  refine ⟨129607081467390434572531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2764951071304329270880661 129607081467390434572531)
                  ·
                    rfl

theorem cell20_283960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_283960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_283960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_283960 prefixEnd_283960 := by exact prefixLift 283960
  have htrace : WordTrace (prefixWord ++ tailWord_283960) baseStart_283960 baseEnd_283960 := by
    simpa [prefixWord, tailWord_283960, baseEnd_283960] using wordTrace_append hprefix tailTrace_283960
  have hstable : (prefixWord ++ tailWord_283960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_283960).length < 2 ^ (prefixWord ++ tailWord_283960).sum := by decide
  have hdescent : baseEnd_283960 < baseStart_283960 := by decide
  rcases family_descends (prefixWord ++ tailWord_283960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284029 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_284029 : Nat := 118140960795 + 284029 * 2 ^ 59
def prefixEnd_284029 : Nat := 4983230072969 + 3 ^ 40 * 284029 * 2
def baseEnd_284029 : Nat := 129638574947532861272249

theorem tailTrace_284029 : CollatzResearch.WordTrace tailWord_284029 prefixEnd_284029 129638574947532861272249 := by
  unfold tailWord_284029
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359388688018916136367141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6906259125345944090911427 10359388688018916136367141)
  ·
    refine ⟨1942385379003546775568839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10359388688018916136367141 1942385379003546775568839)
    ·
      refine ⟨2913578068505320163353259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942385379003546775568839 2913578068505320163353259)
      ·
        refine ⟨4370367102757980245029889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913578068505320163353259 4370367102757980245029889)
        ·
          refine ⟨3277775327068485183772417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4370367102757980245029889 3277775327068485183772417)
          ·
            refine ⟨2458331495301363887829313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3277775327068485183772417 2458331495301363887829313)
            ·
              refine ⟨1843748621476022915871985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458331495301363887829313 1843748621476022915871985)
              ·
                refine ⟨1382811466107017186903989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1843748621476022915871985 1382811466107017186903989)
                ·
                  refine ⟨129638574947532861272249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1382811466107017186903989 129638574947532861272249)
                  ·
                    rfl

theorem cell20_284029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_284029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284029 prefixEnd_284029 := by exact prefixLift 284029
  have htrace : WordTrace (prefixWord ++ tailWord_284029) baseStart_284029 baseEnd_284029 := by
    simpa [prefixWord, tailWord_284029, baseEnd_284029] using wordTrace_append hprefix tailTrace_284029
  have hstable : (prefixWord ++ tailWord_284029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284029).length < 2 ^ (prefixWord ++ tailWord_284029).sum := by decide
  have hdescent : baseEnd_284029 < baseStart_284029 := by decide
  rcases family_descends (prefixWord ++ tailWord_284029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284043 : List Nat := [1, 1, 1, 1, 4, 3, 9]
def baseStart_284043 : Nat := 118140960795 + 284043 * 2 ^ 59
def prefixEnd_284043 : Nat := 4983230072969 + 3 ^ 40 * 284043 * 2
def baseEnd_284043 : Nat := 14404996103223448311725

theorem tailTrace_284043 : CollatzResearch.WordTrace tailWord_284043 prefixEnd_284043 14404996103223448311725 := by
  unfold tailWord_284043
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359899309968196527376783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6906599539978797684917855 10359899309968196527376783)
  ·
    refine ⟨15539848964952294791065175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10359899309968196527376783 15539848964952294791065175)
    ·
      refine ⟨23309773447428442186597763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15539848964952294791065175 23309773447428442186597763)
      ·
        refine ⟨34964660171142663279896645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23309773447428442186597763 34964660171142663279896645)
        ·
          refine ⟨6555873782089249364980621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34964660171142663279896645 6555873782089249364980621)
          ·
            refine ⟨2458452668283468511867733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6555873782089249364980621 2458452668283468511867733)
            ·
              refine ⟨14404996103223448311725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2458452668283468511867733 14404996103223448311725)
              ·
                rfl

theorem cell20_284043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_284043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284043 prefixEnd_284043 := by exact prefixLift 284043
  have htrace : WordTrace (prefixWord ++ tailWord_284043) baseStart_284043 baseEnd_284043 := by
    simpa [prefixWord, tailWord_284043, baseEnd_284043] using wordTrace_append hprefix tailTrace_284043
  have hstable : (prefixWord ++ tailWord_284043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284043).length < 2 ^ (prefixWord ++ tailWord_284043).sum := by decide
  have hdescent : baseEnd_284043 < baseStart_284043 := by decide
  rcases family_descends (prefixWord ++ tailWord_284043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284063 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 3]
def baseStart_284063 : Nat := 118140960795 + 284063 * 2 ^ 59
def prefixEnd_284063 : Nat := 4983230072969 + 3 ^ 40 * 284063 * 2
def baseEnd_284063 : Nat := 129654093473979854138777

theorem tailTrace_284063 : CollatzResearch.WordTrace tailWord_284063 prefixEnd_284063 129654093473979854138777 := by
  unfold tailWord_284063
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360628769895739943104843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6907085846597159962069895 10360628769895739943104843)
  ·
    refine ⟨15540943154843609914657265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10360628769895739943104843 15540943154843609914657265)
    ·
      refine ⟨11655707366132707435992949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15540943154843609914657265 11655707366132707435992949)
      ·
        refine ⟨1092722565574941322124339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11655707366132707435992949 1092722565574941322124339)
        ·
          refine ⟨1639083848362411983186509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092722565574941322124339 1639083848362411983186509)
          ·
            refine ⟨614656443135904493694941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1639083848362411983186509 614656443135904493694941)
            ·
              refine ⟨230496166175964185135603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 614656443135904493694941 230496166175964185135603)
              ·
                refine ⟨345744249263946277703405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230496166175964185135603 345744249263946277703405)
                ·
                  refine ⟨129654093473979854138777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345744249263946277703405 129654093473979854138777)
                  ·
                    rfl

theorem cell20_284063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_284063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284063 prefixEnd_284063 := by exact prefixLift 284063
  have htrace : WordTrace (prefixWord ++ tailWord_284063) baseStart_284063 baseEnd_284063 := by
    simpa [prefixWord, tailWord_284063, baseEnd_284063] using wordTrace_append hprefix tailTrace_284063
  have hstable : (prefixWord ++ tailWord_284063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284063).length < 2 ^ (prefixWord ++ tailWord_284063).sum := by decide
  have hdescent : baseEnd_284063 < baseStart_284063 := by decide
  rcases family_descends (prefixWord ++ tailWord_284063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284077 : List Nat := [1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_284077 : Nat := 118140960795 + 284077 * 2 ^ 59
def prefixEnd_284077 : Nat := 4983230072969 + 3 ^ 40 * 284077 * 2
def baseEnd_284077 : Nat := 43220161151819342557351

theorem tailTrace_284077 : CollatzResearch.WordTrace tailWord_284077 prefixEnd_284077 43220161151819342557351 := by
  unfold tailWord_284077
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361139391845020334114485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6907426261230013556076323 10361139391845020334114485)
  ·
    refine ⟨971356817985470656323233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10361139391845020334114485 971356817985470656323233)
    ·
      refine ⟨728517613489102992242425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 971356817985470656323233 728517613489102992242425)
      ·
        refine ⟨546388210116827244181819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728517613489102992242425 546388210116827244181819)
        ·
          refine ⟨819582315175240866272729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546388210116827244181819 819582315175240866272729)
          ·
            refine ⟨614686736381430649704547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819582315175240866272729 614686736381430649704547)
            ·
              refine ⟨922030104572145974556821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614686736381430649704547 922030104572145974556821)
              ·
                refine ⟨43220161151819342557351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 922030104572145974556821 43220161151819342557351)
                ·
                  rfl

theorem cell20_284077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_284077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284077 prefixEnd_284077 := by exact prefixLift 284077
  have htrace : WordTrace (prefixWord ++ tailWord_284077) baseStart_284077 baseEnd_284077 := by
    simpa [prefixWord, tailWord_284077, baseEnd_284077] using wordTrace_append hprefix tailTrace_284077
  have hstable : (prefixWord ++ tailWord_284077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284077).length < 2 ^ (prefixWord ++ tailWord_284077).sum := by decide
  have hdescent : baseEnd_284077 < baseStart_284077 := by decide
  rcases family_descends (prefixWord ++ tailWord_284077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284105 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_284105 : Nat := 118140960795 + 284105 * 2 ^ 59
def prefixEnd_284105 : Nat := 4983230072969 + 3 ^ 40 * 284105 * 2
def baseEnd_284105 : Nat := 129673263418414374738605

theorem tailTrace_284105 : CollatzResearch.WordTrace tailWord_284105 prefixEnd_284105 129673263418414374738605 := by
  unfold tailWord_284105
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362160635743581116133769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6908107090495720744089179 10362160635743581116133769)
  ·
    refine ⟨7771620476807685837100327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10362160635743581116133769 7771620476807685837100327)
    ·
      refine ⟨11657430715211528755650491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7771620476807685837100327 11657430715211528755650491)
      ·
        refine ⟨17486146072817293133475737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11657430715211528755650491 17486146072817293133475737)
        ·
          refine ⟨13114609554612969850106803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17486146072817293133475737 13114609554612969850106803)
          ·
            refine ⟨19671914331919454775160205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13114609554612969850106803 19671914331919454775160205)
            ·
              refine ⟨7376967874469795540685077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19671914331919454775160205 7376967874469795540685077)
              ·
                refine ⟨345795369115771665969613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7376967874469795540685077 345795369115771665969613)
                ·
                  refine ⟨129673263418414374738605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345795369115771665969613 129673263418414374738605)
                  ·
                    rfl

theorem cell20_284105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_284105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284105 prefixEnd_284105 := by exact prefixLift 284105
  have htrace : WordTrace (prefixWord ++ tailWord_284105) baseStart_284105 baseEnd_284105 := by
    simpa [prefixWord, tailWord_284105, baseEnd_284105] using wordTrace_append hprefix tailTrace_284105
  have hstable : (prefixWord ++ tailWord_284105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284105).length < 2 ^ (prefixWord ++ tailWord_284105).sum := by decide
  have hdescent : baseEnd_284105 < baseStart_284105 := by decide
  rcases family_descends (prefixWord ++ tailWord_284105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284108 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_284108 : Nat := 118140960795 + 284108 * 2 ^ 59
def prefixEnd_284108 : Nat := 4983230072969 + 3 ^ 40 * 284108 * 2
def baseEnd_284108 : Nat := 129674632700159697638593

theorem tailTrace_284108 : CollatzResearch.WordTrace tailWord_284108 prefixEnd_284108 129674632700159697638593 := by
  unfold tailWord_284108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181135027366356314246489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6908180036488475085661985 5181135027366356314246489)
  ·
    refine ⟨3885851270524767235684867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5181135027366356314246489 3885851270524767235684867)
    ·
      refine ⟨5828776905787150853527301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885851270524767235684867 5828776905787150853527301)
      ·
        refine ⟨1092895669835090785036369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5828776905787150853527301 1092895669835090785036369)
        ·
          refine ⟨819671752376318088777277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1092895669835090785036369 819671752376318088777277)
          ·
            refine ⟨307376907141119283291479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 819671752376318088777277 307376907141119283291479)
            ·
              refine ⟨461065360711678924937219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307376907141119283291479 461065360711678924937219)
              ·
                refine ⟨691598041067518387405829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461065360711678924937219 691598041067518387405829)
                ·
                  refine ⟨129674632700159697638593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691598041067518387405829 129674632700159697638593)
                  ·
                    rfl

theorem cell20_284108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_284108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284108 prefixEnd_284108 := by exact prefixLift 284108
  have htrace : WordTrace (prefixWord ++ tailWord_284108) baseStart_284108 baseEnd_284108 := by
    simpa [prefixWord, tailWord_284108, baseEnd_284108] using wordTrace_append hprefix tailTrace_284108
  have hstable : (prefixWord ++ tailWord_284108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284108).length < 2 ^ (prefixWord ++ tailWord_284108).sum := by decide
  have hdescent : baseEnd_284108 < baseStart_284108 := by decide
  rcases family_descends (prefixWord ++ tailWord_284108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284118 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_284118 : Nat := 118140960795 + 284118 * 2 ^ 59
def prefixEnd_284118 : Nat := 4983230072969 + 3 ^ 40 * 284118 * 2
def baseEnd_284118 : Nat := 129679196972644107305219

theorem tailTrace_284118 : CollatzResearch.WordTrace tailWord_284118 prefixEnd_284118 129679196972644107305219 := by
  unfold tailWord_284118
  simp only [CollatzResearch.WordTrace]
  refine ⟨647664674043530271022313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6908423189797656224238005 647664674043530271022313)
  ·
    refine ⟨485748505532647703266735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 647664674043530271022313 485748505532647703266735)
    ·
      refine ⟨728622758298971554900103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485748505532647703266735 728622758298971554900103)
      ·
        refine ⟨1092934137448457332350155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728622758298971554900103 1092934137448457332350155)
        ·
          refine ⟨1639401206172685998525233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1092934137448457332350155 1639401206172685998525233)
          ·
            refine ⟨1229550904629514498893925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639401206172685998525233 1229550904629514498893925)
            ·
              refine ⟨230540794618033968542611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1229550904629514498893925 230540794618033968542611)
              ·
                refine ⟨345811191927050952813917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230540794618033968542611 345811191927050952813917)
                ·
                  refine ⟨129679196972644107305219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345811191927050952813917 129679196972644107305219)
                  ·
                    rfl

theorem cell20_284118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_284118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284118 prefixEnd_284118 := by exact prefixLift 284118
  have htrace : WordTrace (prefixWord ++ tailWord_284118) baseStart_284118 baseEnd_284118 := by
    simpa [prefixWord, tailWord_284118, baseEnd_284118] using wordTrace_append hprefix tailTrace_284118
  have hstable : (prefixWord ++ tailWord_284118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284118).length < 2 ^ (prefixWord ++ tailWord_284118).sum := by decide
  have hdescent : baseEnd_284118 < baseStart_284118 := by decide
  rcases family_descends (prefixWord ++ tailWord_284118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284122 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_284122 : Nat := 118140960795 + 284122 * 2 ^ 59
def prefixEnd_284122 : Nat := 4983230072969 + 3 ^ 40 * 284122 * 2
def baseEnd_284122 : Nat := 129681022681637871171869

theorem tailTrace_284122 : CollatzResearch.WordTrace tailWord_284122 prefixEnd_284122 129681022681637871171869 := by
  unfold tailWord_284122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590695169170498254875655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6908520451121328679668413 2590695169170498254875655)
  ·
    refine ⟨3886042753755747382313483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590695169170498254875655 3886042753755747382313483)
    ·
      refine ⟨5829064130633621073470225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886042753755747382313483 5829064130633621073470225)
      ·
        refine ⟨4371798097975215805102669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5829064130633621073470225 4371798097975215805102669)
        ·
          refine ⟨1639424286740705926913501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4371798097975215805102669 1639424286740705926913501)
          ·
            refine ⟨614784107527764722592563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1639424286740705926913501 614784107527764722592563)
            ·
              refine ⟨922176161291647083888845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614784107527764722592563 922176161291647083888845)
              ·
                refine ⟨345816060484367656458317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922176161291647083888845 345816060484367656458317)
                ·
                  refine ⟨129681022681637871171869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345816060484367656458317 129681022681637871171869)
                  ·
                    rfl

theorem cell20_284122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_284122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284122 prefixEnd_284122 := by exact prefixLift 284122
  have htrace : WordTrace (prefixWord ++ tailWord_284122) baseStart_284122 baseEnd_284122 := by
    simpa [prefixWord, tailWord_284122, baseEnd_284122] using wordTrace_append hprefix tailTrace_284122
  have hstable : (prefixWord ++ tailWord_284122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284122).length < 2 ^ (prefixWord ++ tailWord_284122).sum := by decide
  have hdescent : baseEnd_284122 < baseStart_284122 := by decide
  rcases family_descends (prefixWord ++ tailWord_284122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284157 : List Nat := [1, 4, 1, 1, 1, 12]
def baseStart_284157 : Nat := 118140960795 + 284157 * 2 ^ 59
def prefixEnd_284157 : Nat := 4983230072969 + 3 ^ 40 * 284157 * 2
def baseEnd_284157 : Nat := 4803592505012344629817

theorem tailTrace_284157 : CollatzResearch.WordTrace tailWord_284157 prefixEnd_284157 4803592505012344629817 := by
  unfold tailWord_284157
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364057231555193997026725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6909371487703462664684483 10364057231555193997026725)
  ·
    refine ⟨1943260730916598874442511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10364057231555193997026725 1943260730916598874442511)
    ·
      refine ⟨2914891096374898311663767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943260730916598874442511 2914891096374898311663767)
      ·
        refine ⟨4372336644562347467495651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914891096374898311663767 4372336644562347467495651)
        ·
          refine ⟨6558504966843521201243477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372336644562347467495651 6558504966843521201243477)
          ·
            refine ⟨4803592505012344629817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6558504966843521201243477 4803592505012344629817)
            ·
              rfl

theorem cell20_284157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 12].length) (baseStart_284157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284157 prefixEnd_284157 := by exact prefixLift 284157
  have htrace : WordTrace (prefixWord ++ tailWord_284157) baseStart_284157 baseEnd_284157 := by
    simpa [prefixWord, tailWord_284157, baseEnd_284157] using wordTrace_append hprefix tailTrace_284157
  have hstable : (prefixWord ++ tailWord_284157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284157).length < 2 ^ (prefixWord ++ tailWord_284157).sum := by decide
  have hdescent : baseEnd_284157 < baseStart_284157 := by decide
  rcases family_descends (prefixWord ++ tailWord_284157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284166 : List Nat := [6, 2, 1, 1, 2, 2, 1, 5]
def baseStart_284166 : Nat := 118140960795 + 284166 * 2 ^ 59
def prefixEnd_284166 : Nat := 4983230072969 + 3 ^ 40 * 284166 * 2
def baseEnd_284166 : Nat := 43233701826856424568341

theorem tailTrace_284166 : CollatzResearch.WordTrace tailWord_284166 prefixEnd_284166 43233701826856424568341 := by
  unfold tailWord_284166
  simp only [CollatzResearch.WordTrace]
  refine ⟨323887046516330891690761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6909590325681725689402901 323887046516330891690761)
  ·
    refine ⟨242915284887248168768071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 323887046516330891690761 242915284887248168768071)
    ·
      refine ⟨364372927330872253152107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242915284887248168768071 364372927330872253152107)
      ·
        refine ⟨546559390996308379728161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364372927330872253152107 546559390996308379728161)
        ·
          refine ⟨409919543247231284796121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 546559390996308379728161 409919543247231284796121)
          ·
            refine ⟨307439657435423463597091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409919543247231284796121 307439657435423463597091)
            ·
              refine ⟨461159486153135195395637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307439657435423463597091 461159486153135195395637)
              ·
                refine ⟨43233701826856424568341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461159486153135195395637 43233701826856424568341)
                ·
                  rfl

theorem cell20_284166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_284166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284166 prefixEnd_284166 := by exact prefixLift 284166
  have htrace : WordTrace (prefixWord ++ tailWord_284166) baseStart_284166 baseEnd_284166 := by
    simpa [prefixWord, tailWord_284166, baseEnd_284166] using wordTrace_append hprefix tailTrace_284166
  have hstable : (prefixWord ++ tailWord_284166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284166).length < 2 ^ (prefixWord ++ tailWord_284166).sum := by decide
  have hdescent : baseEnd_284166 < baseStart_284166 := by decide
  rcases family_descends (prefixWord ++ tailWord_284166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284260 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 2]
def baseStart_284260 : Nat := 118140960795 + 284260 * 2 ^ 59
def prefixEnd_284260 : Nat := 4983230072969 + 3 ^ 40 * 284260 * 2
def baseEnd_284260 : Nat := 129744009641922724571305

theorem tailTrace_284260 : CollatzResearch.WordTrace tailWord_284260 prefixEnd_284260 129744009641922724571305 := by
  unfold tailWord_284260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183906975091021294013117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6911875966788028392017489 5183906975091021294013117)
  ·
    refine ⟨1943965115659132985254919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5183906975091021294013117 1943965115659132985254919)
    ·
      refine ⟨2915947673488699477882379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943965115659132985254919 2915947673488699477882379)
      ·
        refine ⟨4373921510233049216823569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2915947673488699477882379 4373921510233049216823569)
        ·
          refine ⟨3280441132674786912617677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4373921510233049216823569 3280441132674786912617677)
          ·
            refine ⟨1230165424753045092231629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3280441132674786912617677 1230165424753045092231629)
            ·
              refine ⟨461312034282391909586861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230165424753045092231629 461312034282391909586861)
              ·
                refine ⟨172992012855896966095073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 461312034282391909586861 172992012855896966095073)
                ·
                  refine ⟨129744009641922724571305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172992012855896966095073 129744009641922724571305)
                  ·
                    rfl

theorem cell20_284260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_284260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284260 prefixEnd_284260 := by exact prefixLift 284260
  have htrace : WordTrace (prefixWord ++ tailWord_284260) baseStart_284260 baseEnd_284260 := by
    simpa [prefixWord, tailWord_284260, baseEnd_284260] using wordTrace_append hprefix tailTrace_284260
  have hstable : (prefixWord ++ tailWord_284260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284260).length < 2 ^ (prefixWord ++ tailWord_284260).sum := by decide
  have hdescent : baseEnd_284260 < baseStart_284260 := by decide
  rcases family_descends (prefixWord ++ tailWord_284260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284328 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 2]
def baseStart_284328 : Nat := 118140960795 + 284328 * 2 ^ 59
def prefixEnd_284328 : Nat := 4983230072969 + 3 ^ 40 * 284328 * 2
def baseEnd_284328 : Nat := 129775046694816710304361

theorem tailTrace_284328 : CollatzResearch.WordTrace tailWord_284328 prefixEnd_284328 129775046694816710304361 := by
  unfold tailWord_284328
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185147056967845100750819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6913529409290460134334425 5185147056967845100750819)
  ·
    refine ⟨7777720585451767651126229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5185147056967845100750819 7777720585451767651126229)
    ·
      refine ⟨182290326221525804323271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7777720585451767651126229 182290326221525804323271)
      ·
        refine ⟨273435489332288706484907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182290326221525804323271 273435489332288706484907)
        ·
          refine ⟨410153233998433059727361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273435489332288706484907 410153233998433059727361)
          ·
            refine ⟨307614925498824794795521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410153233998433059727361 307614925498824794795521)
            ·
              refine ⟨230711194124118596096641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307614925498824794795521 230711194124118596096641)
              ·
                refine ⟨173033395593088947072481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230711194124118596096641 173033395593088947072481)
                ·
                  refine ⟨129775046694816710304361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173033395593088947072481 129775046694816710304361)
                  ·
                    rfl

theorem cell20_284328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 2].length) (baseStart_284328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284328 prefixEnd_284328 := by exact prefixLift 284328
  have htrace : WordTrace (prefixWord ++ tailWord_284328) baseStart_284328 baseEnd_284328 := by
    simpa [prefixWord, tailWord_284328, baseEnd_284328] using wordTrace_append hprefix tailTrace_284328
  have hstable : (prefixWord ++ tailWord_284328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284328).length < 2 ^ (prefixWord ++ tailWord_284328).sum := by decide
  have hdescent : baseEnd_284328 < baseStart_284328 := by decide
  rcases family_descends (prefixWord ++ tailWord_284328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284336 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 2]
def baseStart_284336 : Nat := 118140960795 + 284336 * 2 ^ 59
def prefixEnd_284336 : Nat := 4983230072969 + 3 ^ 40 * 284336 * 2
def baseEnd_284336 : Nat := 129778698112804238037661

theorem tailTrace_284336 : CollatzResearch.WordTrace tailWord_284336 prefixEnd_284336 129778698112804238037661 := by
  unfold tailWord_284336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5185292948953353783896431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6913723931937805045195241 5185292948953353783896431)
  ·
    refine ⟨7777939423430030675844647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5185292948953353783896431 7777939423430030675844647)
    ·
      refine ⟨11666909135145046013766971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7777939423430030675844647 11666909135145046013766971)
      ·
        refine ⟨17500363702717569020650457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11666909135145046013766971 17500363702717569020650457)
        ·
          refine ⟨13125272777038176765487843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17500363702717569020650457 13125272777038176765487843)
          ·
            refine ⟨19687909165557265148231765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13125272777038176765487843 19687909165557265148231765)
            ·
              refine ⟨230717685533874200955841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 19687909165557265148231765 230717685533874200955841)
              ·
                refine ⟨173038264150405650716881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230717685533874200955841 173038264150405650716881)
                ·
                  refine ⟨129778698112804238037661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173038264150405650716881 129778698112804238037661)
                  ·
                    rfl

theorem cell20_284336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_284336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284336 prefixEnd_284336 := by exact prefixLift 284336
  have htrace : WordTrace (prefixWord ++ tailWord_284336) baseStart_284336 baseEnd_284336 := by
    simpa [prefixWord, tailWord_284336, baseEnd_284336] using wordTrace_append hprefix tailTrace_284336
  have hstable : (prefixWord ++ tailWord_284336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284336).length < 2 ^ (prefixWord ++ tailWord_284336).sum := by decide
  have hdescent : baseEnd_284336 < baseStart_284336 := by decide
  rcases family_descends (prefixWord ++ tailWord_284336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284350 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_284350 : Nat := 118140960795 + 284350 * 2 ^ 59
def prefixEnd_284350 : Nat := 4983230072969 + 3 ^ 40 * 284350 * 2
def baseEnd_284350 : Nat := 129785088094282411570937

theorem tailTrace_284350 : CollatzResearch.WordTrace tailWord_284350 prefixEnd_284350 129785088094282411570937 := by
  unfold tailWord_284350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296387064981998494850313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6914064346570658639201669 1296387064981998494850313)
  ·
    refine ⟨972290298736498871137735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1296387064981998494850313 972290298736498871137735)
    ·
      refine ⟨1458435448104748306706603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972290298736498871137735 1458435448104748306706603)
      ·
        refine ⟨2187653172157122460059905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458435448104748306706603 2187653172157122460059905)
        ·
          refine ⟨1640739879117841845044929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2187653172157122460059905 1640739879117841845044929)
          ·
            refine ⟨1230554909338381383783697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1640739879117841845044929 1230554909338381383783697)
            ·
              refine ⟨922916182003786037837773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230554909338381383783697 922916182003786037837773)
              ·
                refine ⟨346093568251419764189165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922916182003786037837773 346093568251419764189165)
                ·
                  refine ⟨129785088094282411570937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346093568251419764189165 129785088094282411570937)
                  ·
                    rfl

theorem cell20_284350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_284350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284350 prefixEnd_284350 := by exact prefixLift 284350
  have htrace : WordTrace (prefixWord ++ tailWord_284350) baseStart_284350 baseEnd_284350 := by
    simpa [prefixWord, tailWord_284350, baseEnd_284350] using wordTrace_append hprefix tailTrace_284350
  have hstable : (prefixWord ++ tailWord_284350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284350).length < 2 ^ (prefixWord ++ tailWord_284350).sum := by decide
  have hdescent : baseEnd_284350 < baseStart_284350 := by decide
  rcases family_descends (prefixWord ++ tailWord_284350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284381 : List Nat := [1, 4, 3, 3, 1, 1, 7]
def baseStart_284381 : Nat := 118140960795 + 284381 * 2 ^ 59
def prefixEnd_284381 : Nat := 4983230072969 + 3 ^ 40 * 284381 * 2
def baseEnd_284381 : Nat := 14422137482109342393053

theorem tailTrace_284381 : CollatzResearch.WordTrace tailWord_284381 prefixEnd_284381 14422137482109342393053 := by
  unfold tailWord_284381
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372227182743680253180997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6914818121829120168787331 10372227182743680253180997)
  ·
    refine ⟨1944792596764440047471437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10372227182743680253180997 1944792596764440047471437)
    ·
      refine ⟨729297223786665017801789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1944792596764440047471437 729297223786665017801789)
      ·
        refine ⟨273486458919999381675671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 729297223786665017801789 273486458919999381675671)
        ·
          refine ⟨410229688379999072513507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273486458919999381675671 410229688379999072513507)
          ·
            refine ⟨615344532569998608770261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410229688379999072513507 615344532569998608770261)
            ·
              refine ⟨14422137482109342393053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 615344532569998608770261 14422137482109342393053)
              ·
                rfl

theorem cell20_284381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_284381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284381 prefixEnd_284381 := by exact prefixLift 284381
  have htrace : WordTrace (prefixWord ++ tailWord_284381) baseStart_284381 baseEnd_284381 := by
    simpa [prefixWord, tailWord_284381, baseEnd_284381] using wordTrace_append hprefix tailTrace_284381
  have hstable : (prefixWord ++ tailWord_284381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284381).length < 2 ^ (prefixWord ++ tailWord_284381).sum := by decide
  have hdescent : baseEnd_284381 < baseStart_284381 := by decide
  rcases family_descends (prefixWord ++ tailWord_284381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284395 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 2]
def baseStart_284395 : Nat := 118140960795 + 284395 * 2 ^ 59
def prefixEnd_284395 : Nat := 4983230072969 + 3 ^ 40 * 284395 * 2
def baseEnd_284395 : Nat := 129805627320462255070753

theorem tailTrace_284395 : CollatzResearch.WordTrace tailWord_284395 prefixEnd_284395 129805627320462255070753 := by
  unfold tailWord_284395
  simp only [CollatzResearch.WordTrace]
  refine ⟨10372737804692960644190639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6915158536461973762793759 10372737804692960644190639)
  ·
    refine ⟨15559106707039440966285959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10372737804692960644190639 15559106707039440966285959)
    ·
      refine ⟨23338660060559161449428939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15559106707039440966285959 23338660060559161449428939)
      ·
        refine ⟨35007990090838742174143409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23338660060559161449428939 35007990090838742174143409)
        ·
          refine ⟨26255992568129056630607557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35007990090838742174143409 26255992568129056630607557)
          ·
            refine ⟨4922998606524198118238917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26255992568129056630607557 4922998606524198118238917)
            ·
              refine ⟨923062238723287147169797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4922998606524198118238917 923062238723287147169797)
              ·
                refine ⟨173074169760616340094337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 923062238723287147169797 173074169760616340094337)
                ·
                  refine ⟨129805627320462255070753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173074169760616340094337 129805627320462255070753)
                  ·
                    rfl

theorem cell20_284395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 2].length) (baseStart_284395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284395 prefixEnd_284395 := by exact prefixLift 284395
  have htrace : WordTrace (prefixWord ++ tailWord_284395) baseStart_284395 baseEnd_284395 := by
    simpa [prefixWord, tailWord_284395, baseEnd_284395] using wordTrace_append hprefix tailTrace_284395
  have hstable : (prefixWord ++ tailWord_284395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284395).length < 2 ^ (prefixWord ++ tailWord_284395).sum := by decide
  have hdescent : baseEnd_284395 < baseStart_284395 := by decide
  rcases family_descends (prefixWord ++ tailWord_284395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284446 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_284446 : Nat := 118140960795 + 284446 * 2 ^ 59
def prefixEnd_284446 : Nat := 4983230072969 + 3 ^ 40 * 284446 * 2
def baseEnd_284446 : Nat := 129828905110132744370545

theorem tailTrace_284446 : CollatzResearch.WordTrace tailWord_284446 prefixEnd_284446 129828905110132744370545 := by
  unfold tailWord_284446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296824740938524544287149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6916398618338797569531461 1296824740938524544287149)
  ·
    refine ⟨486309277851946704107681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1296824740938524544287149 486309277851946704107681)
    ·
      refine ⟨364731958388960028080761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486309277851946704107681 364731958388960028080761)
      ·
        refine ⟨273548968791720021060571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 364731958388960028080761 273548968791720021060571)
        ·
          refine ⟨410323453187580031590857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273548968791720021060571 410323453187580031590857)
          ·
            refine ⟨307742589890685023693143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410323453187580031590857 307742589890685023693143)
            ·
              refine ⟨461613884836027535539715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307742589890685023693143 461613884836027535539715)
              ·
                refine ⟨692420827254041303309573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461613884836027535539715 692420827254041303309573)
                ·
                  refine ⟨129828905110132744370545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 692420827254041303309573 129828905110132744370545)
                  ·
                    rfl

theorem cell20_284446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_284446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284446 prefixEnd_284446 := by exact prefixLift 284446
  have htrace : WordTrace (prefixWord ++ tailWord_284446) baseStart_284446 baseEnd_284446 := by
    simpa [prefixWord, tailWord_284446, baseEnd_284446] using wordTrace_append hprefix tailTrace_284446
  have hstable : (prefixWord ++ tailWord_284446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284446).length < 2 ^ (prefixWord ++ tailWord_284446).sum := by decide
  have hdescent : baseEnd_284446 < baseStart_284446 := by decide
  rcases family_descends (prefixWord ++ tailWord_284446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284447 : List Nat := [1, 1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_284447 : Nat := 118140960795 + 284447 * 2 ^ 59
def prefixEnd_284447 : Nat := 4983230072969 + 3 ^ 40 * 284447 * 2
def baseEnd_284447 : Nat := 129829361537381185337207

theorem tailTrace_284447 : CollatzResearch.WordTrace tailWord_284447 prefixEnd_284447 129829361537381185337207 := by
  unfold tailWord_284447
  simp only [CollatzResearch.WordTrace]
  refine ⟨10374634400504573525083595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6916422933669715683389063 10374634400504573525083595)
  ·
    refine ⟨15561951600756860287625393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10374634400504573525083595 15561951600756860287625393)
    ·
      refine ⟨11671463700567645215719045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15561951600756860287625393 11671463700567645215719045)
      ·
        refine ⟨2188399443856433477947321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11671463700567645215719045 2188399443856433477947321)
        ·
          refine ⟨1641299582892325108460491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188399443856433477947321 1641299582892325108460491)
          ·
            refine ⟨2461949374338487662690737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641299582892325108460491 2461949374338487662690737)
            ·
              refine ⟨1846462030753865747018053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461949374338487662690737 1846462030753865747018053)
              ·
                refine ⟨346211630766349827565885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1846462030753865747018053 346211630766349827565885)
                ·
                  refine ⟨129829361537381185337207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346211630766349827565885 129829361537381185337207)
                  ·
                    rfl

theorem cell20_284447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_284447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284447 prefixEnd_284447 := by exact prefixLift 284447
  have htrace : WordTrace (prefixWord ++ tailWord_284447) baseStart_284447 baseEnd_284447 := by
    simpa [prefixWord, tailWord_284447, baseEnd_284447] using wordTrace_append hprefix tailTrace_284447
  have hstable : (prefixWord ++ tailWord_284447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284447).length < 2 ^ (prefixWord ++ tailWord_284447).sum := by decide
  have hdescent : baseEnd_284447 < baseStart_284447 := by decide
  rcases family_descends (prefixWord ++ tailWord_284447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284478 : List Nat := [4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_284478 : Nat := 118140960795 + 284478 * 2 ^ 59
def prefixEnd_284478 : Nat := 4983230072969 + 3 ^ 40 * 284478 * 2
def baseEnd_284478 : Nat := 43281170260694285101249

theorem tailTrace_284478 : CollatzResearch.WordTrace tailWord_284478 prefixEnd_284478 43281170260694285101249 := by
  unfold tailWord_284478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1296970632924033227432761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6917176708928177212974725 1296970632924033227432761)
  ·
    refine ⟨972727974693024920574571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1296970632924033227432761 972727974693024920574571)
    ·
      refine ⟨1459091962039537380861857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972727974693024920574571 1459091962039537380861857)
      ·
        refine ⟨1094318971529653035646393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1459091962039537380861857 1094318971529653035646393)
        ·
          refine ⟨820739228647239776734795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094318971529653035646393 820739228647239776734795)
          ·
            refine ⟨1231108842970859665102193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820739228647239776734795 1231108842970859665102193)
            ·
              refine ⟨923331632228144748826645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231108842970859665102193 923331632228144748826645)
              ·
                refine ⟨43281170260694285101249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 923331632228144748826645 43281170260694285101249)
                ·
                  rfl

theorem cell20_284478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_284478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284478 prefixEnd_284478 := by exact prefixLift 284478
  have htrace : WordTrace (prefixWord ++ tailWord_284478) baseStart_284478 baseEnd_284478 := by
    simpa [prefixWord, tailWord_284478, baseEnd_284478] using wordTrace_append hprefix tailTrace_284478
  have hstable : (prefixWord ++ tailWord_284478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284478).length < 2 ^ (prefixWord ++ tailWord_284478).sum := by decide
  have hdescent : baseEnd_284478 < baseStart_284478 := by decide
  rcases family_descends (prefixWord ++ tailWord_284478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284544 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_284544 : Nat := 118140960795 + 284544 * 2 ^ 59
def prefixEnd_284544 : Nat := 4983230072969 + 3 ^ 40 * 284544 * 2
def baseEnd_284544 : Nat := 129873634980479959103477

theorem tailTrace_284544 : CollatzResearch.WordTrace tailWord_284544 prefixEnd_284544 129873634980479959103477 := by
  unfold tailWord_284544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189086140576579545682343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6918781520768772727576457 5189086140576579545682343)
  ·
    refine ⟨7783629210864869318523515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5189086140576579545682343 7783629210864869318523515)
    ·
      refine ⟨11675443816297303977785273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7783629210864869318523515 11675443816297303977785273)
      ·
        refine ⟨8756582862222977983338955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11675443816297303977785273 8756582862222977983338955)
        ·
          refine ⟨13134874293334466975008433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756582862222977983338955 13134874293334466975008433)
          ·
            refine ⟨9851155720000850231256325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13134874293334466975008433 9851155720000850231256325)
            ·
              refine ⟨1847091697500159418360561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9851155720000850231256325 1847091697500159418360561)
              ·
                refine ⟨1385318773125119563770421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1847091697500159418360561 1385318773125119563770421)
                ·
                  refine ⟨129873634980479959103477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1385318773125119563770421 129873634980479959103477)
                  ·
                    rfl

theorem cell20_284544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_284544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284544 prefixEnd_284544 := by exact prefixLift 284544
  have htrace : WordTrace (prefixWord ++ tailWord_284544) baseStart_284544 baseEnd_284544 := by
    simpa [prefixWord, tailWord_284544, baseEnd_284544] using wordTrace_append hprefix tailTrace_284544
  have hstable : (prefixWord ++ tailWord_284544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284544).length < 2 ^ (prefixWord ++ tailWord_284544).sum := by decide
  have hdescent : baseEnd_284544 < baseStart_284544 := by decide
  rcases family_descends (prefixWord ++ tailWord_284544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284547 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 2]
def baseStart_284547 : Nat := 118140960795 + 284547 * 2 ^ 59
def prefixEnd_284547 : Nat := 4983230072969 + 3 ^ 40 * 284547 * 2
def baseEnd_284547 : Nat := 129875004262225282003465

theorem tailTrace_284547 : CollatzResearch.WordTrace tailWord_284547 prefixEnd_284547 129875004262225282003465 := by
  unfold tailWord_284547
  simp only [CollatzResearch.WordTrace]
  refine ⟨10378281700142290603723895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6918854466761527069149263 10378281700142290603723895)
  ·
    refine ⟨15567422550213435905585843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10378281700142290603723895 15567422550213435905585843)
    ·
      refine ⟨23351133825320153858378765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15567422550213435905585843 23351133825320153858378765)
      ·
        refine ⟨8756675184495057696892037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23351133825320153858378765 8756675184495057696892037)
        ·
          refine ⟨1641876597092823318167257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8756675184495057696892037 1641876597092823318167257)
          ·
            refine ⟨1231407447819617488625443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641876597092823318167257 1231407447819617488625443)
            ·
              refine ⟨1847111171729426232938165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231407447819617488625443 1847111171729426232938165)
              ·
                refine ⟨173166672349633709337953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1847111171729426232938165 173166672349633709337953)
                ·
                  refine ⟨129875004262225282003465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173166672349633709337953 129875004262225282003465)
                  ·
                    rfl

theorem cell20_284547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 2].length) (baseStart_284547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284547 prefixEnd_284547 := by exact prefixLift 284547
  have htrace : WordTrace (prefixWord ++ tailWord_284547) baseStart_284547 baseEnd_284547 := by
    simpa [prefixWord, tailWord_284547, baseEnd_284547] using wordTrace_append hprefix tailTrace_284547
  have hstable : (prefixWord ++ tailWord_284547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284547).length < 2 ^ (prefixWord ++ tailWord_284547).sum := by decide
  have hdescent : baseEnd_284547 < baseStart_284547 := by decide
  rcases family_descends (prefixWord ++ tailWord_284547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284554 : List Nat := [3, 1, 2, 4, 2, 1, 7]
def baseStart_284554 : Nat := 118140960795 + 284554 * 2 ^ 59
def prefixEnd_284554 : Nat := 4983230072969 + 3 ^ 40 * 284554 * 2
def baseEnd_284554 : Nat := 14430911028107152085567

theorem tailTrace_284554 : CollatzResearch.WordTrace tailWord_284554 prefixEnd_284554 14430911028107152085567 := by
  unfold tailWord_284554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594634252779232699807179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6919024674077953866152477 2594634252779232699807179)
  ·
    refine ⟨3891951379168849049710769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2594634252779232699807179 3891951379168849049710769)
    ·
      refine ⟨2918963534376636787283077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3891951379168849049710769 2918963534376636787283077)
      ·
        refine ⟨547305662695619397615577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2918963534376636787283077 547305662695619397615577)
        ·
          refine ⟨410479247021714548211683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 547305662695619397615577 410479247021714548211683)
          ·
            refine ⟨615718870532571822317525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410479247021714548211683 615718870532571822317525)
            ·
              refine ⟨14430911028107152085567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 615718870532571822317525 14430911028107152085567)
              ·
                rfl

theorem cell20_284554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 7].length) (baseStart_284554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284554 prefixEnd_284554 := by exact prefixLift 284554
  have htrace : WordTrace (prefixWord ++ tailWord_284554) baseStart_284554 baseEnd_284554 := by
    simpa [prefixWord, tailWord_284554, baseEnd_284554] using wordTrace_append hprefix tailTrace_284554
  have hstable : (prefixWord ++ tailWord_284554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284554).length < 2 ^ (prefixWord ++ tailWord_284554).sum := by decide
  have hdescent : baseEnd_284554 < baseStart_284554 := by decide
  rcases family_descends (prefixWord ++ tailWord_284554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284561 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 3]
def baseStart_284561 : Nat := 118140960795 + 284561 * 2 ^ 59
def prefixEnd_284561 : Nat := 4983230072969 + 3 ^ 40 * 284561 * 2
def baseEnd_284561 : Nat := 129881394243703455536741

theorem tailTrace_284561 : CollatzResearch.WordTrace tailWord_284561 prefixEnd_284561 129881394243703455536741 := by
  unfold tailWord_284561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10378792322091570994733537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6919194881394380663155691 10378792322091570994733537)
  ·
    refine ⟨7784094241568678246050153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10378792322091570994733537 7784094241568678246050153)
    ·
      refine ⟨5838070681176508684537615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7784094241568678246050153 5838070681176508684537615)
      ·
        refine ⟨8757106021764763026806423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5838070681176508684537615 8757106021764763026806423)
        ·
          refine ⟨13135659032647144540209635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8757106021764763026806423 13135659032647144540209635)
          ·
            refine ⟨19703488548970716810314453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13135659032647144540209635 19703488548970716810314453)
            ·
              refine ⟨461800512866501175241745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19703488548970716810314453 461800512866501175241745)
              ·
                refine ⟨346350384649875881431309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 461800512866501175241745 346350384649875881431309)
                ·
                  refine ⟨129881394243703455536741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346350384649875881431309 129881394243703455536741)
                  ·
                    rfl

theorem cell20_284561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_284561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284561 prefixEnd_284561 := by exact prefixLift 284561
  have htrace : WordTrace (prefixWord ++ tailWord_284561) baseStart_284561 baseEnd_284561 := by
    simpa [prefixWord, tailWord_284561, baseEnd_284561] using wordTrace_append hprefix tailTrace_284561
  have hstable : (prefixWord ++ tailWord_284561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284561).length < 2 ^ (prefixWord ++ tailWord_284561).sum := by decide
  have hdescent : baseEnd_284561 < baseStart_284561 := by decide
  rcases family_descends (prefixWord ++ tailWord_284561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284564 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 2]
def baseStart_284564 : Nat := 118140960795 + 284564 * 2 ^ 59
def prefixEnd_284564 : Nat := 4983230072969 + 3 ^ 40 * 284564 * 2
def baseEnd_284564 : Nat := 129882763525448778436729

theorem tailTrace_284564 : CollatzResearch.WordTrace tailWord_284564 prefixEnd_284564 129882763525448778436729 := by
  unfold tailWord_284564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189450870540351253546373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6919267827387135004728497 5189450870540351253546373)
  ·
    refine ⟨973022038226315860039945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5189450870540351253546373 973022038226315860039945)
    ·
      refine ⟨729766528669736895029959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 973022038226315860039945 729766528669736895029959)
      ·
        refine ⟨1094649793004605342544939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729766528669736895029959 1094649793004605342544939)
        ·
          refine ⟨1641974689506908013817409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094649793004605342544939 1641974689506908013817409)
          ·
            refine ⟨1231481017130181010363057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641974689506908013817409 1231481017130181010363057)
            ·
              refine ⟨923610762847635757772293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231481017130181010363057 923610762847635757772293)
              ·
                refine ⟨173177018033931704582305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 923610762847635757772293 173177018033931704582305)
                ·
                  refine ⟨129882763525448778436729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173177018033931704582305 129882763525448778436729)
                  ·
                    rfl

theorem cell20_284564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_284564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284564 prefixEnd_284564 := by exact prefixLift 284564
  have htrace : WordTrace (prefixWord ++ tailWord_284564) baseStart_284564 baseEnd_284564 := by
    simpa [prefixWord, tailWord_284564, baseEnd_284564] using wordTrace_append hprefix tailTrace_284564
  have hstable : (prefixWord ++ tailWord_284564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284564).length < 2 ^ (prefixWord ++ tailWord_284564).sum := by decide
  have hdescent : baseEnd_284564 < baseStart_284564 := by decide
  rcases family_descends (prefixWord ++ tailWord_284564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284633 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 3]
def baseStart_284633 : Nat := 118140960795 + 284633 * 2 ^ 59
def prefixEnd_284633 : Nat := 4983230072969 + 3 ^ 40 * 284633 * 2
def baseEnd_284633 : Nat := 129914257005591205136447

theorem tailTrace_284633 : CollatzResearch.WordTrace tailWord_284633 prefixEnd_284633 129914257005591205136447 := by
  unfold tailWord_284633
  simp only [CollatzResearch.WordTrace]
  refine ⟨10381418377830727291354553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6920945585220484860903035 10381418377830727291354553)
  ·
    refine ⟨7786063783373045468515915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10381418377830727291354553 7786063783373045468515915)
    ·
      refine ⟨11679095675059568202773873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7786063783373045468515915 11679095675059568202773873)
      ·
        refine ⟨8759321756294676152080405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11679095675059568202773873 8759321756294676152080405)
        ·
          refine ⟨410593207326312944628769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8759321756294676152080405 410593207326312944628769)
          ·
            refine ⟨307944905494734708471577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410593207326312944628769 307944905494734708471577)
            ·
              refine ⟨230958679121051031353683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307944905494734708471577 230958679121051031353683)
              ·
                refine ⟨346438018681576547030525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230958679121051031353683 346438018681576547030525)
                ·
                  refine ⟨129914257005591205136447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346438018681576547030525 129914257005591205136447)
                  ·
                    rfl

theorem cell20_284633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_284633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284633 prefixEnd_284633 := by exact prefixLift 284633
  have htrace : WordTrace (prefixWord ++ tailWord_284633) baseStart_284633 baseEnd_284633 := by
    simpa [prefixWord, tailWord_284633, baseEnd_284633] using wordTrace_append hprefix tailTrace_284633
  have hstable : (prefixWord ++ tailWord_284633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284633).length < 2 ^ (prefixWord ++ tailWord_284633).sum := by decide
  have hdescent : baseEnd_284633 < baseStart_284633 := by decide
  rcases family_descends (prefixWord ++ tailWord_284633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284706 : List Nat := [3, 3, 1, 1, 1, 2, 5, 4]
def baseStart_284706 : Nat := 118140960795 + 284706 * 2 ^ 59
def prefixEnd_284706 : Nat := 4983230072969 + 3 ^ 40 * 284706 * 2
def baseEnd_284706 : Nat := 43315858731575798567605

theorem tailTrace_284706 : CollatzResearch.WordTrace tailWord_284706 prefixEnd_284706 43315858731575798567605 := by
  unfold tailWord_284706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596020226641565189690493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6922720604377507172507981 2596020226641565189690493)
  ·
    refine ⟨973507584990586946133935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2596020226641565189690493 973507584990586946133935)
    ·
      refine ⟨1460261377485880419200903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973507584990586946133935 1460261377485880419200903)
      ·
        refine ⟨2190392066228820628801355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460261377485880419200903 2190392066228820628801355)
        ·
          refine ⟨3285588099343230943202033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190392066228820628801355 3285588099343230943202033)
          ·
            refine ⟨2464191074507423207401525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285588099343230943202033 2464191074507423207401525)
            ·
              refine ⟨231017913235070925693893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2464191074507423207401525 231017913235070925693893)
              ·
                refine ⟨43315858731575798567605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231017913235070925693893 43315858731575798567605)
                ·
                  rfl

theorem cell20_284706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_284706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284706 prefixEnd_284706 := by exact prefixLift 284706
  have htrace : WordTrace (prefixWord ++ tailWord_284706) baseStart_284706 baseEnd_284706 := by
    simpa [prefixWord, tailWord_284706, baseEnd_284706] using wordTrace_append hprefix tailTrace_284706
  have hstable : (prefixWord ++ tailWord_284706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284706).length < 2 ^ (prefixWord ++ tailWord_284706).sum := by decide
  have hdescent : baseEnd_284706 < baseStart_284706 := by decide
  rcases family_descends (prefixWord ++ tailWord_284706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284737 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 4]
def baseStart_284737 : Nat := 118140960795 + 284737 * 2 ^ 59
def prefixEnd_284737 : Nat := 4983230072969 + 3 ^ 40 * 284737 * 2
def baseEnd_284737 : Nat := 129961725439429065669355

theorem tailTrace_284737 : CollatzResearch.WordTrace tailWord_284737 prefixEnd_284737 129961725439429065669355 := by
  unfold tailWord_284737
  simp only [CollatzResearch.WordTrace]
  refine ⟨10385211569453953053140465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6923474379635968702093643 10385211569453953053140465)
  ·
    refine ⟨7788908677090464789855349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10385211569453953053140465 7788908677090464789855349)
    ·
      refine ⟨730210188477231074048939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7788908677090464789855349 730210188477231074048939)
      ·
        refine ⟨1095315282715846611073409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730210188477231074048939 1095315282715846611073409)
        ·
          refine ⟨821486462036884958305057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095315282715846611073409 821486462036884958305057)
          ·
            refine ⟨616114846527663718728793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821486462036884958305057 616114846527663718728793)
            ·
              refine ⟨462086134895747789046595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616114846527663718728793 462086134895747789046595)
              ·
                refine ⟨693129202343621683569893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462086134895747789046595 693129202343621683569893)
                ·
                  refine ⟨129961725439429065669355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693129202343621683569893 129961725439429065669355)
                  ·
                    rfl

theorem cell20_284737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_284737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284737 prefixEnd_284737 := by exact prefixLift 284737
  have htrace : WordTrace (prefixWord ++ tailWord_284737) baseStart_284737 baseEnd_284737 := by
    simpa [prefixWord, tailWord_284737, baseEnd_284737] using wordTrace_append hprefix tailTrace_284737
  have hstable : (prefixWord ++ tailWord_284737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284737).length < 2 ^ (prefixWord ++ tailWord_284737).sum := by decide
  have hdescent : baseEnd_284737 < baseStart_284737 := by decide
  rcases family_descends (prefixWord ++ tailWord_284737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284772 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_284772 : Nat := 118140960795 + 284772 * 2 ^ 59
def prefixEnd_284772 : Nat := 4983230072969 + 3 ^ 40 * 284772 * 2
def baseEnd_284772 : Nat := 129977700393124499502545

theorem tailTrace_284772 : CollatzResearch.WordTrace tailWord_284772 prefixEnd_284772 129977700393124499502545 := by
  unfold tailWord_284772
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193244062163577015332285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6924325416218102687109713 5193244062163577015332285)
  ·
    refine ⟨1947466523311341380749607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5193244062163577015332285 1947466523311341380749607)
    ·
      refine ⟨2921199784967012071124411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1947466523311341380749607 2921199784967012071124411)
      ·
        refine ⟨4381799677450518106686617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921199784967012071124411 4381799677450518106686617)
        ·
          refine ⟨3286349758087888580014963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4381799677450518106686617 3286349758087888580014963)
          ·
            refine ⟨4929524637131832870022445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286349758087888580014963 4929524637131832870022445)
            ·
              refine ⟨1848571738924437326258417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4929524637131832870022445 1848571738924437326258417)
              ·
                refine ⟨1386428804193327994693813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848571738924437326258417 1386428804193327994693813)
                ·
                  refine ⟨129977700393124499502545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1386428804193327994693813 129977700393124499502545)
                  ·
                    rfl

theorem cell20_284772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_284772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284772 prefixEnd_284772 := by exact prefixLift 284772
  have htrace : WordTrace (prefixWord ++ tailWord_284772) baseStart_284772 baseEnd_284772 := by
    simpa [prefixWord, tailWord_284772, baseEnd_284772] using wordTrace_append hprefix tailTrace_284772
  have hstable : (prefixWord ++ tailWord_284772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284772).length < 2 ^ (prefixWord ++ tailWord_284772).sum := by decide
  have hdescent : baseEnd_284772 < baseStart_284772 := by decide
  rcases family_descends (prefixWord ++ tailWord_284772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284796 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_284796 : Nat := 118140960795 + 284796 * 2 ^ 59
def prefixEnd_284796 : Nat := 4983230072969 + 3 ^ 40 * 284796 * 2
def baseEnd_284796 : Nat := 129988654647087082702447

theorem tailTrace_284796 : CollatzResearch.WordTrace tailWord_284796 prefixEnd_284796 129988654647087082702447 := by
  unfold tailWord_284796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193681738120103064769121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6924908984160137419692161 5193681738120103064769121)
  ·
    refine ⟨3895261303590077298576841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5193681738120103064769121 3895261303590077298576841)
    ·
      refine ⟨2921445977692557973932631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895261303590077298576841 2921445977692557973932631)
      ·
        refine ⟨4382168966538836960898947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2921445977692557973932631 4382168966538836960898947)
        ·
          refine ⟨6573253449808255441348421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4382168966538836960898947 6573253449808255441348421)
          ·
            refine ⟨1232485021839047895252829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6573253449808255441348421 1232485021839047895252829)
            ·
              refine ⟨462181883189642960719811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1232485021839047895252829 462181883189642960719811)
              ·
                refine ⟨693272824784464441079717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462181883189642960719811 693272824784464441079717)
                ·
                  refine ⟨129988654647087082702447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693272824784464441079717 129988654647087082702447)
                  ·
                    rfl

theorem cell20_284796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_284796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284796 prefixEnd_284796 := by exact prefixLift 284796
  have htrace : WordTrace (prefixWord ++ tailWord_284796) baseStart_284796 baseEnd_284796 := by
    simpa [prefixWord, tailWord_284796, baseEnd_284796] using wordTrace_append hprefix tailTrace_284796
  have hstable : (prefixWord ++ tailWord_284796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284796).length < 2 ^ (prefixWord ++ tailWord_284796).sum := by decide
  have hdescent : baseEnd_284796 < baseStart_284796 := by decide
  rcases family_descends (prefixWord ++ tailWord_284796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284803 : List Nat := [1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_284803 : Nat := 118140960795 + 284803 * 2 ^ 59
def prefixEnd_284803 : Nat := 4983230072969 + 3 ^ 40 * 284803 * 2
def baseEnd_284803 : Nat := 43330616545942056489695

theorem tailTrace_284803 : CollatzResearch.WordTrace tailWord_284803 prefixEnd_284803 43330616545942056489695 := by
  unfold tailWord_284803
  simp only [CollatzResearch.WordTrace]
  refine ⟨10387618787214846325043063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6925079191476564216695375 10387618787214846325043063)
  ·
    refine ⟨15581428180822269487564595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10387618787214846325043063 15581428180822269487564595)
    ·
      refine ⟨23372142271233404231346893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15581428180822269487564595 23372142271233404231346893)
      ·
        refine ⟨8764553351712526586755085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23372142271233404231346893 8764553351712526586755085)
        ·
          refine ⟨3286707506892197470033157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8764553351712526586755085 3286707506892197470033157)
          ·
            refine ⟨616257657542287025631217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3286707506892197470033157 616257657542287025631217)
            ·
              refine ⟨462193243156715269223413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616257657542287025631217 462193243156715269223413)
              ·
                refine ⟨43330616545942056489695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 462193243156715269223413 43330616545942056489695)
                ·
                  rfl

theorem cell20_284803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_284803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284803 prefixEnd_284803 := by exact prefixLift 284803
  have htrace : WordTrace (prefixWord ++ tailWord_284803) baseStart_284803 baseEnd_284803 := by
    simpa [prefixWord, tailWord_284803, baseEnd_284803] using wordTrace_append hprefix tailTrace_284803
  have hstable : (prefixWord ++ tailWord_284803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284803).length < 2 ^ (prefixWord ++ tailWord_284803).sum := by decide
  have hdescent : baseEnd_284803 < baseStart_284803 := by decide
  rcases family_descends (prefixWord ++ tailWord_284803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284879 : List Nat := [1, 1, 2, 1, 1, 3, 7, 4]
def baseStart_284879 : Nat := 118140960795 + 284879 * 2 ^ 59
def prefixEnd_284879 : Nat := 4983230072969 + 3 ^ 40 * 284879 * 2
def baseEnd_284879 : Nat := 43342179369569227645147

theorem tailTrace_284879 : CollatzResearch.WordTrace tailWord_284879 prefixEnd_284879 43342179369569227645147 := by
  unfold tailWord_284879
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390390734939511304809691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6926927156626340869873127 10390390734939511304809691)
  ·
    refine ⟨15585586102409266957214537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10390390734939511304809691 15585586102409266957214537)
    ·
      refine ⟨11689189576806950217910903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15585586102409266957214537 11689189576806950217910903)
      ·
        refine ⟨17533784365210425326866355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11689189576806950217910903 17533784365210425326866355)
        ·
          refine ⟨26300676547815637990299533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17533784365210425326866355 26300676547815637990299533)
          ·
            refine ⟨9862753705430864246362325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26300676547815637990299533 9862753705430864246362325)
            ·
              refine ⟨231158289971035880774117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9862753705430864246362325 231158289971035880774117)
              ·
                refine ⟨43342179369569227645147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231158289971035880774117 43342179369569227645147)
                ·
                  rfl

theorem cell20_284879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_284879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284879 prefixEnd_284879 := by exact prefixLift 284879
  have htrace : WordTrace (prefixWord ++ tailWord_284879) baseStart_284879 baseEnd_284879 := by
    simpa [prefixWord, tailWord_284879, baseEnd_284879] using wordTrace_append hprefix tailTrace_284879
  have hstable : (prefixWord ++ tailWord_284879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284879).length < 2 ^ (prefixWord ++ tailWord_284879).sum := by decide
  have hdescent : baseEnd_284879 < baseStart_284879 := by decide
  rcases family_descends (prefixWord ++ tailWord_284879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284899 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 3]
def baseStart_284899 : Nat := 118140960795 + 284899 * 2 ^ 59
def prefixEnd_284899 : Nat := 4983230072969 + 3 ^ 40 * 284899 * 2
def baseEnd_284899 : Nat := 130035666653676502268693

theorem tailTrace_284899 : CollatzResearch.WordTrace tailWord_284899 prefixEnd_284899 130035666653676502268693 := by
  unfold tailWord_284899
  simp only [CollatzResearch.WordTrace]
  refine ⟨10391120194867054720537751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6927413463244703147025167 10391120194867054720537751)
  ·
    refine ⟨15586680292300582080806627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10391120194867054720537751 15586680292300582080806627)
    ·
      refine ⟨23380020438450873121209941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15586680292300582080806627 23380020438450873121209941)
      ·
        refine ⟨273984614513096169389179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 23380020438450873121209941 273984614513096169389179)
        ·
          refine ⟨410976921769644254083769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273984614513096169389179 410976921769644254083769)
          ·
            refine ⟨308232691327233190562827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 410976921769644254083769 308232691327233190562827)
            ·
              refine ⟨462349036990849785844241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308232691327233190562827 462349036990849785844241)
              ·
                refine ⟨346761777743137339383181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462349036990849785844241 346761777743137339383181)
                ·
                  refine ⟨130035666653676502268693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346761777743137339383181 130035666653676502268693)
                  ·
                    rfl

theorem cell20_284899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 3].length) (baseStart_284899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284899 prefixEnd_284899 := by exact prefixLift 284899
  have htrace : WordTrace (prefixWord ++ tailWord_284899) baseStart_284899 baseEnd_284899 := by
    simpa [prefixWord, tailWord_284899, baseEnd_284899] using wordTrace_append hprefix tailTrace_284899
  have hstable : (prefixWord ++ tailWord_284899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284899).length < 2 ^ (prefixWord ++ tailWord_284899).sum := by decide
  have hdescent : baseEnd_284899 < baseStart_284899 := by decide
  rcases family_descends (prefixWord ++ tailWord_284899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284903 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 5]
def baseStart_284903 : Nat := 118140960795 + 284903 * 2 ^ 59
def prefixEnd_284903 : Nat := 4983230072969 + 3 ^ 40 * 284903 * 2
def baseEnd_284903 : Nat := 130037492362670266135343

theorem tailTrace_284903 : CollatzResearch.WordTrace tailWord_284903 prefixEnd_284903 130037492362670266135343 := by
  unfold tailWord_284903
  simp only [CollatzResearch.WordTrace]
  refine ⟨10391266086852563403683363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6927510724568375602455575 10391266086852563403683363)
  ·
    refine ⟨15586899130278845105525045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10391266086852563403683363 15586899130278845105525045)
    ·
      refine ⟨1461271793463641728642973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15586899130278845105525045 1461271793463641728642973)
      ·
        refine ⟨547976922548865648241115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1461271793463641728642973 547976922548865648241115)
        ·
          refine ⟨821965383823298472361673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547976922548865648241115 821965383823298472361673)
          ·
            refine ⟨616474037867473854271255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821965383823298472361673 616474037867473854271255)
            ·
              refine ⟨924711056801210781406883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616474037867473854271255 924711056801210781406883)
              ·
                refine ⟨1387066585201816172110325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924711056801210781406883 1387066585201816172110325)
                ·
                  refine ⟨130037492362670266135343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1387066585201816172110325 130037492362670266135343)
                  ·
                    rfl

theorem cell20_284903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_284903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284903 prefixEnd_284903 := by exact prefixLift 284903
  have htrace : WordTrace (prefixWord ++ tailWord_284903) baseStart_284903 baseEnd_284903 := by
    simpa [prefixWord, tailWord_284903, baseEnd_284903] using wordTrace_append hprefix tailTrace_284903
  have hstable : (prefixWord ++ tailWord_284903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284903).length < 2 ^ (prefixWord ++ tailWord_284903).sum := by decide
  have hdescent : baseEnd_284903 < baseStart_284903 := by decide
  rcases family_descends (prefixWord ++ tailWord_284903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284931 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_284931 : Nat := 118140960795 + 284931 * 2 ^ 59
def prefixEnd_284931 : Nat := 4983230072969 + 3 ^ 40 * 284931 * 2
def baseEnd_284931 : Nat := 130050272325626613201895

theorem tailTrace_284931 : CollatzResearch.WordTrace tailWord_284931 prefixEnd_284931 130050272325626613201895 := by
  unfold tailWord_284931
  simp only [CollatzResearch.WordTrace]
  refine ⟨10392287330751124185702647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6928191553834082790468431 10392287330751124185702647)
  ·
    refine ⟨15588430996126686278553971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10392287330751124185702647 15588430996126686278553971)
    ·
      refine ⟨23382646494190029417830957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15588430996126686278553971 23382646494190029417830957)
      ·
        refine ⟨8768492435321261031686609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23382646494190029417830957 8768492435321261031686609)
        ·
          refine ⟨6576369326490945773764957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8768492435321261031686609 6576369326490945773764957)
          ·
            refine ⟨2466138497434104665161859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6576369326490945773764957 2466138497434104665161859)
            ·
              refine ⟨3699207746151156997742789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466138497434104665161859 3699207746151156997742789)
              ·
                refine ⟨693601452403341937076773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3699207746151156997742789 693601452403341937076773)
                ·
                  refine ⟨130050272325626613201895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693601452403341937076773 130050272325626613201895)
                  ·
                    rfl

theorem cell20_284931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_284931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284931 prefixEnd_284931 := by exact prefixLift 284931
  have htrace : WordTrace (prefixWord ++ tailWord_284931) baseStart_284931 baseEnd_284931 := by
    simpa [prefixWord, tailWord_284931, baseEnd_284931] using wordTrace_append hprefix tailTrace_284931
  have hstable : (prefixWord ++ tailWord_284931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284931).length < 2 ^ (prefixWord ++ tailWord_284931).sum := by decide
  have hdescent : baseEnd_284931 < baseStart_284931 := by decide
  rcases family_descends (prefixWord ++ tailWord_284931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284958 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_284958 : Nat := 118140960795 + 284958 * 2 ^ 59
def prefixEnd_284958 : Nat := 4983230072969 + 3 ^ 40 * 284958 * 2
def baseEnd_284958 : Nat := 130062595861334519301785

theorem tailTrace_284958 : CollatzResearch.WordTrace tailWord_284958 prefixEnd_284958 130062595861334519301785 := by
  unfold tailWord_284958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299159012706663474616941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6928848067768871864623685 1299159012706663474616941)
  ·
    refine ⟨487184629764998802981353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1299159012706663474616941 487184629764998802981353)
    ·
      refine ⟨365388472323749102236015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 487184629764998802981353 365388472323749102236015)
      ·
        refine ⟨548082708485623653354023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365388472323749102236015 548082708485623653354023)
        ·
          refine ⟨822124062728435480031035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548082708485623653354023 822124062728435480031035)
          ·
            refine ⟨1233186094092653220046553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822124062728435480031035 1233186094092653220046553)
            ·
              refine ⟨924889570569489915034915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233186094092653220046553 924889570569489915034915)
              ·
                refine ⟨1387334355854234872552373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924889570569489915034915 1387334355854234872552373)
                ·
                  refine ⟨130062595861334519301785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1387334355854234872552373 130062595861334519301785)
                  ·
                    rfl

theorem cell20_284958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_284958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284958 prefixEnd_284958 := by exact prefixLift 284958
  have htrace : WordTrace (prefixWord ++ tailWord_284958) baseStart_284958 baseEnd_284958 := by
    simpa [prefixWord, tailWord_284958, baseEnd_284958] using wordTrace_append hprefix tailTrace_284958
  have hstable : (prefixWord ++ tailWord_284958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284958).length < 2 ^ (prefixWord ++ tailWord_284958).sum := by decide
  have hdescent : baseEnd_284958 < baseStart_284958 := by decide
  rcases family_descends (prefixWord ++ tailWord_284958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_284965 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 4]
def baseStart_284965 : Nat := 118140960795 + 284965 * 2 ^ 59
def prefixEnd_284965 : Nat := 4983230072969 + 3 ^ 40 * 284965 * 2
def baseEnd_284965 : Nat := 130065790852073606068423

theorem tailTrace_284965 : CollatzResearch.WordTrace tailWord_284965 prefixEnd_284965 130065790852073606068423 := by
  unfold tailWord_284965
  simp only [CollatzResearch.WordTrace]
  refine ⟨10393527412627947992440349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6929018275085298661626899 10393527412627947992440349)
  ·
    refine ⟨3897572779735480497165131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10393527412627947992440349 3897572779735480497165131)
    ·
      refine ⟨5846359169603220745747697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3897572779735480497165131 5846359169603220745747697)
      ·
        refine ⟨4384769377202415559310773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5846359169603220745747697 4384769377202415559310773)
        ·
          refine ⟨411072129112726458685385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4384769377202415559310773 411072129112726458685385)
          ·
            refine ⟨308304096834544844014039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411072129112726458685385 308304096834544844014039)
            ·
              refine ⟨462456145251817266021059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308304096834544844014039 462456145251817266021059)
              ·
                refine ⟨693684217877725899031589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 462456145251817266021059 693684217877725899031589)
                ·
                  refine ⟨130065790852073606068423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 693684217877725899031589 130065790852073606068423)
                  ·
                    rfl

theorem cell20_284965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_284965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_284965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_284965 prefixEnd_284965 := by exact prefixLift 284965
  have htrace : WordTrace (prefixWord ++ tailWord_284965) baseStart_284965 baseEnd_284965 := by
    simpa [prefixWord, tailWord_284965, baseEnd_284965] using wordTrace_append hprefix tailTrace_284965
  have hstable : (prefixWord ++ tailWord_284965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_284965).length < 2 ^ (prefixWord ++ tailWord_284965).sum := by decide
  have hdescent : baseEnd_284965 < baseStart_284965 := by decide
  rcases family_descends (prefixWord ++ tailWord_284965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285031 : List Nat := [1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_285031 : Nat := 118140960795 + 285031 * 2 ^ 59
def prefixEnd_285031 : Nat := 4983230072969 + 3 ^ 40 * 285031 * 2
def baseEnd_285031 : Nat := 43365305016823569956051

theorem tailTrace_285031 : CollatzResearch.WordTrace tailWord_285031 prefixEnd_285031 43365305016823569956051 := by
  unfold tailWord_285031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10395934630388841264342947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6930623086925894176228631 10395934630388841264342947)
  ·
    refine ⟨15593901945583261896514421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10395934630388841264342947 15593901945583261896514421)
    ·
      refine ⟨1461928307398430802798227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15593901945583261896514421 1461928307398430802798227)
      ·
        refine ⟨2192892461097646204197341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1461928307398430802798227 2192892461097646204197341)
        ·
          refine ⟨822334672911617326574003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2192892461097646204197341 822334672911617326574003)
          ·
            refine ⟨1233502009367425989861005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822334672911617326574003 1233502009367425989861005)
            ·
              refine ⟨462563253512784746197877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1233502009367425989861005 462563253512784746197877)
              ·
                refine ⟨43365305016823569956051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 462563253512784746197877 43365305016823569956051)
                ·
                  rfl

theorem cell20_285031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_285031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285031 prefixEnd_285031 := by exact prefixLift 285031
  have htrace : WordTrace (prefixWord ++ tailWord_285031) baseStart_285031 baseEnd_285031 := by
    simpa [prefixWord, tailWord_285031, baseEnd_285031] using wordTrace_append hprefix tailTrace_285031
  have hstable : (prefixWord ++ tailWord_285031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285031).length < 2 ^ (prefixWord ++ tailWord_285031).sum := by decide
  have hdescent : baseEnd_285031 < baseStart_285031 := by decide
  rcases family_descends (prefixWord ++ tailWord_285031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285089 : List Nat := [1, 2, 3, 5, 1, 1, 3, 1, 3]
def baseStart_285089 : Nat := 118140960795 + 285089 * 2 ^ 59
def prefixEnd_285089 : Nat := 4983230072969 + 3 ^ 40 * 285089 * 2
def baseEnd_285089 : Nat := 130122387830880285934583

theorem tailTrace_285089 : CollatzResearch.WordTrace tailWord_285089 prefixEnd_285089 130122387830880285934583 := by
  unfold tailWord_285089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398050064178717169954321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6932033376119144779969547 10398050064178717169954321)
  ·
    refine ⟨7798537548134037877465741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10398050064178717169954321 7798537548134037877465741)
    ·
      refine ⟨2924451580550264204049653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7798537548134037877465741 2924451580550264204049653)
      ·
        refine ⟨274167335676587269129655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2924451580550264204049653 274167335676587269129655)
        ·
          refine ⟨411251003514880903694483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274167335676587269129655 411251003514880903694483)
          ·
            refine ⟨616876505272321355541725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411251003514880903694483 616876505272321355541725)
            ·
              refine ⟨231328689477120508328147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 616876505272321355541725 231328689477120508328147)
              ·
                refine ⟨346993034215680762492221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231328689477120508328147 346993034215680762492221)
                ·
                  refine ⟨130122387830880285934583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346993034215680762492221 130122387830880285934583)
                  ·
                    rfl

theorem cell20_285089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_285089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285089 prefixEnd_285089 := by exact prefixLift 285089
  have htrace : WordTrace (prefixWord ++ tailWord_285089) baseStart_285089 baseEnd_285089 := by
    simpa [prefixWord, tailWord_285089, baseEnd_285089] using wordTrace_append hprefix tailTrace_285089
  have hstable : (prefixWord ++ tailWord_285089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285089).length < 2 ^ (prefixWord ++ tailWord_285089).sum := by decide
  have hdescent : baseEnd_285089 < baseStart_285089 := by decide
  rcases family_descends (prefixWord ++ tailWord_285089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285093 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 3]
def baseStart_285093 : Nat := 118140960795 + 285093 * 2 ^ 59
def prefixEnd_285093 : Nat := 4983230072969 + 3 ^ 40 * 285093 * 2
def baseEnd_285093 : Nat := 130124213539874049801233

theorem tailTrace_285093 : CollatzResearch.WordTrace tailWord_285093 prefixEnd_285093 130124213539874049801233 := by
  unfold tailWord_285093
  simp only [CollatzResearch.WordTrace]
  refine ⟨10398195956164225853099933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6932130637442817235399955 10398195956164225853099933)
  ·
    refine ⟨3899323483561584694912475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10398195956164225853099933 3899323483561584694912475)
    ·
      refine ⟨5848985225342377042368713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3899323483561584694912475 5848985225342377042368713)
      ·
        refine ⟨4386738919006782781776535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5848985225342377042368713 4386738919006782781776535)
        ·
          refine ⟨6580108378510174172664803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386738919006782781776535 6580108378510174172664803)
          ·
            refine ⟨9870162567765261258997205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6580108378510174172664803 9870162567765261258997205)
            ·
              refine ⟨231331935181998310757747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9870162567765261258997205 231331935181998310757747)
              ·
                refine ⟨346997902772997466136621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231331935181998310757747 346997902772997466136621)
                ·
                  refine ⟨130124213539874049801233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 346997902772997466136621 130124213539874049801233)
                  ·
                    rfl

theorem cell20_285093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_285093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285093 prefixEnd_285093 := by exact prefixLift 285093
  have htrace : WordTrace (prefixWord ++ tailWord_285093) baseStart_285093 baseEnd_285093 := by
    simpa [prefixWord, tailWord_285093, baseEnd_285093] using wordTrace_append hprefix tailTrace_285093
  have hstable : (prefixWord ++ tailWord_285093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285093).length < 2 ^ (prefixWord ++ tailWord_285093).sum := by decide
  have hdescent : baseEnd_285093 < baseStart_285093 := by decide
  rcases family_descends (prefixWord ++ tailWord_285093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285117 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 2]
def baseStart_285117 : Nat := 118140960795 + 285117 * 2 ^ 59
def prefixEnd_285117 : Nat := 4983230072969 + 3 ^ 40 * 285117 * 2
def baseEnd_285117 : Nat := 130135167793836633001135

theorem tailTrace_285117 : CollatzResearch.WordTrace tailWord_285117 prefixEnd_285117 130135167793836633001135 := by
  unfold tailWord_285117
  simp only [CollatzResearch.WordTrace]
  refine ⟨10399071308077277951973605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6932714205384851967982403 10399071308077277951973605)
  ·
    refine ⟨1949825870264489615995051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10399071308077277951973605 1949825870264489615995051)
    ·
      refine ⟨2924738805396734423992577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1949825870264489615995051 2924738805396734423992577)
      ·
        refine ⟨2193554104047550817994433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2924738805396734423992577 2193554104047550817994433)
        ·
          refine ⟨1645165578035663113495825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193554104047550817994433 1645165578035663113495825)
          ·
            refine ⟨1233874183526747335121869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1645165578035663113495825 1233874183526747335121869)
            ·
              refine ⟨462702818822530250670701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1233874183526747335121869 462702818822530250670701)
              ·
                refine ⟨173513557058448844001513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462702818822530250670701 173513557058448844001513)
                ·
                  refine ⟨130135167793836633001135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173513557058448844001513 130135167793836633001135)
                  ·
                    rfl

theorem cell20_285117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_285117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285117 prefixEnd_285117 := by exact prefixLift 285117
  have htrace : WordTrace (prefixWord ++ tailWord_285117) baseStart_285117 baseEnd_285117 := by
    simpa [prefixWord, tailWord_285117, baseEnd_285117] using wordTrace_append hprefix tailTrace_285117
  have hstable : (prefixWord ++ tailWord_285117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285117).length < 2 ^ (prefixWord ++ tailWord_285117).sum := by decide
  have hdescent : baseEnd_285117 < baseStart_285117 := by decide
  rcases family_descends (prefixWord ++ tailWord_285117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285124 : List Nat := [2, 3, 3, 2, 2, 2, 6]
def baseStart_285124 : Nat := 118140960795 + 285124 * 2 ^ 59
def prefixEnd_285124 : Nat := 4983230072969 + 3 ^ 40 * 285124 * 2
def baseEnd_285124 : Nat := 14459818087175079974197

theorem tailTrace_285124 : CollatzResearch.WordTrace tailWord_285124 prefixEnd_285124 14459818087175079974197 := by
  unfold tailWord_285124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199663309525959073739213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6932884412701278764985617 5199663309525959073739213)
  ·
    refine ⟨1949873741072234652652205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5199663309525959073739213 1949873741072234652652205)
    ·
      refine ⟨731202652902087994744577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1949873741072234652652205 731202652902087994744577)
      ·
        refine ⟨548401989676565996058433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 731202652902087994744577 548401989676565996058433)
        ·
          refine ⟨411301492257424497043825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548401989676565996058433 411301492257424497043825)
          ·
            refine ⟨308476119193068372782869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411301492257424497043825 308476119193068372782869)
            ·
              refine ⟨14459818087175079974197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 308476119193068372782869 14459818087175079974197)
              ·
                rfl

theorem cell20_285124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 6].length) (baseStart_285124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285124 prefixEnd_285124 := by exact prefixLift 285124
  have htrace : WordTrace (prefixWord ++ tailWord_285124) baseStart_285124 baseEnd_285124 := by
    simpa [prefixWord, tailWord_285124, baseEnd_285124] using wordTrace_append hprefix tailTrace_285124
  have hstable : (prefixWord ++ tailWord_285124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285124).length < 2 ^ (prefixWord ++ tailWord_285124).sum := by decide
  have hdescent : baseEnd_285124 < baseStart_285124 := by decide
  rcases family_descends (prefixWord ++ tailWord_285124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285128 : List Nat := [2, 1, 3, 1, 3, 2, 8]
def baseStart_285128 : Nat := 118140960795 + 285128 * 2 ^ 59
def prefixEnd_285128 : Nat := 4983230072969 + 3 ^ 40 * 285128 * 2
def baseEnd_285128 : Nat := 14460020943729942626047

theorem tailTrace_285128 : CollatzResearch.WordTrace tailWord_285128 prefixEnd_285128 14460020943729942626047 := by
  unfold tailWord_285128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199736255518713415312019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6932981674024951220416025 5199736255518713415312019)
  ·
    refine ⟨7799604383278070122968029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5199736255518713415312019 7799604383278070122968029)
    ·
      refine ⟨2924851643729276296113011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7799604383278070122968029 2924851643729276296113011)
      ·
        refine ⟨4387277465593914444169517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924851643729276296113011 4387277465593914444169517)
        ·
          refine ⟨1645229049597717916563569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4387277465593914444169517 1645229049597717916563569)
          ·
            refine ⟨1233921787198288437422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1645229049597717916563569 1233921787198288437422677)
            ·
              refine ⟨14460020943729942626047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1233921787198288437422677 14460020943729942626047)
              ·
                rfl

theorem cell20_285128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_285128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285128 prefixEnd_285128 := by exact prefixLift 285128
  have htrace : WordTrace (prefixWord ++ tailWord_285128) baseStart_285128 baseEnd_285128 := by
    simpa [prefixWord, tailWord_285128, baseEnd_285128] using wordTrace_append hprefix tailTrace_285128
  have hstable : (prefixWord ++ tailWord_285128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285128).length < 2 ^ (prefixWord ++ tailWord_285128).sum := by decide
  have hdescent : baseEnd_285128 < baseStart_285128 := by decide
  rcases family_descends (prefixWord ++ tailWord_285128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285152 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 3]
def baseStart_285152 : Nat := 118140960795 + 285152 * 2 ^ 59
def prefixEnd_285152 : Nat := 4983230072969 + 3 ^ 40 * 285152 * 2
def baseEnd_285152 : Nat := 130151142747532066834325

theorem tailTrace_285152 : CollatzResearch.WordTrace tailWord_285152 prefixEnd_285152 130151142747532066834325 := by
  unfold tailWord_285152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200173931475239464748855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6933565241966985952998473 5200173931475239464748855)
  ·
    refine ⟨7800260897212859197123283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5200173931475239464748855 7800260897212859197123283)
    ·
      refine ⟨11700391345819288795684925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7800260897212859197123283 11700391345819288795684925)
      ·
        refine ⟨4387646754682233298381847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11700391345819288795684925 4387646754682233298381847)
        ·
          refine ⟨6581470132023349947572771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4387646754682233298381847 6581470132023349947572771)
          ·
            refine ⟨9872205198035024921359157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6581470132023349947572771 9872205198035024921359157)
            ·
              refine ⟨925519237315783586377421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9872205198035024921359157 925519237315783586377421)
              ·
                refine ⟨347069713993418844891533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 925519237315783586377421 347069713993418844891533)
                ·
                  refine ⟨130151142747532066834325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347069713993418844891533 130151142747532066834325)
                  ·
                    rfl

theorem cell20_285152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_285152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285152 prefixEnd_285152 := by exact prefixLift 285152
  have htrace : WordTrace (prefixWord ++ tailWord_285152) baseStart_285152 baseEnd_285152 := by
    simpa [prefixWord, tailWord_285152, baseEnd_285152] using wordTrace_append hprefix tailTrace_285152
  have hstable : (prefixWord ++ tailWord_285152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285152).length < 2 ^ (prefixWord ++ tailWord_285152).sum := by decide
  have hdescent : baseEnd_285152 < baseStart_285152 := by decide
  rcases family_descends (prefixWord ++ tailWord_285152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285159 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_285159 : Nat := 118140960795 + 285159 * 2 ^ 59
def prefixEnd_285159 : Nat := 4983230072969 + 3 ^ 40 * 285159 * 2
def baseEnd_285159 : Nat := 130154337738271153600963

theorem tailTrace_285159 : CollatzResearch.WordTrace tailWord_285159 prefixEnd_285159 130154337738271153600963 := by
  unfold tailWord_285159
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400603173925119125002531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6933735449283412750001687 10400603173925119125002531)
  ·
    refine ⟨15600904760887678687503797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400603173925119125002531 15600904760887678687503797)
    ·
      refine ⟨1462584821333219876953481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15600904760887678687503797 1462584821333219876953481)
      ·
        refine ⟨1096938615999914907715111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1462584821333219876953481 1096938615999914907715111)
        ·
          refine ⟨1645407923999872361572667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096938615999914907715111 1645407923999872361572667)
          ·
            refine ⟨2468111885999808542359001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645407923999872361572667 2468111885999808542359001)
            ·
              refine ⟨1851083914499856406769251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468111885999808542359001 1851083914499856406769251)
              ·
                refine ⟨2776625871749784610153877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1851083914499856406769251 2776625871749784610153877)
                ·
                  refine ⟨130154337738271153600963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2776625871749784610153877 130154337738271153600963)
                  ·
                    rfl

theorem cell20_285159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_285159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285159 prefixEnd_285159 := by exact prefixLift 285159
  have htrace : WordTrace (prefixWord ++ tailWord_285159) baseStart_285159 baseEnd_285159 := by
    simpa [prefixWord, tailWord_285159, baseEnd_285159] using wordTrace_append hprefix tailTrace_285159
  have hstable : (prefixWord ++ tailWord_285159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285159).length < 2 ^ (prefixWord ++ tailWord_285159).sum := by decide
  have hdescent : baseEnd_285159 < baseStart_285159 := by decide
  rcases family_descends (prefixWord ++ tailWord_285159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285176 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 2]
def baseStart_285176 : Nat := 118140960795 + 285176 * 2 ^ 59
def prefixEnd_285176 : Nat := 4983230072969 + 3 ^ 40 * 285176 * 2
def baseEnd_285176 : Nat := 130162097001494650034227

theorem tailTrace_285176 : CollatzResearch.WordTrace tailWord_285176 prefixEnd_285176 130162097001494650034227 := by
  unfold tailWord_285176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5200611607431765514185691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6934148809909020685580921 5200611607431765514185691)
  ·
    refine ⟨7800917411147648271278537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5200611607431765514185691 7800917411147648271278537)
    ·
      refine ⟨5850688058360736203458903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7800917411147648271278537 5850688058360736203458903)
      ·
        refine ⟨8776032087541104305188355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850688058360736203458903 8776032087541104305188355)
        ·
          refine ⟨13164048131311656457782533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8776032087541104305188355 13164048131311656457782533)
          ·
            refine ⟨2468259024620935585834225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13164048131311656457782533 2468259024620935585834225)
            ·
              refine ⟨1851194268465701689375669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468259024620935585834225 1851194268465701689375669)
              ·
                refine ⟨173549462668659533378969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1851194268465701689375669 173549462668659533378969)
                ·
                  refine ⟨130162097001494650034227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173549462668659533378969 130162097001494650034227)
                  ·
                    rfl

theorem cell20_285176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_285176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285176 prefixEnd_285176 := by exact prefixLift 285176
  have htrace : WordTrace (prefixWord ++ tailWord_285176) baseStart_285176 baseEnd_285176 := by
    simpa [prefixWord, tailWord_285176, baseEnd_285176] using wordTrace_append hprefix tailTrace_285176
  have hstable : (prefixWord ++ tailWord_285176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285176).length < 2 ^ (prefixWord ++ tailWord_285176).sum := by decide
  have hdescent : baseEnd_285176 < baseStart_285176 := by decide
  rcases family_descends (prefixWord ++ tailWord_285176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285242 : List Nat := [3, 1, 1, 1, 3, 4, 7]
def baseStart_285242 : Nat := 118140960795 + 285242 * 2 ^ 59
def prefixEnd_285242 : Nat := 4983230072969 + 3 ^ 40 * 285242 * 2
def baseEnd_285242 : Nat := 14465802355543528203773

theorem tailTrace_285242 : CollatzResearch.WordTrace tailWord_285242 prefixEnd_285242 14465802355543528203773 := by
  unfold tailWord_285242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600907608156106075068495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6935753621749616200182653 2600907608156106075068495)
  ·
    refine ⟨3901361412234159112602743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2600907608156106075068495 3901361412234159112602743)
    ·
      refine ⟨5852042118351238668904115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3901361412234159112602743 5852042118351238668904115)
      ·
        refine ⟨8778063177526858003356173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852042118351238668904115 8778063177526858003356173)
        ·
          refine ⟨3291773691572571751258565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8778063177526858003356173 3291773691572571751258565)
          ·
            refine ⟨617207567169857203360981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3291773691572571751258565 617207567169857203360981)
            ·
              refine ⟨14465802355543528203773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 617207567169857203360981 14465802355543528203773)
              ·
                rfl

theorem cell20_285242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_285242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285242 prefixEnd_285242 := by exact prefixLift 285242
  have htrace : WordTrace (prefixWord ++ tailWord_285242) baseStart_285242 baseEnd_285242 := by
    simpa [prefixWord, tailWord_285242, baseEnd_285242] using wordTrace_append hprefix tailTrace_285242
  have hstable : (prefixWord ++ tailWord_285242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285242).length < 2 ^ (prefixWord ++ tailWord_285242).sum := by decide
  have hdescent : baseEnd_285242 < baseStart_285242 := by decide
  rcases family_descends (prefixWord ++ tailWord_285242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285245 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 3]
def baseStart_285245 : Nat := 118140960795 + 285245 * 2 ^ 59
def prefixEnd_285245 : Nat := 4983230072969 + 3 ^ 40 * 285245 * 2
def baseEnd_285245 : Nat := 130193590481637076733945

theorem tailTrace_285245 : CollatzResearch.WordTrace tailWord_285245 prefixEnd_285245 130193590481637076733945 := by
  unfold tailWord_285245
  simp only [CollatzResearch.WordTrace]
  refine ⟨10403739851613555812633189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6935826567742370541755459 10403739851613555812633189)
  ·
    refine ⟨1950701222177541714868723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10403739851613555812633189 1950701222177541714868723)
    ·
      refine ⟨2926051833266312572303085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1950701222177541714868723 2926051833266312572303085)
      ·
        refine ⟨1097269437474867214613657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2926051833266312572303085 1097269437474867214613657)
        ·
          refine ⟨822952078106150410960243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1097269437474867214613657 822952078106150410960243)
          ·
            refine ⟨1234428117159225616440365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 822952078106150410960243 1234428117159225616440365)
            ·
              refine ⟨462910543934709606165137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1234428117159225616440365 462910543934709606165137)
              ·
                refine ⟨347182907951032204623853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 462910543934709606165137 347182907951032204623853)
                ·
                  refine ⟨130193590481637076733945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347182907951032204623853 130193590481637076733945)
                  ·
                    rfl

theorem cell20_285245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_285245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285245 prefixEnd_285245 := by exact prefixLift 285245
  have htrace : WordTrace (prefixWord ++ tailWord_285245) baseStart_285245 baseEnd_285245 := by
    simpa [prefixWord, tailWord_285245, baseEnd_285245] using wordTrace_append hprefix tailTrace_285245
  have hstable : (prefixWord ++ tailWord_285245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285245).length < 2 ^ (prefixWord ++ tailWord_285245).sum := by decide
  have hdescent : baseEnd_285245 < baseStart_285245 := by decide
  rcases family_descends (prefixWord ++ tailWord_285245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285282 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 2]
def baseStart_285282 : Nat := 118140960795 + 285282 * 2 ^ 59
def prefixEnd_285282 : Nat := 4983230072969 + 3 ^ 40 * 285282 * 2
def baseEnd_285282 : Nat := 130210478289829392500461

theorem tailTrace_285282 : CollatzResearch.WordTrace tailWord_285282 prefixEnd_285282 130210478289829392500461 := by
  unfold tailWord_285282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2601272338119877782932525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6936726234986340754486733 2601272338119877782932525)
  ·
    refine ⟨975477126794954168599697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2601272338119877782932525 975477126794954168599697)
    ·
      refine ⟨731607845096215626449773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 975477126794954168599697 731607845096215626449773)
      ·
        refine ⟨274352941911080859918665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 731607845096215626449773 274352941911080859918665)
        ·
          refine ⟨205764706433310644938999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274352941911080859918665 205764706433310644938999)
          ·
            refine ⟨308647059649965967408499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205764706433310644938999 308647059649965967408499)
            ·
              refine ⟨462970589474948951112749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308647059649965967408499 462970589474948951112749)
              ·
                refine ⟨173613971053105856667281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462970589474948951112749 173613971053105856667281)
                ·
                  refine ⟨130210478289829392500461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173613971053105856667281 130210478289829392500461)
                  ·
                    rfl

theorem cell20_285282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_285282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285282 prefixEnd_285282 := by exact prefixLift 285282
  have htrace : WordTrace (prefixWord ++ tailWord_285282) baseStart_285282 baseEnd_285282 := by
    simpa [prefixWord, tailWord_285282, baseEnd_285282] using wordTrace_append hprefix tailTrace_285282
  have hstable : (prefixWord ++ tailWord_285282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285282).length < 2 ^ (prefixWord ++ tailWord_285282).sum := by decide
  have hdescent : baseEnd_285282 < baseStart_285282 := by decide
  rcases family_descends (prefixWord ++ tailWord_285282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285373 : List Nat := [1, 4, 1, 2, 1, 5, 1, 5]
def baseStart_285373 : Nat := 118140960795 + 285373 * 2 ^ 59
def prefixEnd_285373 : Nat := 4983230072969 + 3 ^ 40 * 285373 * 2
def baseEnd_285373 : Nat := 43417337723145840155585

theorem tailTrace_285373 : CollatzResearch.WordTrace tailWord_285373 prefixEnd_285373 43417337723145840155585 := by
  unfold tailWord_285373
  simp only [CollatzResearch.WordTrace]
  refine ⟨10408408395149833673292773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6938938930099889115528515 10408408395149833673292773)
  ·
    refine ⟨1951576574090593813742395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10408408395149833673292773 1951576574090593813742395)
    ·
      refine ⟨2927364861135890720613593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951576574090593813742395 2927364861135890720613593)
      ·
        refine ⟨2195523645851918040460195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2927364861135890720613593 2195523645851918040460195)
        ·
          refine ⟨3293285468777877060690293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195523645851918040460195 3293285468777877060690293)
          ·
            refine ⟨308745512697925974439715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3293285468777877060690293 308745512697925974439715)
            ·
              refine ⟨463118269046888961659573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308745512697925974439715 463118269046888961659573)
              ·
                refine ⟨43417337723145840155585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 463118269046888961659573 43417337723145840155585)
                ·
                  rfl

theorem cell20_285373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_285373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285373 prefixEnd_285373 := by exact prefixLift 285373
  have htrace : WordTrace (prefixWord ++ tailWord_285373) baseStart_285373 baseEnd_285373 := by
    simpa [prefixWord, tailWord_285373, baseEnd_285373] using wordTrace_append hprefix tailTrace_285373
  have hstable : (prefixWord ++ tailWord_285373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285373).length < 2 ^ (prefixWord ++ tailWord_285373).sum := by decide
  have hdescent : baseEnd_285373 < baseStart_285373 := by decide
  rcases family_descends (prefixWord ++ tailWord_285373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285401 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 5]
def baseStart_285401 : Nat := 118140960795 + 285401 * 2 ^ 59
def prefixEnd_285401 : Nat := 4983230072969 + 3 ^ 40 * 285401 * 2
def baseEnd_285401 : Nat := 130264793132393867533307

theorem tailTrace_285401 : CollatzResearch.WordTrace tailWord_285401 prefixEnd_285401 130264793132393867533307 := by
  unfold tailWord_285401
  simp only [CollatzResearch.WordTrace]
  refine ⟨10409429639048394455312057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6939619759365596303541371 10409429639048394455312057)
  ·
    refine ⟨7807072229286295841484043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10409429639048394455312057 7807072229286295841484043)
    ·
      refine ⟨11710608343929443762226065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807072229286295841484043 11710608343929443762226065)
      ·
        refine ⟨8782956257947082821669549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11710608343929443762226065 8782956257947082821669549)
        ·
          refine ⟨3293608596730156058126081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8782956257947082821669549 3293608596730156058126081)
          ·
            refine ⟨2470206447547617043594561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293608596730156058126081 2470206447547617043594561)
            ·
              refine ⟨1852654835660712782695921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2470206447547617043594561 1852654835660712782695921)
              ·
                refine ⟨1389491126745534587021941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1852654835660712782695921 1389491126745534587021941)
                ·
                  refine ⟨130264793132393867533307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389491126745534587021941 130264793132393867533307)
                  ·
                    rfl

theorem cell20_285401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_285401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285401 prefixEnd_285401 := by exact prefixLift 285401
  have htrace : WordTrace (prefixWord ++ tailWord_285401) baseStart_285401 baseEnd_285401 := by
    simpa [prefixWord, tailWord_285401, baseEnd_285401] using wordTrace_append hprefix tailTrace_285401
  have hstable : (prefixWord ++ tailWord_285401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285401).length < 2 ^ (prefixWord ++ tailWord_285401).sum := by decide
  have hdescent : baseEnd_285401 < baseStart_285401 := by decide
  rcases family_descends (prefixWord ++ tailWord_285401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285408 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_285408 : Nat := 118140960795 + 285408 * 2 ^ 59
def prefixEnd_285408 : Nat := 4983230072969 + 3 ^ 40 * 285408 * 2
def baseEnd_285408 : Nat := 130267988123132954299945

theorem tailTrace_285408 : CollatzResearch.WordTrace tailWord_285408 prefixEnd_285408 130267988123132954299945 := by
  unfold tailWord_285408
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204842475011517325408439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6939789966682023100544585 5204842475011517325408439)
  ·
    refine ⟨7807263712517275988112659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5204842475011517325408439 7807263712517275988112659)
    ·
      refine ⟨11710895568775913982168989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807263712517275988112659 11710895568775913982168989)
      ·
        refine ⟨4391585838290967743313371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11710895568775913982168989 4391585838290967743313371)
        ·
          refine ⟨6587378757436451614970057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391585838290967743313371 6587378757436451614970057)
          ·
            refine ⟨4940534068077338711227543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6587378757436451614970057 4940534068077338711227543)
            ·
              refine ⟨7410801102116008066841315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940534068077338711227543 7410801102116008066841315)
              ·
                refine ⟨11116201653174012100261973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7410801102116008066841315 11116201653174012100261973)
                ·
                  refine ⟨130267988123132954299945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11116201653174012100261973 130267988123132954299945)
                  ·
                    rfl

theorem cell20_285408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_285408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285408 prefixEnd_285408 := by exact prefixLift 285408
  have htrace : WordTrace (prefixWord ++ tailWord_285408) baseStart_285408 baseEnd_285408 := by
    simpa [prefixWord, tailWord_285408, baseEnd_285408] using wordTrace_append hprefix tailTrace_285408
  have hstable : (prefixWord ++ tailWord_285408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285408).length < 2 ^ (prefixWord ++ tailWord_285408).sum := by decide
  have hdescent : baseEnd_285408 < baseStart_285408 := by decide
  rcases family_descends (prefixWord ++ tailWord_285408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285425 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 4]
def baseStart_285425 : Nat := 118140960795 + 285425 * 2 ^ 59
def prefixEnd_285425 : Nat := 4983230072969 + 3 ^ 40 * 285425 * 2
def baseEnd_285425 : Nat := 130275747386356450733209

theorem tailTrace_285425 : CollatzResearch.WordTrace tailWord_285425 prefixEnd_285425 130275747386356450733209 := by
  unfold tailWord_285425
  simp only [CollatzResearch.WordTrace]
  refine ⟨10410304990961446554185729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6940203327307631036123819 10410304990961446554185729)
  ·
    refine ⟨7807728743221084915639297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10410304990961446554185729 7807728743221084915639297)
    ·
      refine ⟨5855796557415813686729473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7807728743221084915639297 5855796557415813686729473)
      ·
        refine ⟨4391847418061860265047105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5855796557415813686729473 4391847418061860265047105)
        ·
          refine ⟨3293885563546395198785329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4391847418061860265047105 3293885563546395198785329)
          ·
            refine ⟨2470414172659796399088997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293885563546395198785329 2470414172659796399088997)
            ·
              refine ⟨463202657373711824829187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2470414172659796399088997 463202657373711824829187)
              ·
                refine ⟨694803986060567737243781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463202657373711824829187 694803986060567737243781)
                ·
                  refine ⟨130275747386356450733209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694803986060567737243781 130275747386356450733209)
                  ·
                    rfl

theorem cell20_285425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_285425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285425 prefixEnd_285425 := by exact prefixLift 285425
  have htrace : WordTrace (prefixWord ++ tailWord_285425) baseStart_285425 baseEnd_285425 := by
    simpa [prefixWord, tailWord_285425, baseEnd_285425] using wordTrace_append hprefix tailTrace_285425
  have hstable : (prefixWord ++ tailWord_285425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285425).length < 2 ^ (prefixWord ++ tailWord_285425).sum := by decide
  have hdescent : baseEnd_285425 < baseStart_285425 := by decide
  rcases family_descends (prefixWord ++ tailWord_285425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285442 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_285442 : Nat := 118140960795 + 285442 * 2 ^ 59
def prefixEnd_285442 : Nat := 4983230072969 + 3 ^ 40 * 285442 * 2
def baseEnd_285442 : Nat := 130283506649579947166473

theorem tailTrace_285442 : CollatzResearch.WordTrace tailWord_285442 prefixEnd_285442 130283506649579947166473 := by
  unfold tailWord_285442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602731257974964614388645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6940616687933238971703053 2602731257974964614388645)
  ·
    refine ⟨488012110870305865197871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2602731257974964614388645 488012110870305865197871)
    ·
      refine ⟨732018166305458797796807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 488012110870305865197871 732018166305458797796807)
      ·
        refine ⟨1098027249458188196695211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732018166305458797796807 1098027249458188196695211)
        ·
          refine ⟨1647040874187282295042817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098027249458188196695211 1647040874187282295042817)
          ·
            refine ⟨1235280655640461721282113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1647040874187282295042817 1235280655640461721282113)
            ·
              refine ⟨926460491730346290961585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1235280655640461721282113 926460491730346290961585)
              ·
                refine ⟨694845368797759718221189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926460491730346290961585 694845368797759718221189)
                ·
                  refine ⟨130283506649579947166473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 694845368797759718221189 130283506649579947166473)
                  ·
                    rfl

theorem cell20_285442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_285442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285442 prefixEnd_285442 := by exact prefixLift 285442
  have htrace : WordTrace (prefixWord ++ tailWord_285442) baseStart_285442 baseEnd_285442 := by
    simpa [prefixWord, tailWord_285442, baseEnd_285442] using wordTrace_append hprefix tailTrace_285442
  have hstable : (prefixWord ++ tailWord_285442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285442).length < 2 ^ (prefixWord ++ tailWord_285442).sum := by decide
  have hdescent : baseEnd_285442 < baseStart_285442 := by decide
  rcases family_descends (prefixWord ++ tailWord_285442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285476 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 2]
def baseStart_285476 : Nat := 118140960795 + 285476 * 2 ^ 59
def prefixEnd_285476 : Nat := 4983230072969 + 3 ^ 40 * 285476 * 2
def baseEnd_285476 : Nat := 130299025176026940033001

theorem tailTrace_285476 : CollatzResearch.WordTrace tailWord_285476 prefixEnd_285476 130299025176026940033001 := by
  unfold tailWord_285476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5206082556888341132146141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6941443409184454842861521 5206082556888341132146141)
  ·
    refine ⟨1952280958833127924554803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5206082556888341132146141 1952280958833127924554803)
    ·
      refine ⟨2928421438249691886832205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952280958833127924554803 2928421438249691886832205)
      ·
        refine ⟨1098158039343634457562077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2928421438249691886832205 1098158039343634457562077)
        ·
          refine ⟨411809264753862921585779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1098158039343634457562077 411809264753862921585779)
          ·
            refine ⟨617713897130794382378669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411809264753862921585779 617713897130794382378669)
            ·
              refine ⟨231642711424047893392001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 617713897130794382378669 231642711424047893392001)
              ·
                refine ⟨173732033568035920044001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231642711424047893392001 173732033568035920044001)
                ·
                  refine ⟨130299025176026940033001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173732033568035920044001 130299025176026940033001)
                  ·
                    rfl

theorem cell20_285476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_285476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285476 prefixEnd_285476 := by exact prefixLift 285476
  have htrace : WordTrace (prefixWord ++ tailWord_285476) baseStart_285476 baseEnd_285476 := by
    simpa [prefixWord, tailWord_285476, baseEnd_285476] using wordTrace_append hprefix tailTrace_285476
  have hstable : (prefixWord ++ tailWord_285476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285476).length < 2 ^ (prefixWord ++ tailWord_285476).sum := by decide
  have hdescent : baseEnd_285476 < baseStart_285476 := by decide
  rcases family_descends (prefixWord ++ tailWord_285476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285477 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_285477 : Nat := 118140960795 + 285477 * 2 ^ 59
def prefixEnd_285477 : Nat := 4983230072969 + 3 ^ 40 * 285477 * 2
def baseEnd_285477 : Nat := 130299481603275380999663

theorem tailTrace_285477 : CollatzResearch.WordTrace tailWord_285477 prefixEnd_285477 130299481603275380999663 := by
  unfold tailWord_285477
  simp only [CollatzResearch.WordTrace]
  refine ⟨10412201586773059435078685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6941467724515372956719123 10412201586773059435078685)
  ·
    refine ⟨3904575595039897288154507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10412201586773059435078685 3904575595039897288154507)
    ·
      refine ⟨5856863392559845932231761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904575595039897288154507 5856863392559845932231761)
      ·
        refine ⟨4392647544419884449173821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5856863392559845932231761 4392647544419884449173821)
        ·
          refine ⟨1647242829157456668440183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4392647544419884449173821 1647242829157456668440183)
          ·
            refine ⟨2470864243736185002660275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647242829157456668440183 2470864243736185002660275)
            ·
              refine ⟨3706296365604277503990413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470864243736185002660275 3706296365604277503990413)
              ·
                refine ⟨1389861137101604063996405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3706296365604277503990413 1389861137101604063996405)
                ·
                  refine ⟨130299481603275380999663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1389861137101604063996405 130299481603275380999663)
                  ·
                    rfl

theorem cell20_285477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_285477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285477 prefixEnd_285477 := by exact prefixLift 285477
  have htrace : WordTrace (prefixWord ++ tailWord_285477) baseStart_285477 baseEnd_285477 := by
    simpa [prefixWord, tailWord_285477, baseEnd_285477] using wordTrace_append hprefix tailTrace_285477
  have hstable : (prefixWord ++ tailWord_285477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285477).length < 2 ^ (prefixWord ++ tailWord_285477).sum := by decide
  have hdescent : baseEnd_285477 < baseStart_285477 := by decide
  rcases family_descends (prefixWord ++ tailWord_285477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285529 : List Nat := [1, 2, 1, 2, 2, 12]
def baseStart_285529 : Nat := 118140960795 + 285529 * 2 ^ 59
def prefixEnd_285529 : Nat := 4983230072969 + 3 ^ 40 * 285529 * 2
def baseEnd_285529 : Nat := 4826785771118307824671

theorem tailTrace_285529 : CollatzResearch.WordTrace tailWord_285529 prefixEnd_285529 4826785771118307824671 := by
  unfold tailWord_285529
  simp only [CollatzResearch.WordTrace]
  refine ⟨10414098182584672315971641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6942732121723114877314427 10414098182584672315971641)
  ·
    refine ⟨7810573636938504236978731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10414098182584672315971641 7810573636938504236978731)
    ·
      refine ⟨11715860455407756355468097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7810573636938504236978731 11715860455407756355468097)
      ·
        refine ⟨8786895341555817266601073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11715860455407756355468097 8786895341555817266601073)
        ·
          refine ⟨6590171506166862949950805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8786895341555817266601073 6590171506166862949950805)
          ·
            refine ⟨4826785771118307824671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6590171506166862949950805 4826785771118307824671)
            ·
              rfl

theorem cell20_285529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 12].length) (baseStart_285529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285529 prefixEnd_285529 := by exact prefixLift 285529
  have htrace : WordTrace (prefixWord ++ tailWord_285529) baseStart_285529 baseEnd_285529 := by
    simpa [prefixWord, tailWord_285529, baseEnd_285529] using wordTrace_append hprefix tailTrace_285529
  have hstable : (prefixWord ++ tailWord_285529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285529).length < 2 ^ (prefixWord ++ tailWord_285529).sum := by decide
  have hdescent : baseEnd_285529 < baseStart_285529 := by decide
  rcases family_descends (prefixWord ++ tailWord_285529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285567 : List Nat := [1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_285567 : Nat := 118140960795 + 285567 * 2 ^ 59
def prefixEnd_285567 : Nat := 4983230072969 + 3 ^ 40 * 285567 * 2
def baseEnd_285567 : Nat := 43446853351878355999765

theorem tailTrace_285567 : CollatzResearch.WordTrace tailWord_285567 prefixEnd_285567 43446853351878355999765 := by
  unfold tailWord_285567
  simp only [CollatzResearch.WordTrace]
  refine ⟨10415484156447004805854955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6943656104298003203903303 10415484156447004805854955)
  ·
    refine ⟨15623226234670507208782433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10415484156447004805854955 15623226234670507208782433)
    ·
      refine ⟨11717419676002880406586825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15623226234670507208782433 11717419676002880406586825)
      ·
        refine ⟨8788064757002160304940119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11717419676002880406586825 8788064757002160304940119)
        ·
          refine ⟨13182097135503240457410179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8788064757002160304940119 13182097135503240457410179)
          ·
            refine ⟨19773145703254860686115269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13182097135503240457410179 19773145703254860686115269)
            ·
              refine ⟨3707464819360286378646613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19773145703254860686115269 3707464819360286378646613)
              ·
                refine ⟨43446853351878355999765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3707464819360286378646613 43446853351878355999765)
                ·
                  rfl

theorem cell20_285567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_285567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285567 prefixEnd_285567 := by exact prefixLift 285567
  have htrace : WordTrace (prefixWord ++ tailWord_285567) baseStart_285567 baseEnd_285567 := by
    simpa [prefixWord, tailWord_285567, baseEnd_285567] using wordTrace_append hprefix tailTrace_285567
  have hstable : (prefixWord ++ tailWord_285567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285567).length < 2 ^ (prefixWord ++ tailWord_285567).sum := by decide
  have hdescent : baseEnd_285567 < baseStart_285567 := by decide
  rcases family_descends (prefixWord ++ tailWord_285567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285590 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_285590 : Nat := 118140960795 + 285590 * 2 ^ 59
def prefixEnd_285590 : Nat := 4983230072969 + 3 ^ 40 * 285590 * 2
def baseEnd_285590 : Nat := 130351057882349210232535

theorem tailTrace_285590 : CollatzResearch.WordTrace tailWord_285590 prefixEnd_285590 130351057882349210232535 := by
  unfold tailWord_285590
  simp only [CollatzResearch.WordTrace]
  refine ⟨651020189710229983371389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6944215356909119822628149 651020189710229983371389)
  ·
    refine ⟨244132571141336243764271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 651020189710229983371389 244132571141336243764271)
    ·
      refine ⟨366198856712004365646407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244132571141336243764271 366198856712004365646407)
      ·
        refine ⟨549298285068006548469611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366198856712004365646407 549298285068006548469611)
        ·
          refine ⟨823947427602009822704417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549298285068006548469611 823947427602009822704417)
          ·
            refine ⟨617960570701507367028313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823947427602009822704417 617960570701507367028313)
            ·
              refine ⟨463470428026130525271235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617960570701507367028313 463470428026130525271235)
              ·
                refine ⟨695205642039195787906853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463470428026130525271235 695205642039195787906853)
                ·
                  refine ⟨130351057882349210232535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695205642039195787906853 130351057882349210232535)
                  ·
                    rfl

theorem cell20_285590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_285590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285590 prefixEnd_285590 := by exact prefixLift 285590
  have htrace : WordTrace (prefixWord ++ tailWord_285590) baseStart_285590 baseEnd_285590 := by
    simpa [prefixWord, tailWord_285590, baseEnd_285590] using wordTrace_append hprefix tailTrace_285590
  have hstable : (prefixWord ++ tailWord_285590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285590).length < 2 ^ (prefixWord ++ tailWord_285590).sum := by decide
  have hdescent : baseEnd_285590 < baseStart_285590 := by decide
  rcases family_descends (prefixWord ++ tailWord_285590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285591 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_285591 : Nat := 118140960795 + 285591 * 2 ^ 59
def prefixEnd_285591 : Nat := 4983230072969 + 3 ^ 40 * 285591 * 2
def baseEnd_285591 : Nat := 130351514309597651199197

theorem tailTrace_285591 : CollatzResearch.WordTrace tailWord_285591 prefixEnd_285591 130351514309597651199197 := by
  unfold tailWord_285591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416359508360056904728627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6944239672240037936485751 10416359508360056904728627)
  ·
    refine ⟨15624539262540085357092941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10416359508360056904728627 15624539262540085357092941)
    ·
      refine ⟨5859202223452532008909853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15624539262540085357092941 5859202223452532008909853)
      ·
        refine ⟨2197200833794699503341195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5859202223452532008909853 2197200833794699503341195)
        ·
          refine ⟨3295801250692049255011793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197200833794699503341195 3295801250692049255011793)
          ·
            refine ⟨2471850938019036941258845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295801250692049255011793 2471850938019036941258845)
            ·
              refine ⟨926944101757138852972067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2471850938019036941258845 926944101757138852972067)
              ·
                refine ⟨1390416152635708279458101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 926944101757138852972067 1390416152635708279458101)
                ·
                  refine ⟨130351514309597651199197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1390416152635708279458101 130351514309597651199197)
                  ·
                    rfl

theorem cell20_285591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_285591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285591 prefixEnd_285591 := by exact prefixLift 285591
  have htrace : WordTrace (prefixWord ++ tailWord_285591) baseStart_285591 baseEnd_285591 := by
    simpa [prefixWord, tailWord_285591, baseEnd_285591] using wordTrace_append hprefix tailTrace_285591
  have hstable : (prefixWord ++ tailWord_285591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285591).length < 2 ^ (prefixWord ++ tailWord_285591).sum := by decide
  have hdescent : baseEnd_285591 < baseStart_285591 := by decide
  rcases family_descends (prefixWord ++ tailWord_285591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285594 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_285594 : Nat := 118140960795 + 285594 * 2 ^ 59
def prefixEnd_285594 : Nat := 4983230072969 + 3 ^ 40 * 285594 * 2
def baseEnd_285594 : Nat := 130352883591342974099185

theorem tailTrace_285594 : CollatzResearch.WordTrace tailWord_285594 prefixEnd_285594 130352883591342974099185 := by
  unfold tailWord_285594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604117231837297104271959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6944312618232792278058557 2604117231837297104271959)
  ·
    refine ⟨3906175847755945656407939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2604117231837297104271959 3906175847755945656407939)
    ·
      refine ⟨5859263771633918484611909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3906175847755945656407939 5859263771633918484611909)
      ·
        refine ⟨1098611957181359715864733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5859263771633918484611909 1098611957181359715864733)
        ·
          refine ⟨411979483943009893449275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1098611957181359715864733 411979483943009893449275)
          ·
            refine ⟨617969225914514840173913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411979483943009893449275 617969225914514840173913)
            ·
              refine ⟨463476919435886130130435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617969225914514840173913 463476919435886130130435)
              ·
                refine ⟨695215379153829195195653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463476919435886130130435 695215379153829195195653)
                ·
                  refine ⟨130352883591342974099185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695215379153829195195653 130352883591342974099185)
                  ·
                    rfl

theorem cell20_285594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_285594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285594 prefixEnd_285594 := by exact prefixLift 285594
  have htrace : WordTrace (prefixWord ++ tailWord_285594) baseStart_285594 baseEnd_285594 := by
    simpa [prefixWord, tailWord_285594, baseEnd_285594] using wordTrace_append hprefix tailTrace_285594
  have hstable : (prefixWord ++ tailWord_285594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285594).length < 2 ^ (prefixWord ++ tailWord_285594).sum := by decide
  have hdescent : baseEnd_285594 < baseStart_285594 := by decide
  rcases family_descends (prefixWord ++ tailWord_285594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285632 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 2]
def baseStart_285632 : Nat := 118140960795 + 285632 * 2 ^ 59
def prefixEnd_285632 : Nat := 4983230072969 + 3 ^ 40 * 285632 * 2
def baseEnd_285632 : Nat := 130370227826783730832363

theorem tailTrace_285632 : CollatzResearch.WordTrace tailWord_285632 prefixEnd_285632 130370227826783730832363 := by
  unfold tailWord_285632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208927450605760453485575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6945236600807680604647433 5208927450605760453485575)
  ·
    refine ⟨7813391175908640680228363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5208927450605760453485575 7813391175908640680228363)
    ·
      refine ⟨11720086763862961020342545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7813391175908640680228363 11720086763862961020342545)
      ·
        refine ⟨8790065072897220765256909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11720086763862961020342545 8790065072897220765256909)
        ·
          refine ⟨3296274402336457786971341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8790065072897220765256909 3296274402336457786971341)
          ·
            refine ⟨1236102900876171670114253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3296274402336457786971341 1236102900876171670114253)
            ·
              refine ⟨463538587828564376292845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236102900876171670114253 463538587828564376292845)
              ·
                refine ⟨173826970435711641109817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463538587828564376292845 173826970435711641109817)
                ·
                  refine ⟨130370227826783730832363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173826970435711641109817 130370227826783730832363)
                  ·
                    rfl

theorem cell20_285632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_285632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285632 prefixEnd_285632 := by exact prefixLift 285632
  have htrace : WordTrace (prefixWord ++ tailWord_285632) baseStart_285632 baseEnd_285632 := by
    simpa [prefixWord, tailWord_285632, baseEnd_285632] using wordTrace_append hprefix tailTrace_285632
  have hstable : (prefixWord ++ tailWord_285632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285632).length < 2 ^ (prefixWord ++ tailWord_285632).sum := by decide
  have hdescent : baseEnd_285632 < baseStart_285632 := by decide
  rcases family_descends (prefixWord ++ tailWord_285632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285643 : List Nat := [1, 1, 1, 1, 3, 5, 8]
def baseStart_285643 : Nat := 118140960795 + 285643 * 2 ^ 59
def prefixEnd_285643 : Nat := 4983230072969 + 3 ^ 40 * 285643 * 2
def baseEnd_285643 : Nat := 14486138725168509051739

theorem tailTrace_285643 : CollatzResearch.WordTrace tailWord_285643 prefixEnd_285643 14486138725168509051739 := by
  unfold tailWord_285643
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418256104171669785621583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6945504069447779857081055 10418256104171669785621583)
  ·
    refine ⟨15627384156257504678432375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10418256104171669785621583 15627384156257504678432375)
    ·
      refine ⟨23441076234386257017648563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15627384156257504678432375 23441076234386257017648563)
      ·
        refine ⟨35161614351579385526472845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23441076234386257017648563 35161614351579385526472845)
        ·
          refine ⟨13185605381842269572427317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35161614351579385526472845 13185605381842269572427317)
          ·
            refine ⟨1236150504547712772415061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13185605381842269572427317 1236150504547712772415061)
            ·
              refine ⟨14486138725168509051739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1236150504547712772415061 14486138725168509051739)
              ·
                rfl

theorem cell20_285643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_285643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285643 prefixEnd_285643 := by exact prefixLift 285643
  have htrace : WordTrace (prefixWord ++ tailWord_285643) baseStart_285643 baseEnd_285643 := by
    simpa [prefixWord, tailWord_285643, baseEnd_285643] using wordTrace_append hprefix tailTrace_285643
  have hstable : (prefixWord ++ tailWord_285643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285643).length < 2 ^ (prefixWord ++ tailWord_285643).sum := by decide
  have hdescent : baseEnd_285643 < baseStart_285643 := by decide
  rcases family_descends (prefixWord ++ tailWord_285643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285645 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 4]
def baseStart_285645 : Nat := 118140960795 + 285645 * 2 ^ 59
def prefixEnd_285645 : Nat := 4983230072969 + 3 ^ 40 * 285645 * 2
def baseEnd_285645 : Nat := 130376161381013463398977

theorem tailTrace_285645 : CollatzResearch.WordTrace tailWord_285645 prefixEnd_285645 130376161381013463398977 := by
  unfold tailWord_285645
  simp only [CollatzResearch.WordTrace]
  refine ⟨10418329050164424127194389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6945552700109616084796259 10418329050164424127194389)
  ·
    refine ⟨488359174226457380962237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10418329050164424127194389 488359174226457380962237)
    ·
      refine ⟨183134690334921517860839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 488359174226457380962237 183134690334921517860839)
      ·
        refine ⟨274702035502382276791259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183134690334921517860839 274702035502382276791259)
        ·
          refine ⟨412053053253573415186889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274702035502382276791259 412053053253573415186889)
          ·
            refine ⟨309039789940180061390167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412053053253573415186889 309039789940180061390167)
            ·
              refine ⟨463559684910270092085251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309039789940180061390167 463559684910270092085251)
              ·
                refine ⟨695339527365405138127877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463559684910270092085251 695339527365405138127877)
                ·
                  refine ⟨130376161381013463398977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695339527365405138127877 130376161381013463398977)
                  ·
                    rfl

theorem cell20_285645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_285645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285645 prefixEnd_285645 := by exact prefixLift 285645
  have htrace : WordTrace (prefixWord ++ tailWord_285645) baseStart_285645 baseEnd_285645 := by
    simpa [prefixWord, tailWord_285645, baseEnd_285645] using wordTrace_append hprefix tailTrace_285645
  have hstable : (prefixWord ++ tailWord_285645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285645).length < 2 ^ (prefixWord ++ tailWord_285645).sum := by decide
  have hdescent : baseEnd_285645 < baseStart_285645 := by decide
  rcases family_descends (prefixWord ++ tailWord_285645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285691 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 2]
def baseStart_285691 : Nat := 118140960795 + 285691 * 2 ^ 59
def prefixEnd_285691 : Nat := 4983230072969 + 3 ^ 40 * 285691 * 2
def baseEnd_285691 : Nat := 130397157034441747865455

theorem tailTrace_285691 : CollatzResearch.WordTrace tailWord_285691 prefixEnd_285691 130397157034441747865455 := by
  unfold tailWord_285691
  simp only [CollatzResearch.WordTrace]
  refine ⟨10420006807997773983368927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6946671205331849322245951 10420006807997773983368927)
  ·
    refine ⟨15630010211996660975053391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10420006807997773983368927 15630010211996660975053391)
    ·
      refine ⟨23445015317994991462580087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15630010211996660975053391 23445015317994991462580087)
      ·
        refine ⟨35167522976992487193870131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23445015317994991462580087 35167522976992487193870131)
        ·
          refine ⟨52751284465488730790805197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35167522976992487193870131 52751284465488730790805197)
          ·
            refine ⟨19781731674558274046551949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52751284465488730790805197 19781731674558274046551949)
            ·
              refine ⟨7418149377959352767456981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19781731674558274046551949 7418149377959352767456981)
              ·
                refine ⟨173862876045922330487273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7418149377959352767456981 173862876045922330487273)
                ·
                  refine ⟨130397157034441747865455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173862876045922330487273 130397157034441747865455)
                  ·
                    rfl

theorem cell20_285691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 2].length) (baseStart_285691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285691 prefixEnd_285691 := by exact prefixLift 285691
  have htrace : WordTrace (prefixWord ++ tailWord_285691) baseStart_285691 baseEnd_285691 := by
    simpa [prefixWord, tailWord_285691, baseEnd_285691] using wordTrace_append hprefix tailTrace_285691
  have hstable : (prefixWord ++ tailWord_285691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285691).length < 2 ^ (prefixWord ++ tailWord_285691).sum := by decide
  have hdescent : baseEnd_285691 < baseStart_285691 := by decide
  rcases family_descends (prefixWord ++ tailWord_285691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285708 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 2]
def baseStart_285708 : Nat := 118140960795 + 285708 * 2 ^ 59
def prefixEnd_285708 : Nat := 4983230072969 + 3 ^ 40 * 285708 * 2
def baseEnd_285708 : Nat := 130404916297665244298719

theorem tailTrace_285708 : CollatzResearch.WordTrace tailWord_285708 prefixEnd_285708 130404916297665244298719 := by
  unfold tailWord_285708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5210313424468092943368889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6947084565957457257825185 5210313424468092943368889)
  ·
    refine ⟨3907735068351069707526667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5210313424468092943368889 3907735068351069707526667)
    ·
      refine ⟨5861602602526604561290001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3907735068351069707526667 5861602602526604561290001)
      ·
        refine ⟨4396201951894953420967501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5861602602526604561290001 4396201951894953420967501)
        ·
          refine ⟨1648575731960607532862813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4396201951894953420967501 1648575731960607532862813)
          ·
            refine ⟨618215899485227824823555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1648575731960607532862813 618215899485227824823555)
            ·
              refine ⟨927323849227841737235333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618215899485227824823555 927323849227841737235333)
              ·
                refine ⟨173873221730220325731625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 927323849227841737235333 173873221730220325731625)
                ·
                  refine ⟨130404916297665244298719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173873221730220325731625 130404916297665244298719)
                  ·
                    rfl

theorem cell20_285708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_285708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285708 prefixEnd_285708 := by exact prefixLift 285708
  have htrace : WordTrace (prefixWord ++ tailWord_285708) baseStart_285708 baseEnd_285708 := by
    simpa [prefixWord, tailWord_285708, baseEnd_285708] using wordTrace_append hprefix tailTrace_285708
  have hstable : (prefixWord ++ tailWord_285708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285708).length < 2 ^ (prefixWord ++ tailWord_285708).sum := by decide
  have hdescent : baseEnd_285708 < baseStart_285708 := by decide
  rcases family_descends (prefixWord ++ tailWord_285708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285729 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_285729 : Nat := 118140960795 + 285729 * 2 ^ 59
def prefixEnd_285729 : Nat := 4983230072969 + 3 ^ 40 * 285729 * 2
def baseEnd_285729 : Nat := 130414501269882504598633

theorem tailTrace_285729 : CollatzResearch.WordTrace tailWord_285729 prefixEnd_285729 130414501269882504598633 := by
  unfold tailWord_285729
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421392781860106473252241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6947595187906737648834827 10421392781860106473252241)
  ·
    refine ⟨7816044586395079854939181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10421392781860106473252241 7816044586395079854939181)
    ·
      refine ⟨2931016719898154945602193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7816044586395079854939181 2931016719898154945602193)
      ·
        refine ⟨2198262539923616209201645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2931016719898154945602193 2198262539923616209201645)
        ·
          refine ⟨824348452471356078450617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2198262539923616209201645 824348452471356078450617)
          ·
            refine ⟨618261339353517058837963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 824348452471356078450617 618261339353517058837963)
            ·
              refine ⟨927392009030275588256945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618261339353517058837963 927392009030275588256945)
              ·
                refine ⟨695544006772706691192709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927392009030275588256945 695544006772706691192709)
                ·
                  refine ⟨130414501269882504598633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695544006772706691192709 130414501269882504598633)
                  ·
                    rfl

theorem cell20_285729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_285729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285729 prefixEnd_285729 := by exact prefixLift 285729
  have htrace : WordTrace (prefixWord ++ tailWord_285729) baseStart_285729 baseEnd_285729 := by
    simpa [prefixWord, tailWord_285729, baseEnd_285729] using wordTrace_append hprefix tailTrace_285729
  have hstable : (prefixWord ++ tailWord_285729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285729).length < 2 ^ (prefixWord ++ tailWord_285729).sum := by decide
  have hdescent : baseEnd_285729 < baseStart_285729 := by decide
  rcases family_descends (prefixWord ++ tailWord_285729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285746 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_285746 : Nat := 118140960795 + 285746 * 2 ^ 59
def prefixEnd_285746 : Nat := 4983230072969 + 3 ^ 40 * 285746 * 2
def baseEnd_285746 : Nat := 130422260533106001031897

theorem tailTrace_285746 : CollatzResearch.WordTrace tailWord_285746 prefixEnd_285746 130422260533106001031897 := by
  unfold tailWord_285746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605503205699629594155273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6948008548532345584414061 2605503205699629594155273)
  ·
    refine ⟨1954127404274722195616455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2605503205699629594155273 1954127404274722195616455)
    ·
      refine ⟨2931191106412083293424683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1954127404274722195616455 2931191106412083293424683)
      ·
        refine ⟨4396786659618124940137025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931191106412083293424683 4396786659618124940137025)
        ·
          refine ⟨3297589994713593705102769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4396786659618124940137025 3297589994713593705102769)
          ·
            refine ⟨2473192496035195278827077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297589994713593705102769 2473192496035195278827077)
            ·
              refine ⟨463723593006599114780077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2473192496035195278827077 463723593006599114780077)
              ·
                refine ⟨173896347377474668042529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 463723593006599114780077 173896347377474668042529)
                ·
                  refine ⟨130422260533106001031897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 173896347377474668042529 130422260533106001031897)
                  ·
                    rfl

theorem cell20_285746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_285746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285746 prefixEnd_285746 := by exact prefixLift 285746
  have htrace : WordTrace (prefixWord ++ tailWord_285746) baseStart_285746 baseEnd_285746 := by
    simpa [prefixWord, tailWord_285746, baseEnd_285746] using wordTrace_append hprefix tailTrace_285746
  have hstable : (prefixWord ++ tailWord_285746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285746).length < 2 ^ (prefixWord ++ tailWord_285746).sum := by decide
  have hdescent : baseEnd_285746 < baseStart_285746 := by decide
  rcases family_descends (prefixWord ++ tailWord_285746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285767 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 4]
def baseStart_285767 : Nat := 118140960795 + 285767 * 2 ^ 59
def prefixEnd_285767 : Nat := 4983230072969 + 3 ^ 40 * 285767 * 2
def baseEnd_285767 : Nat := 130431845505323261331811

theorem tailTrace_285767 : CollatzResearch.WordTrace tailWord_285767 prefixEnd_285767 130431845505323261331811 := by
  unfold tailWord_285767
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422778755722438963135555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6948519170481625975423703 10422778755722438963135555)
  ·
    refine ⟨15634168133583658444703333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10422778755722438963135555 15634168133583658444703333)
    ·
      refine ⟨2931406525046935958381875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15634168133583658444703333 2931406525046935958381875)
      ·
        refine ⟨4397109787570403937572813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931406525046935958381875 4397109787570403937572813)
        ·
          refine ⟨1648916170338901476589805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4397109787570403937572813 1648916170338901476589805)
          ·
            refine ⟨618343563877088053721177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1648916170338901476589805 618343563877088053721177)
            ·
              refine ⟨463757672907816040290883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618343563877088053721177 463757672907816040290883)
              ·
                refine ⟨695636509361724060436325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463757672907816040290883 695636509361724060436325)
                ·
                  refine ⟨130431845505323261331811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695636509361724060436325 130431845505323261331811)
                  ·
                    rfl

theorem cell20_285767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_285767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285767 prefixEnd_285767 := by exact prefixLift 285767
  have htrace : WordTrace (prefixWord ++ tailWord_285767) baseStart_285767 baseEnd_285767 := by
    simpa [prefixWord, tailWord_285767, baseEnd_285767] using wordTrace_append hprefix tailTrace_285767
  have hstable : (prefixWord ++ tailWord_285767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285767).length < 2 ^ (prefixWord ++ tailWord_285767).sum := by decide
  have hdescent : baseEnd_285767 < baseStart_285767 := by decide
  rcases family_descends (prefixWord ++ tailWord_285767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285832 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 3]
def baseStart_285832 : Nat := 118140960795 + 285832 * 2 ^ 59
def prefixEnd_285832 : Nat := 4983230072969 + 3 ^ 40 * 285832 * 2
def baseEnd_285832 : Nat := 130461513276471924164879

theorem tailTrace_285832 : CollatzResearch.WordTrace tailWord_285832 prefixEnd_285832 130461513276471924164879 := by
  unfold tailWord_285832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212574750243477532125875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6950099666991303376167833 5212574750243477532125875)
  ·
    refine ⟨7818862125365216298188813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5212574750243477532125875 7818862125365216298188813)
    ·
      refine ⟨2932073297011956111820805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7818862125365216298188813 2932073297011956111820805)
      ·
        refine ⟨549763743189741770966401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2932073297011956111820805 549763743189741770966401)
        ·
          refine ⟨412322807392306328224801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549763743189741770966401 412322807392306328224801)
          ·
            refine ⟨309242105544229746168601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412322807392306328224801 309242105544229746168601)
            ·
              refine ⟨231931579158172309626451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309242105544229746168601 231931579158172309626451)
              ·
                refine ⟨347897368737258464439677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231931579158172309626451 347897368737258464439677)
                ·
                  refine ⟨130461513276471924164879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347897368737258464439677 130461513276471924164879)
                  ·
                    rfl

theorem cell20_285832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_285832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285832 prefixEnd_285832 := by exact prefixLift 285832
  have htrace : WordTrace (prefixWord ++ tailWord_285832) baseStart_285832 baseEnd_285832 := by
    simpa [prefixWord, tailWord_285832, baseEnd_285832] using wordTrace_append hprefix tailTrace_285832
  have hstable : (prefixWord ++ tailWord_285832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285832).length < 2 ^ (prefixWord ++ tailWord_285832).sum := by decide
  have hdescent : baseEnd_285832 < baseStart_285832 := by decide
  rcases family_descends (prefixWord ++ tailWord_285832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285833 : List Nat := [1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_285833 : Nat := 118140960795 + 285833 * 2 ^ 59
def prefixEnd_285833 : Nat := 4983230072969 + 3 ^ 40 * 285833 * 2
def baseEnd_285833 : Nat := 43487323234573455043847

theorem tailTrace_285833 : CollatzResearch.WordTrace tailWord_285833 prefixEnd_285833 43487323234573455043847 := by
  unfold tailWord_285833
  simp only [CollatzResearch.WordTrace]
  refine ⟨10425185973483332235038153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6950123982322221490025435 10425185973483332235038153)
  ·
    refine ⟨7818889480112499176278615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10425185973483332235038153 7818889480112499176278615)
    ·
      refine ⟨11728334220168748764417923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818889480112499176278615 11728334220168748764417923)
      ·
        refine ⟨17592501330253123146626885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11728334220168748764417923 17592501330253123146626885)
        ·
          refine ⟨3298593999422460589992541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17592501330253123146626885 3298593999422460589992541)
          ·
            refine ⟨1236972749783422721247203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3298593999422460589992541 1236972749783422721247203)
            ·
              refine ⟨1855459124675134081870805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236972749783422721247203 1855459124675134081870805)
              ·
                refine ⟨43487323234573455043847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1855459124675134081870805 43487323234573455043847)
                ·
                  rfl

theorem cell20_285833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_285833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285833 prefixEnd_285833 := by exact prefixLift 285833
  have htrace : WordTrace (prefixWord ++ tailWord_285833) baseStart_285833 baseEnd_285833 := by
    simpa [prefixWord, tailWord_285833, baseEnd_285833] using wordTrace_append hprefix tailTrace_285833
  have hstable : (prefixWord ++ tailWord_285833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285833).length < 2 ^ (prefixWord ++ tailWord_285833).sum := by decide
  have hdescent : baseEnd_285833 < baseStart_285833 := by decide
  rcases family_descends (prefixWord ++ tailWord_285833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285840 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_285840 : Nat := 118140960795 + 285840 * 2 ^ 59
def prefixEnd_285840 : Nat := 4983230072969 + 3 ^ 40 * 285840 * 2
def baseEnd_285840 : Nat := 130465164694459451898179

theorem tailTrace_285840 : CollatzResearch.WordTrace tailWord_285840 prefixEnd_285840 130465164694459451898179 := by
  unfold tailWord_285840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212720642228986215271487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6950294189638648287028649 5212720642228986215271487)
  ·
    refine ⟨7819080963343479322907231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5212720642228986215271487 7819080963343479322907231)
    ·
      refine ⟨11728621445015218984360847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7819080963343479322907231 11728621445015218984360847)
      ·
        refine ⟨17592932167522828476541271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11728621445015218984360847 17592932167522828476541271)
        ·
          refine ⟨26389398251284242714811907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17592932167522828476541271 26389398251284242714811907)
          ·
            refine ⟨39584097376926364072217861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26389398251284242714811907 39584097376926364072217861)
            ·
              refine ⟨7422018258173693263540849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39584097376926364072217861 7422018258173693263540849)
              ·
                refine ⟨5566513693630269947655637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7422018258173693263540849 5566513693630269947655637)
                ·
                  refine ⟨130465164694459451898179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5566513693630269947655637 130465164694459451898179)
                  ·
                    rfl

theorem cell20_285840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_285840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285840 prefixEnd_285840 := by exact prefixLift 285840
  have htrace : WordTrace (prefixWord ++ tailWord_285840) baseStart_285840 baseEnd_285840 := by
    simpa [prefixWord, tailWord_285840, baseEnd_285840] using wordTrace_append hprefix tailTrace_285840
  have hstable : (prefixWord ++ tailWord_285840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285840).length < 2 ^ (prefixWord ++ tailWord_285840).sum := by decide
  have hdescent : baseEnd_285840 < baseStart_285840 := by decide
  rcases family_descends (prefixWord ++ tailWord_285840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285850 : List Nat := [3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_285850 : Nat := 118140960795 + 285850 * 2 ^ 59
def prefixEnd_285850 : Nat := 4983230072969 + 3 ^ 40 * 285850 * 2
def baseEnd_285850 : Nat := 43489909655647953854935

theorem tailTrace_285850 : CollatzResearch.WordTrace tailWord_285850 prefixEnd_285850 43489909655647953854935 := by
  unfold tailWord_285850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606451503605436034601751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6950537342947829425604669 2606451503605436034601751)
  ·
    refine ⟨3909677255408154051902627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2606451503605436034601751 3909677255408154051902627)
    ·
      refine ⟨5864515883112231077853941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909677255408154051902627 5864515883112231077853941)
      ·
        refine ⟨549798364041771663548807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5864515883112231077853941 549798364041771663548807)
        ·
          refine ⟨824697546062657495323211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549798364041771663548807 824697546062657495323211)
          ·
            refine ⟨1237046319093986242984817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824697546062657495323211 1237046319093986242984817)
            ·
              refine ⟨927784739320489682238613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237046319093986242984817 927784739320489682238613)
              ·
                refine ⟨43489909655647953854935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 927784739320489682238613 43489909655647953854935)
                ·
                  rfl

theorem cell20_285850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_285850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285850 prefixEnd_285850 := by exact prefixLift 285850
  have htrace : WordTrace (prefixWord ++ tailWord_285850) baseStart_285850 baseEnd_285850 := by
    simpa [prefixWord, tailWord_285850, baseEnd_285850] using wordTrace_append hprefix tailTrace_285850
  have hstable : (prefixWord ++ tailWord_285850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285850).length < 2 ^ (prefixWord ++ tailWord_285850).sum := by decide
  have hdescent : baseEnd_285850 < baseStart_285850 := by decide
  rcases family_descends (prefixWord ++ tailWord_285850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285874 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_285874 : Nat := 118140960795 + 285874 * 2 ^ 59
def prefixEnd_285874 : Nat := 4983230072969 + 3 ^ 40 * 285874 * 2
def baseEnd_285874 : Nat := 130480683220906444764707

theorem tailTrace_285874 : CollatzResearch.WordTrace tailWord_285874 prefixEnd_285874 130480683220906444764707 := by
  unfold tailWord_285874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606670341583699059320169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6951120910889864158187117 2606670341583699059320169)
  ·
    refine ⟨1955002756187774294490127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2606670341583699059320169 1955002756187774294490127)
    ·
      refine ⟨2932504134281661441735191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955002756187774294490127 2932504134281661441735191)
      ·
        refine ⟨4398756201422492162602787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932504134281661441735191 4398756201422492162602787)
        ·
          refine ⟨6598134302133738243904181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398756201422492162602787 6598134302133738243904181)
          ·
            refine ⟨618575090825037960366017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6598134302133738243904181 618575090825037960366017)
            ·
              refine ⟨463931318118778470274513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618575090825037960366017 463931318118778470274513)
              ·
                refine ⟨347948488589083852705885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463931318118778470274513 347948488589083852705885)
                ·
                  refine ⟨130480683220906444764707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 347948488589083852705885 130480683220906444764707)
                  ·
                    rfl

theorem cell20_285874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_285874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285874 prefixEnd_285874 := by exact prefixLift 285874
  have htrace : WordTrace (prefixWord ++ tailWord_285874) baseStart_285874 baseEnd_285874 := by
    simpa [prefixWord, tailWord_285874, baseEnd_285874] using wordTrace_append hprefix tailTrace_285874
  have hstable : (prefixWord ++ tailWord_285874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285874).length < 2 ^ (prefixWord ++ tailWord_285874).sum := by decide
  have hdescent : baseEnd_285874 < baseStart_285874 := by decide
  rcases family_descends (prefixWord ++ tailWord_285874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285894 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_285894 : Nat := 118140960795 + 285894 * 2 ^ 59
def prefixEnd_285894 : Nat := 4983230072969 + 3 ^ 40 * 285894 * 2
def baseEnd_285894 : Nat := 130489811765875264097959

theorem tailTrace_285894 : CollatzResearch.WordTrace tailWord_285894 prefixEnd_285894 130489811765875264097959 := by
  unfold tailWord_285894
  simp only [CollatzResearch.WordTrace]
  refine ⟨325856588320698114156523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6951607217508226435339157 325856588320698114156523)
  ·
    refine ⟨488784882481047171234785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 325856588320698114156523 488784882481047171234785)
    ·
      refine ⟨366588661860785378426089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 488784882481047171234785 366588661860785378426089)
      ·
        refine ⟨274941496395589033819567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366588661860785378426089 274941496395589033819567)
        ·
          refine ⟨412412244593383550729351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274941496395589033819567 412412244593383550729351)
          ·
            refine ⟨618618366890075326094027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412412244593383550729351 618618366890075326094027)
            ·
              refine ⟨927927550335112989141041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618618366890075326094027 927927550335112989141041)
              ·
                refine ⟨695945662751334741855781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927927550335112989141041 695945662751334741855781)
                ·
                  refine ⟨130489811765875264097959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 695945662751334741855781 130489811765875264097959)
                  ·
                    rfl

theorem cell20_285894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_285894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285894 prefixEnd_285894 := by exact prefixLift 285894
  have htrace : WordTrace (prefixWord ++ tailWord_285894) baseStart_285894 baseEnd_285894 := by
    simpa [prefixWord, tailWord_285894, baseEnd_285894] using wordTrace_append hprefix tailTrace_285894
  have hstable : (prefixWord ++ tailWord_285894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285894).length < 2 ^ (prefixWord ++ tailWord_285894).sum := by decide
  have hdescent : baseEnd_285894 < baseStart_285894 := by decide
  rcases family_descends (prefixWord ++ tailWord_285894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285901 : List Nat := [1, 6, 2, 2, 1, 1, 3, 4]
def baseStart_285901 : Nat := 118140960795 + 285901 * 2 ^ 59
def prefixEnd_285901 : Nat := 4983230072969 + 3 ^ 40 * 285901 * 2
def baseEnd_285901 : Nat := 43497668918871450288199

theorem tailTrace_285901 : CollatzResearch.WordTrace tailWord_285901 prefixEnd_285901 43497668918871450288199 := by
  unfold tailWord_285901
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427666137236979848513557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6951777424824653232342371 10427666137236979848513557)
  ·
    refine ⟨488796850182983430399073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10427666137236979848513557 488796850182983430399073)
    ·
      refine ⟨366597637637237572799305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 488796850182983430399073 366597637637237572799305)
      ·
        refine ⟨274948228227928179599479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366597637637237572799305 274948228227928179599479)
        ·
          refine ⟨412422342341892269399219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274948228227928179599479 412422342341892269399219)
          ·
            refine ⟨618633513512838404098829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412422342341892269399219 618633513512838404098829)
            ·
              refine ⟨231987567567314401537061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 618633513512838404098829 231987567567314401537061)
              ·
                refine ⟨43497668918871450288199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231987567567314401537061 43497668918871450288199)
                ·
                  rfl

theorem cell20_285901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_285901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285901 prefixEnd_285901 := by exact prefixLift 285901
  have htrace : WordTrace (prefixWord ++ tailWord_285901) baseStart_285901 baseEnd_285901 := by
    simpa [prefixWord, tailWord_285901, baseEnd_285901] using wordTrace_append hprefix tailTrace_285901
  have hstable : (prefixWord ++ tailWord_285901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285901).length < 2 ^ (prefixWord ++ tailWord_285901).sum := by decide
  have hdescent : baseEnd_285901 < baseStart_285901 := by decide
  rcases family_descends (prefixWord ++ tailWord_285901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285919 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 2]
def baseStart_285919 : Nat := 118140960795 + 285919 * 2 ^ 59
def prefixEnd_285919 : Nat := 4983230072969 + 3 ^ 40 * 285919 * 2
def baseEnd_285919 : Nat := 130501222447086288264523

theorem tailTrace_285919 : CollatzResearch.WordTrace tailWord_285919 prefixEnd_285919 130501222447086288264523 := by
  unfold tailWord_285919
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428322651171768922668811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6952215100781179281779207 10428322651171768922668811)
  ·
    refine ⟨15642483976757653384003217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10428322651171768922668811 15642483976757653384003217)
    ·
      refine ⟨11731862982568240038002413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15642483976757653384003217 11731862982568240038002413)
      ·
        refine ⟨4399448618463090014250905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11731862982568240038002413 4399448618463090014250905)
        ·
          refine ⟨3299586463847317510688179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4399448618463090014250905 3299586463847317510688179)
          ·
            refine ⟨4949379695770976266032269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299586463847317510688179 4949379695770976266032269)
            ·
              refine ⟨1856017385914116099762101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4949379695770976266032269 1856017385914116099762101)
              ·
                refine ⟨174001629929448384352697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1856017385914116099762101 174001629929448384352697)
                ·
                  refine ⟨130501222447086288264523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174001629929448384352697 130501222447086288264523)
                  ·
                    rfl

theorem cell20_285919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 2].length) (baseStart_285919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285919 prefixEnd_285919 := by exact prefixLift 285919
  have htrace : WordTrace (prefixWord ++ tailWord_285919) baseStart_285919 baseEnd_285919 := by
    simpa [prefixWord, tailWord_285919, baseEnd_285919] using wordTrace_append hprefix tailTrace_285919
  have hstable : (prefixWord ++ tailWord_285919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285919).length < 2 ^ (prefixWord ++ tailWord_285919).sum := by decide
  have hdescent : baseEnd_285919 < baseStart_285919 := by decide
  rcases family_descends (prefixWord ++ tailWord_285919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285960 : List Nat := [2, 1, 3, 2, 5, 1, 2, 4]
def baseStart_285960 : Nat := 118140960795 + 285960 * 2 ^ 59
def prefixEnd_285960 : Nat := 4983230072969 + 3 ^ 40 * 285960 * 2
def baseEnd_285960 : Nat := 43506645321424122632563

theorem tailTrace_285960 : CollatzResearch.WordTrace tailWord_285960 prefixEnd_285960 43506645321424122632563 := by
  unfold tailWord_285960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214909022011616462455667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6953212029348821949940889 5214909022011616462455667)
  ·
    refine ⟨7822363533017424693683501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5214909022011616462455667 7822363533017424693683501)
    ·
      refine ⟨2933386324881534260131313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7822363533017424693683501 2933386324881534260131313)
      ·
        refine ⟨2200039743661150695098485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2933386324881534260131313 2200039743661150695098485)
        ·
          refine ⟨206253725968232877665483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2200039743661150695098485 206253725968232877665483)
          ·
            refine ⟨309380588952349316498225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206253725968232877665483 309380588952349316498225)
            ·
              refine ⟨232035441714261987373669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309380588952349316498225 232035441714261987373669)
              ·
                refine ⟨43506645321424122632563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232035441714261987373669 43506645321424122632563)
                ·
                  rfl

theorem cell20_285960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_285960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285960 prefixEnd_285960 := by exact prefixLift 285960
  have htrace : WordTrace (prefixWord ++ tailWord_285960) baseStart_285960 baseEnd_285960 := by
    simpa [prefixWord, tailWord_285960, baseEnd_285960] using wordTrace_append hprefix tailTrace_285960
  have hstable : (prefixWord ++ tailWord_285960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285960).length < 2 ^ (prefixWord ++ tailWord_285960).sum := by decide
  have hdescent : baseEnd_285960 < baseStart_285960 := by decide
  rcases family_descends (prefixWord ++ tailWord_285960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_285964 : List Nat := [2, 2, 1, 2, 2, 3, 4, 4]
def baseStart_285964 : Nat := 118140960795 + 285964 * 2 ^ 59
def prefixEnd_285964 : Nat := 4983230072969 + 3 ^ 40 * 285964 * 2
def baseEnd_285964 : Nat := 43507253891088710588113

theorem tailTrace_285964 : CollatzResearch.WordTrace tailWord_285964 prefixEnd_285964 43507253891088710588113 := by
  unfold tailWord_285964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214981968004370804028473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6953309290672494405371297 5214981968004370804028473)
  ·
    refine ⟨3911236476003278103021355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5214981968004370804028473 3911236476003278103021355)
    ·
      refine ⟨5866854714004917154532033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911236476003278103021355 5866854714004917154532033)
      ·
        refine ⟨4400141035503687865899025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5866854714004917154532033 4400141035503687865899025)
        ·
          refine ⟨3300105776627765899424269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4400141035503687865899025 3300105776627765899424269)
          ·
            refine ⟨1237539666235412212284101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3300105776627765899424269 1237539666235412212284101)
            ·
              refine ⟨232038687419139789803269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1237539666235412212284101 232038687419139789803269)
              ·
                refine ⟨43507253891088710588113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232038687419139789803269 43507253891088710588113)
                ·
                  rfl

theorem cell20_285964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_285964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_285964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_285964 prefixEnd_285964 := by exact prefixLift 285964
  have htrace : WordTrace (prefixWord ++ tailWord_285964) baseStart_285964 baseEnd_285964 := by
    simpa [prefixWord, tailWord_285964, baseEnd_285964] using wordTrace_append hprefix tailTrace_285964
  have hstable : (prefixWord ++ tailWord_285964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_285964).length < 2 ^ (prefixWord ++ tailWord_285964).sum := by decide
  have hdescent : baseEnd_285964 < baseStart_285964 := by decide
  rcases family_descends (prefixWord ++ tailWord_285964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286002 : List Nat := [3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_286002 : Nat := 118140960795 + 286002 * 2 ^ 59
def prefixEnd_286002 : Nat := 4983230072969 + 3 ^ 40 * 286002 * 2
def baseEnd_286002 : Nat := 43513035302902296165839

theorem tailTrace_286002 : CollatzResearch.WordTrace tailWord_286002 prefixEnd_286002 43513035302902296165839 := by
  unfold tailWord_286002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2607837477467768524485065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6954233273247382731960173 2607837477467768524485065)
  ·
    refine ⟨1955878108100826393363799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2607837477467768524485065 1955878108100826393363799)
    ·
      refine ⟨2933817162151239590045699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955878108100826393363799 2933817162151239590045699)
      ·
        refine ⟨4400725743226859385068549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2933817162151239590045699 4400725743226859385068549)
        ·
          refine ⟨825136076855036134700353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4400725743226859385068549 825136076855036134700353)
          ·
            refine ⟨618852057641277101025265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825136076855036134700353 618852057641277101025265)
            ·
              refine ⟨464139043230957825768949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618852057641277101025265 464139043230957825768949)
              ·
                refine ⟨43513035302902296165839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464139043230957825768949 43513035302902296165839)
                ·
                  rfl

theorem cell20_286002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_286002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286002 prefixEnd_286002 := by exact prefixLift 286002
  have htrace : WordTrace (prefixWord ++ tailWord_286002) baseStart_286002 baseEnd_286002 := by
    simpa [prefixWord, tailWord_286002, baseEnd_286002] using wordTrace_append hprefix tailTrace_286002
  have hstable : (prefixWord ++ tailWord_286002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286002).length < 2 ^ (prefixWord ++ tailWord_286002).sum := by decide
  have hdescent : baseEnd_286002 < baseStart_286002 := by decide
  rcases family_descends (prefixWord ++ tailWord_286002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286005 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 3]
def baseStart_286005 : Nat := 118140960795 + 286005 * 2 ^ 59
def prefixEnd_286005 : Nat := 4983230072969 + 3 ^ 40 * 286005 * 2
def baseEnd_286005 : Nat := 130540475190452211397505

theorem tailTrace_286005 : CollatzResearch.WordTrace tailWord_286005 prefixEnd_286005 130540475190452211397505 := by
  unfold tailWord_286005
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431459328860205610299469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6954306219240137073532979 10431459328860205610299469)
  ·
    refine ⟨3911797248322577103862301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10431459328860205610299469 3911797248322577103862301)
    ·
      refine ⟨1466923968120966413948363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3911797248322577103862301 1466923968120966413948363)
      ·
        refine ⟨2200385952181449620922545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466923968120966413948363 2200385952181449620922545)
        ·
          refine ⟨1650289464136087215691909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2200385952181449620922545 1650289464136087215691909)
          ·
            refine ⟨309429274525516352942233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1650289464136087215691909 309429274525516352942233)
            ·
              refine ⟨232071955894137264706675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309429274525516352942233 232071955894137264706675)
              ·
                refine ⟨348107933841205897060013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232071955894137264706675 348107933841205897060013)
                ·
                  refine ⟨130540475190452211397505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348107933841205897060013 130540475190452211397505)
                  ·
                    rfl

theorem cell20_286005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_286005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286005 prefixEnd_286005 := by exact prefixLift 286005
  have htrace : WordTrace (prefixWord ++ tailWord_286005) baseStart_286005 baseEnd_286005 := by
    simpa [prefixWord, tailWord_286005, baseEnd_286005] using wordTrace_append hprefix tailTrace_286005
  have hstable : (prefixWord ++ tailWord_286005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286005).length < 2 ^ (prefixWord ++ tailWord_286005).sum := by decide
  have hdescent : baseEnd_286005 < baseStart_286005 := by decide
  rcases family_descends (prefixWord ++ tailWord_286005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286023 : List Nat := [1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_286023 : Nat := 118140960795 + 286023 * 2 ^ 59
def prefixEnd_286023 : Nat := 4983230072969 + 3 ^ 40 * 286023 * 2
def baseEnd_286023 : Nat := 43516230293641382932477

theorem tailTrace_286023 : CollatzResearch.WordTrace tailWord_286023 prefixEnd_286023 43516230293641382932477 := by
  unfold tailWord_286023
  simp only [CollatzResearch.WordTrace]
  refine ⟨10432115842794994684454723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6954743895196663122969815 10432115842794994684454723)
  ·
    refine ⟨15648173764192492026682085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10432115842794994684454723 15648173764192492026682085)
    ·
      refine ⟨2934032580786092255002891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15648173764192492026682085 2934032580786092255002891)
      ·
        refine ⟨4401048871179138382504337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2934032580786092255002891 4401048871179138382504337)
        ·
          refine ⟨3300786653384353786878253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4401048871179138382504337 3300786653384353786878253)
          ·
            refine ⟨1237794995019132670079345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3300786653384353786878253 1237794995019132670079345)
            ·
              refine ⟨928346246264349502559509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237794995019132670079345 928346246264349502559509)
              ·
                refine ⟨43516230293641382932477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 928346246264349502559509 43516230293641382932477)
                ·
                  rfl

theorem cell20_286023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_286023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286023 prefixEnd_286023 := by exact prefixLift 286023
  have htrace : WordTrace (prefixWord ++ tailWord_286023) baseStart_286023 baseEnd_286023 := by
    simpa [prefixWord, tailWord_286023, baseEnd_286023] using wordTrace_append hprefix tailTrace_286023
  have hstable : (prefixWord ++ tailWord_286023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286023).length < 2 ^ (prefixWord ++ tailWord_286023).sum := by decide
  have hdescent : baseEnd_286023 < baseStart_286023 := by decide
  rcases family_descends (prefixWord ++ tailWord_286023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286033 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 2]
def baseStart_286033 : Nat := 118140960795 + 286033 * 2 ^ 59
def prefixEnd_286033 : Nat := 4983230072969 + 3 ^ 40 * 286033 * 2
def baseEnd_286033 : Nat := 130553255153408558464057

theorem tailTrace_286033 : CollatzResearch.WordTrace tailWord_286033 prefixEnd_286033 130553255153408558464057 := by
  unfold tailWord_286033
  simp only [CollatzResearch.WordTrace]
  refine ⟨10432480572758766392318753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6954987048505844261545835 10432480572758766392318753)
  ·
    refine ⟨7824360429569074794239065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10432480572758766392318753 7824360429569074794239065)
    ·
      refine ⟨5868270322176806095679299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7824360429569074794239065 5868270322176806095679299)
      ·
        refine ⟨8802405483265209143518949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5868270322176806095679299 8802405483265209143518949)
        ·
          refine ⟨1650451028112226714409803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8802405483265209143518949 1650451028112226714409803)
          ·
            refine ⟨2475676542168340071614705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650451028112226714409803 2475676542168340071614705)
            ·
              refine ⟨1856757406626255053711029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475676542168340071614705 1856757406626255053711029)
              ·
                refine ⟨174071006871211411285409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1856757406626255053711029 174071006871211411285409)
                ·
                  refine ⟨130553255153408558464057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174071006871211411285409 130553255153408558464057)
                  ·
                    rfl

theorem cell20_286033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_286033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286033 prefixEnd_286033 := by exact prefixLift 286033
  have htrace : WordTrace (prefixWord ++ tailWord_286033) baseStart_286033 baseEnd_286033 := by
    simpa [prefixWord, tailWord_286033, baseEnd_286033] using wordTrace_append hprefix tailTrace_286033
  have hstable : (prefixWord ++ tailWord_286033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286033).length < 2 ^ (prefixWord ++ tailWord_286033).sum := by decide
  have hdescent : baseEnd_286033 < baseStart_286033 := by decide
  rcases family_descends (prefixWord ++ tailWord_286033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286050 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_286050 : Nat := 118140960795 + 286050 * 2 ^ 59
def prefixEnd_286050 : Nat := 4983230072969 + 3 ^ 40 * 286050 * 2
def baseEnd_286050 : Nat := 130561014416632054897321

theorem tailTrace_286050 : CollatzResearch.WordTrace tailWord_286050 prefixEnd_286050 130561014416632054897321 := by
  unfold tailWord_286050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608275153424294573921901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6955400409131452197125069 2608275153424294573921901)
  ·
    refine ⟨978103182534110465220713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2608275153424294573921901 978103182534110465220713)
    ·
      refine ⟨733577386900582848915535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 978103182534110465220713 733577386900582848915535)
      ·
        refine ⟨1100366080350874273373303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 733577386900582848915535 1100366080350874273373303)
        ·
          refine ⟨1650549120526311410059955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100366080350874273373303 1650549120526311410059955)
          ·
            refine ⟨2475823680789467115089933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650549120526311410059955 2475823680789467115089933)
            ·
              refine ⟨928433880296050168158725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2475823680789467115089933 928433880296050168158725)
              ·
                refine ⟨174081352555509406529761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 928433880296050168158725 174081352555509406529761)
                ·
                  refine ⟨130561014416632054897321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174081352555509406529761 130561014416632054897321)
                  ·
                    rfl

theorem cell20_286050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_286050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286050 prefixEnd_286050 := by exact prefixLift 286050
  have htrace : WordTrace (prefixWord ++ tailWord_286050) baseStart_286050 baseEnd_286050 := by
    simpa [prefixWord, tailWord_286050, baseEnd_286050] using wordTrace_append hprefix tailTrace_286050
  have hstable : (prefixWord ++ tailWord_286050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286050).length < 2 ^ (prefixWord ++ tailWord_286050).sum := by decide
  have hdescent : baseEnd_286050 < baseStart_286050 := by decide
  rcases family_descends (prefixWord ++ tailWord_286050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286088 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 2]
def baseStart_286088 : Nat := 118140960795 + 286088 * 2 ^ 59
def prefixEnd_286088 : Nat := 4983230072969 + 3 ^ 40 * 286088 * 2
def baseEnd_286088 : Nat := 130578358652072811630499

theorem tailTrace_286088 : CollatzResearch.WordTrace tailWord_286088 prefixEnd_286088 130578358652072811630499 := by
  unfold tailWord_286088
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217243293779755392785459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6956324391706340523713945 5217243293779755392785459)
  ·
    refine ⟨7825864940669633089178189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5217243293779755392785459 7825864940669633089178189)
    ·
      refine ⟨2934699352751112408441821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7825864940669633089178189 2934699352751112408441821)
      ·
        refine ⟨1100512257281667153165683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2934699352751112408441821 1100512257281667153165683)
        ·
          refine ⟨1650768385922500729748525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100512257281667153165683 1650768385922500729748525)
          ·
            refine ⟨619038144720937773655697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1650768385922500729748525 619038144720937773655697)
            ·
              refine ⟨464278608540703330241773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619038144720937773655697 464278608540703330241773)
              ·
                refine ⟨174104478202763748840665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464278608540703330241773 174104478202763748840665)
                ·
                  refine ⟨130578358652072811630499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174104478202763748840665 130578358652072811630499)
                  ·
                    rfl

theorem cell20_286088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_286088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286088 prefixEnd_286088 := by exact prefixLift 286088
  have htrace : WordTrace (prefixWord ++ tailWord_286088) baseStart_286088 baseEnd_286088 := by
    simpa [prefixWord, tailWord_286088, baseEnd_286088] using wordTrace_append hprefix tailTrace_286088
  have hstable : (prefixWord ++ tailWord_286088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286088).length < 2 ^ (prefixWord ++ tailWord_286088).sum := by decide
  have hdescent : baseEnd_286088 < baseStart_286088 := by decide
  rcases family_descends (prefixWord ++ tailWord_286088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286098 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_286098 : Nat := 118140960795 + 286098 * 2 ^ 59
def prefixEnd_286098 : Nat := 4983230072969 + 3 ^ 40 * 286098 * 2
def baseEnd_286098 : Nat := 130582922924557221297125

theorem tailTrace_286098 : CollatzResearch.WordTrace tailWord_286098 prefixEnd_286098 130582922924557221297125 := by
  unfold tailWord_286098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608712829380820623358737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6956567545015521662289965 2608712829380820623358737)
  ·
    refine ⟨1956534622035615467519053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2608712829380820623358737 1956534622035615467519053)
    ·
      refine ⟨733700483263355800319645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1956534622035615467519053 733700483263355800319645)
      ·
        refine ⟨275137681223758425119867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 733700483263355800319645 275137681223758425119867)
        ·
          refine ⟨412706521835637637679801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275137681223758425119867 412706521835637637679801)
          ·
            refine ⟨309529891376728228259851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412706521835637637679801 309529891376728228259851)
            ·
              refine ⟨464294837065092342389777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309529891376728228259851 464294837065092342389777)
              ·
                refine ⟨348221127798819256792333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464294837065092342389777 348221127798819256792333)
                ·
                  refine ⟨130582922924557221297125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348221127798819256792333 130582922924557221297125)
                  ·
                    rfl

theorem cell20_286098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_286098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286098 prefixEnd_286098 := by exact prefixLift 286098
  have htrace : WordTrace (prefixWord ++ tailWord_286098) baseStart_286098 baseEnd_286098 := by
    simpa [prefixWord, tailWord_286098, baseEnd_286098] using wordTrace_append hprefix tailTrace_286098
  have hstable : (prefixWord ++ tailWord_286098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286098).length < 2 ^ (prefixWord ++ tailWord_286098).sum := by decide
  have hdescent : baseEnd_286098 < baseStart_286098 := by decide
  rcases family_descends (prefixWord ++ tailWord_286098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286109 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 4]
def baseStart_286109 : Nat := 118140960795 + 286109 * 2 ^ 59
def prefixEnd_286109 : Nat := 4983230072969 + 3 ^ 40 * 286109 * 2
def baseEnd_286109 : Nat := 130587943624290071930413

theorem tailTrace_286109 : CollatzResearch.WordTrace tailWord_286109 prefixEnd_286109 130587943624290071930413 := by
  unfold tailWord_286109
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435252520483431372085381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6956835013655620914723587 10435252520483431372085381)
  ·
    refine ⟨1956609847590643382266009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10435252520483431372085381 1956609847590643382266009)
    ·
      refine ⟨1467457385692982536699507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1956609847590643382266009 1467457385692982536699507)
      ·
        refine ⟨2201186078539473805049261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467457385692982536699507 2201186078539473805049261)
        ·
          refine ⟨825444779452302676893473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2201186078539473805049261 825444779452302676893473)
          ·
            refine ⟨619083584589227007670105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825444779452302676893473 619083584589227007670105)
            ·
              refine ⟨464312688441920255752579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619083584589227007670105 464312688441920255752579)
              ·
                refine ⟨696469032662880383628869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464312688441920255752579 696469032662880383628869)
                ·
                  refine ⟨130587943624290071930413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696469032662880383628869 130587943624290071930413)
                  ·
                    rfl

theorem cell20_286109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_286109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286109 prefixEnd_286109 := by exact prefixLift 286109
  have htrace : WordTrace (prefixWord ++ tailWord_286109) baseStart_286109 baseEnd_286109 := by
    simpa [prefixWord, tailWord_286109, baseEnd_286109] using wordTrace_append hprefix tailTrace_286109
  have hstable : (prefixWord ++ tailWord_286109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286109).length < 2 ^ (prefixWord ++ tailWord_286109).sum := by decide
  have hdescent : baseEnd_286109 < baseStart_286109 := by decide
  rcases family_descends (prefixWord ++ tailWord_286109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286133 : List Nat := [1, 3, 3, 2, 2, 3, 2, 4]
def baseStart_286133 : Nat := 118140960795 + 286133 * 2 ^ 59
def prefixEnd_286133 : Nat := 4983230072969 + 3 ^ 40 * 286133 * 2
def baseEnd_286133 : Nat := 43532965959417551710105

theorem tailTrace_286133 : CollatzResearch.WordTrace tailWord_286133 prefixEnd_286133 43532965959417551710105 := by
  unfold tailWord_286133
  simp only [CollatzResearch.WordTrace]
  refine ⟨10436127872396483470959053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6957418581597655647306035 10436127872396483470959053)
  ·
    refine ⟨3913547952148681301609645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10436127872396483470959053 3913547952148681301609645)
    ·
      refine ⟨1467580482055755488103617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3913547952148681301609645 1467580482055755488103617)
      ·
        refine ⟨1100685361541816616077713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1467580482055755488103617 1100685361541816616077713)
        ·
          refine ⟨825514021156362462058285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100685361541816616077713 825514021156362462058285)
          ·
            refine ⟨309567757933635923271857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 825514021156362462058285 309567757933635923271857)
            ·
              refine ⟨232175818450226942453893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309567757933635923271857 232175818450226942453893)
              ·
                refine ⟨43532965959417551710105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232175818450226942453893 43532965959417551710105)
                ·
                  rfl

theorem cell20_286133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 4].length) (baseStart_286133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286133 prefixEnd_286133 := by exact prefixLift 286133
  have htrace : WordTrace (prefixWord ++ tailWord_286133) baseStart_286133 baseEnd_286133 := by
    simpa [prefixWord, tailWord_286133, baseEnd_286133] using wordTrace_append hprefix tailTrace_286133
  have hstable : (prefixWord ++ tailWord_286133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286133).length < 2 ^ (prefixWord ++ tailWord_286133).sum := by decide
  have hdescent : baseEnd_286133 < baseStart_286133 := by decide
  rcases family_descends (prefixWord ++ tailWord_286133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286144 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_286144 : Nat := 118140960795 + 286144 * 2 ^ 59
def prefixEnd_286144 : Nat := 4983230072969 + 3 ^ 40 * 286144 * 2
def baseEnd_286144 : Nat := 130603918577985505763603

theorem tailTrace_286144 : CollatzResearch.WordTrace tailWord_286144 prefixEnd_286144 130603918577985505763603 := by
  unfold tailWord_286144
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218264537678316174804743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6957686050237754899739657 5218264537678316174804743)
  ·
    refine ⟨7827396806517474262207115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5218264537678316174804743 7827396806517474262207115)
    ·
      refine ⟨11741095209776211393310673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7827396806517474262207115 11741095209776211393310673)
      ·
        refine ⟨8805821407332158544983005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11741095209776211393310673 8805821407332158544983005)
        ·
          refine ⟨3302183027749559454368627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8805821407332158544983005 3302183027749559454368627)
          ·
            refine ⟨4953274541624339181552941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302183027749559454368627 4953274541624339181552941)
            ·
              refine ⟨1857477953109127193082353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4953274541624339181552941 1857477953109127193082353)
              ·
                refine ⟨1393108464831845394811765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857477953109127193082353 1393108464831845394811765)
                ·
                  refine ⟨130603918577985505763603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1393108464831845394811765 130603918577985505763603)
                  ·
                    rfl

theorem cell20_286144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_286144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286144 prefixEnd_286144 := by exact prefixLift 286144
  have htrace : WordTrace (prefixWord ++ tailWord_286144) baseStart_286144 baseEnd_286144 := by
    simpa [prefixWord, tailWord_286144, baseEnd_286144] using wordTrace_append hprefix tailTrace_286144
  have hstable : (prefixWord ++ tailWord_286144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286144).length < 2 ^ (prefixWord ++ tailWord_286144).sum := by decide
  have hdescent : baseEnd_286144 < baseStart_286144 := by decide
  rcases family_descends (prefixWord ++ tailWord_286144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286146 : List Nat := [3, 5, 2, 1, 2, 1, 6]
def baseStart_286146 : Nat := 118140960795 + 286146 * 2 ^ 59
def prefixEnd_286146 : Nat := 4983230072969 + 3 ^ 40 * 286146 * 2
def baseEnd_286146 : Nat := 14511647936942487521881

theorem tailTrace_286146 : CollatzResearch.WordTrace tailWord_286146 prefixEnd_286146 14511647936942487521881 := by
  unfold tailWord_286146
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609150505337346672795573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6957734680899591127454861 2609150505337346672795573)
  ·
    refine ⟨244607859875376250574585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2609150505337346672795573 244607859875376250574585)
    ·
      refine ⟨183455894906532187930939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244607859875376250574585 183455894906532187930939)
      ·
        refine ⟨275183842359798281896409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183455894906532187930939 275183842359798281896409)
        ·
          refine ⟨206387881769848711422307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275183842359798281896409 206387881769848711422307)
          ·
            refine ⟨309581822654773067133461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206387881769848711422307 309581822654773067133461)
            ·
              refine ⟨14511647936942487521881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 309581822654773067133461 14511647936942487521881)
              ·
                rfl

theorem cell20_286146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 6].length) (baseStart_286146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286146 prefixEnd_286146 := by exact prefixLift 286146
  have htrace : WordTrace (prefixWord ++ tailWord_286146) baseStart_286146 baseEnd_286146 := by
    simpa [prefixWord, tailWord_286146, baseEnd_286146] using wordTrace_append hprefix tailTrace_286146
  have hstable : (prefixWord ++ tailWord_286146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286146).length < 2 ^ (prefixWord ++ tailWord_286146).sum := by decide
  have hdescent : baseEnd_286146 < baseStart_286146 := by decide
  rcases family_descends (prefixWord ++ tailWord_286146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286147 : List Nat := [1, 1, 1, 3, 1, 1, 7, 3, 2]
def baseStart_286147 : Nat := 118140960795 + 286147 * 2 ^ 59
def prefixEnd_286147 : Nat := 4983230072969 + 3 ^ 40 * 286147 * 2
def baseEnd_286147 : Nat := 130605287859730828663591

theorem tailTrace_286147 : CollatzResearch.WordTrace tailWord_286147 prefixEnd_286147 130605287859730828663591 := by
  unfold tailWord_286147
  simp only [CollatzResearch.WordTrace]
  refine ⟨10436638494345763861968695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6957758996230509241312463 10436638494345763861968695)
  ·
    refine ⟨15654957741518645792953043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10436638494345763861968695 15654957741518645792953043)
    ·
      refine ⟨23482436612277968689429565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15654957741518645792953043 23482436612277968689429565)
      ·
        refine ⟨8805913729604238258536087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23482436612277968689429565 8805913729604238258536087)
        ·
          refine ⟨13208870594406357387804131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8805913729604238258536087 13208870594406357387804131)
          ·
            refine ⟨19813305891609536081706197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13208870594406357387804131 19813305891609536081706197)
            ·
              refine ⟨464374356834598501914989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19813305891609536081706197 464374356834598501914989)
              ·
                refine ⟨174140383812974438218121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464374356834598501914989 174140383812974438218121)
                ·
                  refine ⟨130605287859730828663591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174140383812974438218121 130605287859730828663591)
                  ·
                    rfl

theorem cell20_286147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 2].length) (baseStart_286147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286147 prefixEnd_286147 := by exact prefixLift 286147
  have htrace : WordTrace (prefixWord ++ tailWord_286147) baseStart_286147 baseEnd_286147 := by
    simpa [prefixWord, tailWord_286147, baseEnd_286147] using wordTrace_append hprefix tailTrace_286147
  have hstable : (prefixWord ++ tailWord_286147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286147).length < 2 ^ (prefixWord ++ tailWord_286147).sum := by decide
  have hdescent : baseEnd_286147 < baseStart_286147 := by decide
  rcases family_descends (prefixWord ++ tailWord_286147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286164 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_286164 : Nat := 118140960795 + 286164 * 2 ^ 59
def prefixEnd_286164 : Nat := 4983230072969 + 3 ^ 40 * 286164 * 2
def baseEnd_286164 : Nat := 130613047122954325096855

theorem tailTrace_286164 : CollatzResearch.WordTrace tailWord_286164 prefixEnd_286164 130613047122954325096855 := by
  unfold tailWord_286164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218629267642087882668773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6958172356856117176891697 5218629267642087882668773)
  ·
    refine ⟨978492987682891478000395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5218629267642087882668773 978492987682891478000395)
    ·
      refine ⟨1467739481524337217000593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978492987682891478000395 1467739481524337217000593)
      ·
        refine ⟨1100804611143252912750445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1467739481524337217000593 1100804611143252912750445)
        ·
          refine ⟨412801729178719842281417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1100804611143252912750445 412801729178719842281417)
          ·
            refine ⟨309601296884039881711063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412801729178719842281417 309601296884039881711063)
            ·
              refine ⟨464401945326059822566595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309601296884039881711063 464401945326059822566595)
              ·
                refine ⟨696602917989089733849893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464401945326059822566595 696602917989089733849893)
                ·
                  refine ⟨130613047122954325096855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696602917989089733849893 130613047122954325096855)
                  ·
                    rfl

theorem cell20_286164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_286164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286164 prefixEnd_286164 := by exact prefixLift 286164
  have htrace : WordTrace (prefixWord ++ tailWord_286164) baseStart_286164 baseEnd_286164 := by
    simpa [prefixWord, tailWord_286164, baseEnd_286164] using wordTrace_append hprefix tailTrace_286164
  have hstable : (prefixWord ++ tailWord_286164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286164).length < 2 ^ (prefixWord ++ tailWord_286164).sum := by decide
  have hdescent : baseEnd_286164 < baseStart_286164 := by decide
  rcases family_descends (prefixWord ++ tailWord_286164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286168 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_286168 : Nat := 118140960795 + 286168 * 2 ^ 59
def prefixEnd_286168 : Nat := 4983230072969 + 3 ^ 40 * 286168 * 2
def baseEnd_286168 : Nat := 130614872831948088963505

theorem tailTrace_286168 : CollatzResearch.WordTrace tailWord_286168 prefixEnd_286168 130614872831948088963505 := by
  unfold tailWord_286168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218702213634842224241579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6958269618179789632322105 5218702213634842224241579)
  ·
    refine ⟨7828053320452263336362369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5218702213634842224241579 7828053320452263336362369)
    ·
      refine ⟨5871039990339197502271777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7828053320452263336362369 5871039990339197502271777)
      ·
        refine ⟨4403279992754398126703833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5871039990339197502271777 4403279992754398126703833)
        ·
          refine ⟨3302459994565798595027875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4403279992754398126703833 3302459994565798595027875)
          ·
            refine ⟨4953689991848697892541813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302459994565798595027875 4953689991848697892541813)
            ·
              refine ⟨464408436735815427425795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4953689991848697892541813 464408436735815427425795)
              ·
                refine ⟨696612655103723141138693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464408436735815427425795 696612655103723141138693)
                ·
                  refine ⟨130614872831948088963505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696612655103723141138693 130614872831948088963505)
                  ·
                    rfl

theorem cell20_286168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_286168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286168 prefixEnd_286168 := by exact prefixLift 286168
  have htrace : WordTrace (prefixWord ++ tailWord_286168) baseStart_286168 baseEnd_286168 := by
    simpa [prefixWord, tailWord_286168, baseEnd_286168] using wordTrace_append hprefix tailTrace_286168
  have hstable : (prefixWord ++ tailWord_286168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286168).length < 2 ^ (prefixWord ++ tailWord_286168).sum := by decide
  have hdescent : baseEnd_286168 < baseStart_286168 := by decide
  rcases family_descends (prefixWord ++ tailWord_286168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286175 : List Nat := [1, 1, 2, 3, 3, 1, 4, 5]
def baseStart_286175 : Nat := 118140960795 + 286175 * 2 ^ 59
def prefixEnd_286175 : Nat := 4983230072969 + 3 ^ 40 * 286175 * 2
def baseEnd_286175 : Nat := 43539355940895725243381

theorem tailTrace_286175 : CollatzResearch.WordTrace tailWord_286175 prefixEnd_286175 43539355940895725243381 := by
  unfold tailWord_286175
  simp only [CollatzResearch.WordTrace]
  refine ⟨10437659738244324643987979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6958439825496216429325319 10437659738244324643987979)
  ·
    refine ⟨15656489607366486965981969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10437659738244324643987979 15656489607366486965981969)
    ·
      refine ⟨11742367205524865224486477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15656489607366486965981969 11742367205524865224486477)
      ·
        refine ⟨4403387702071824459182429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11742367205524865224486477 4403387702071824459182429)
        ·
          refine ⟨1651270388276934172193411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4403387702071824459182429 1651270388276934172193411)
          ·
            refine ⟨2476905582415401258290117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651270388276934172193411 2476905582415401258290117)
            ·
              refine ⟨464419796702887735929397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2476905582415401258290117 464419796702887735929397)
              ·
                refine ⟨43539355940895725243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464419796702887735929397 43539355940895725243381)
                ·
                  rfl

theorem cell20_286175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 5].length) (baseStart_286175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286175 prefixEnd_286175 := by exact prefixLift 286175
  have htrace : WordTrace (prefixWord ++ tailWord_286175) baseStart_286175 baseEnd_286175 := by
    simpa [prefixWord, tailWord_286175, baseEnd_286175] using wordTrace_append hprefix tailTrace_286175
  have hstable : (prefixWord ++ tailWord_286175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286175).length < 2 ^ (prefixWord ++ tailWord_286175).sum := by decide
  have hdescent : baseEnd_286175 < baseStart_286175 := by decide
  rcases family_descends (prefixWord ++ tailWord_286175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286219 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 2]
def baseStart_286219 : Nat := 118140960795 + 286219 * 2 ^ 59
def prefixEnd_286219 : Nat := 4983230072969 + 3 ^ 40 * 286219 * 2
def baseEnd_286219 : Nat := 130638150621618578263297

theorem tailTrace_286219 : CollatzResearch.WordTrace tailWord_286219 prefixEnd_286219 130638150621618578263297 := by
  unfold tailWord_286219
  simp only [CollatzResearch.WordTrace]
  refine ⟨10439264550084920158589711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6959509700056613439059807 10439264550084920158589711)
  ·
    refine ⟨15658896825127380237884567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10439264550084920158589711 15658896825127380237884567)
    ·
      refine ⟨23488345237691070356826851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15658896825127380237884567 23488345237691070356826851)
      ·
        refine ⟨35232517856536605535240277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23488345237691070356826851 35232517856536605535240277)
        ·
          refine ⟨412881068631288346116097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 35232517856536605535240277 412881068631288346116097)
          ·
            refine ⟨309660801473466259587073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412881068631288346116097 309660801473466259587073)
            ·
              refine ⟨232245601105099694690305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309660801473466259587073 232245601105099694690305)
              ·
                refine ⟨174184200828824771017729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232245601105099694690305 174184200828824771017729)
                ·
                  refine ⟨130638150621618578263297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174184200828824771017729 130638150621618578263297)
                  ·
                    rfl

theorem cell20_286219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 2].length) (baseStart_286219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286219 prefixEnd_286219 := by exact prefixLift 286219
  have htrace : WordTrace (prefixWord ++ tailWord_286219) baseStart_286219 baseEnd_286219 := by
    simpa [prefixWord, tailWord_286219, baseEnd_286219] using wordTrace_append hprefix tailTrace_286219
  have hstable : (prefixWord ++ tailWord_286219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286219).length < 2 ^ (prefixWord ++ tailWord_286219).sum := by decide
  have hdescent : baseEnd_286219 < baseStart_286219 := by decide
  rcases family_descends (prefixWord ++ tailWord_286219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286237 : List Nat := [1, 4, 2, 2, 1, 1, 1, 5, 3]
def baseStart_286237 : Nat := 118140960795 + 286237 * 2 ^ 59
def prefixEnd_286237 : Nat := 4983230072969 + 3 ^ 40 * 286237 * 2
def baseEnd_286237 : Nat := 130646366312090515663223

theorem tailTrace_286237 : CollatzResearch.WordTrace tailWord_286237 prefixEnd_286237 130646366312090515663223 := by
  unfold tailWord_286237
  simp only [CollatzResearch.WordTrace]
  refine ⟨10439921064019709232744965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6959947376013139488496643 10439921064019709232744965)
  ·
    refine ⟨1957485199503695481139681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10439921064019709232744965 1957485199503695481139681)
    ·
      refine ⟨1468113899627771610854761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1957485199503695481139681 1468113899627771610854761)
      ·
        refine ⟨1101085424720828708141071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1468113899627771610854761 1101085424720828708141071)
        ·
          refine ⟨1651628137081243062211607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101085424720828708141071 1651628137081243062211607)
          ·
            refine ⟨2477442205621864593317411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651628137081243062211607 2477442205621864593317411)
            ·
              refine ⟨3716163308432796889976117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477442205621864593317411 3716163308432796889976117)
              ·
                refine ⟨348390310165574708435261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3716163308432796889976117 348390310165574708435261)
                ·
                  refine ⟨130646366312090515663223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348390310165574708435261 130646366312090515663223)
                  ·
                    rfl

theorem cell20_286237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_286237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286237 prefixEnd_286237 := by exact prefixLift 286237
  have htrace : WordTrace (prefixWord ++ tailWord_286237) baseStart_286237 baseEnd_286237 := by
    simpa [prefixWord, tailWord_286237, baseEnd_286237] using wordTrace_append hprefix tailTrace_286237
  have hstable : (prefixWord ++ tailWord_286237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286237).length < 2 ^ (prefixWord ++ tailWord_286237).sum := by decide
  have hdescent : baseEnd_286237 < baseStart_286237 := by decide
  rcases family_descends (prefixWord ++ tailWord_286237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286258 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_286258 : Nat := 118140960795 + 286258 * 2 ^ 59
def prefixEnd_286258 : Nat := 4983230072969 + 3 ^ 40 * 286258 * 2
def baseEnd_286258 : Nat := 130655951284307775963137

theorem tailTrace_286258 : CollatzResearch.WordTrace tailWord_286258 prefixEnd_286258 130655951284307775963137 := by
  unfold tailWord_286258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610171749235907454814857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6960457997962419879506285 2610171749235907454814857)
  ·
    refine ⟨1957628811926930591111143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2610171749235907454814857 1957628811926930591111143)
    ·
      refine ⟨2936443217890395886666715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957628811926930591111143 2936443217890395886666715)
      ·
        refine ⟨4404664826835593830000073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936443217890395886666715 4404664826835593830000073)
        ·
          refine ⟨3303498620126695372500055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4404664826835593830000073 3303498620126695372500055)
          ·
            refine ⟨4955247930190043058750083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303498620126695372500055 4955247930190043058750083)
            ·
              refine ⟨7432871895285064588125125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955247930190043058750083 7432871895285064588125125)
              ·
                refine ⟨1393663480365949610273461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7432871895285064588125125 1393663480365949610273461)
                ·
                  refine ⟨130655951284307775963137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1393663480365949610273461 130655951284307775963137)
                  ·
                    rfl

theorem cell20_286258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_286258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286258 prefixEnd_286258 := by exact prefixLift 286258
  have htrace : WordTrace (prefixWord ++ tailWord_286258) baseStart_286258 baseEnd_286258 := by
    simpa [prefixWord, tailWord_286258, baseEnd_286258] using wordTrace_append hprefix tailTrace_286258
  have hstable : (prefixWord ++ tailWord_286258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286258).length < 2 ^ (prefixWord ++ tailWord_286258).sum := by decide
  have hdescent : baseEnd_286258 < baseStart_286258 := by decide
  rcases family_descends (prefixWord ++ tailWord_286258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286261 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 2]
def baseStart_286261 : Nat := 118140960795 + 286261 * 2 ^ 59
def prefixEnd_286261 : Nat := 4983230072969 + 3 ^ 40 * 286261 * 2
def baseEnd_286261 : Nat := 130657320566053098863125

theorem tailTrace_286261 : CollatzResearch.WordTrace tailWord_286261 prefixEnd_286261 130657320566053098863125 := by
  unfold tailWord_286261
  simp only [CollatzResearch.WordTrace]
  refine ⟨10440796415932761331618637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6960530943955174221079091 10440796415932761331618637)
  ·
    refine ⟨3915298655974785499356989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10440796415932761331618637 3915298655974785499356989)
    ·
      refine ⟨1468236995990544562258871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3915298655974785499356989 1468236995990544562258871)
      ·
        refine ⟨2202355493985816843388307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468236995990544562258871 2202355493985816843388307)
        ·
          refine ⟨3303533240978725265082461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202355493985816843388307 3303533240978725265082461)
          ·
            refine ⟨1238824965367021974405923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3303533240978725265082461 1238824965367021974405923)
            ·
              refine ⟨1858237448050532961608885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238824965367021974405923 1858237448050532961608885)
              ·
                refine ⟨174209760754737465150833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1858237448050532961608885 174209760754737465150833)
                ·
                  refine ⟨130657320566053098863125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174209760754737465150833 130657320566053098863125)
                  ·
                    rfl

theorem cell20_286261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_286261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286261 prefixEnd_286261 := by exact prefixLift 286261
  have htrace : WordTrace (prefixWord ++ tailWord_286261) baseStart_286261 baseEnd_286261 := by
    simpa [prefixWord, tailWord_286261, baseEnd_286261] using wordTrace_append hprefix tailTrace_286261
  have hstable : (prefixWord ++ tailWord_286261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286261).length < 2 ^ (prefixWord ++ tailWord_286261).sum := by decide
  have hdescent : baseEnd_286261 < baseStart_286261 := by decide
  rcases family_descends (prefixWord ++ tailWord_286261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286282 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_286282 : Nat := 118140960795 + 286282 * 2 ^ 59
def prefixEnd_286282 : Nat := 4983230072969 + 3 ^ 40 * 286282 * 2
def baseEnd_286282 : Nat := 130666905538270359163039

theorem tailTrace_286282 : CollatzResearch.WordTrace tailWord_286282 prefixEnd_286282 130666905538270359163039 := by
  unfold tailWord_286282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610390587214170479533275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6961041565904454612088733 2610390587214170479533275)
  ·
    refine ⟨3915585880821255719299913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2610390587214170479533275 3915585880821255719299913)
    ·
      refine ⟨2936689410615941789474935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3915585880821255719299913 2936689410615941789474935)
      ·
        refine ⟨4405034115923912684212403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936689410615941789474935 4405034115923912684212403)
        ·
          refine ⟨6607551173885869026318605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405034115923912684212403 6607551173885869026318605)
          ·
            refine ⟨2477831690207200884869477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6607551173885869026318605 2477831690207200884869477)
            ·
              refine ⟨464593441913850165913027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2477831690207200884869477 464593441913850165913027)
              ·
                refine ⟨696890162870775248869541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464593441913850165913027 696890162870775248869541)
                ·
                  refine ⟨130666905538270359163039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 696890162870775248869541 130666905538270359163039)
                  ·
                    rfl

theorem cell20_286282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_286282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286282 prefixEnd_286282 := by exact prefixLift 286282
  have htrace : WordTrace (prefixWord ++ tailWord_286282) baseStart_286282 baseEnd_286282 := by
    simpa [prefixWord, tailWord_286282, baseEnd_286282] using wordTrace_append hprefix tailTrace_286282
  have hstable : (prefixWord ++ tailWord_286282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286282).length < 2 ^ (prefixWord ++ tailWord_286282).sum := by decide
  have hdescent : baseEnd_286282 < baseStart_286282 := by decide
  rcases family_descends (prefixWord ++ tailWord_286282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286292 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_286292 : Nat := 118140960795 + 286292 * 2 ^ 59
def prefixEnd_286292 : Nat := 4983230072969 + 3 ^ 40 * 286292 * 2
def baseEnd_286292 : Nat := 130671469810754768829665

theorem tailTrace_286292 : CollatzResearch.WordTrace tailWord_286292 prefixEnd_286292 130671469810754768829665 := by
  unfold tailWord_286292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5220963539410226812998565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6961284719213635750664753 5220963539410226812998565)
  ·
    refine ⟨978930663639417527437231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5220963539410226812998565 978930663639417527437231)
    ·
      refine ⟨1468395995459126291155847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978930663639417527437231 1468395995459126291155847)
      ·
        refine ⟨2202593993188689436733771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468395995459126291155847 2202593993188689436733771)
        ·
          refine ⟨3303890989783034155100657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202593993188689436733771 3303890989783034155100657)
          ·
            refine ⟨2477918242337275616325493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3303890989783034155100657 2477918242337275616325493)
            ·
              refine ⟨232304835219119589030515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2477918242337275616325493 232304835219119589030515)
              ·
                refine ⟨348457252828679383545773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232304835219119589030515 348457252828679383545773)
                ·
                  refine ⟨130671469810754768829665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348457252828679383545773 130671469810754768829665)
                  ·
                    rfl

theorem cell20_286292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_286292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286292 prefixEnd_286292 := by exact prefixLift 286292
  have htrace : WordTrace (prefixWord ++ tailWord_286292) baseStart_286292 baseEnd_286292 := by
    simpa [prefixWord, tailWord_286292, baseEnd_286292] using wordTrace_append hprefix tailTrace_286292
  have hstable : (prefixWord ++ tailWord_286292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286292).length < 2 ^ (prefixWord ++ tailWord_286292).sum := by decide
  have hdescent : baseEnd_286292 < baseStart_286292 := by decide
  rcases family_descends (prefixWord ++ tailWord_286292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286337 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 4]
def baseStart_286337 : Nat := 118140960795 + 286337 * 2 ^ 59
def prefixEnd_286337 : Nat := 4983230072969 + 3 ^ 40 * 286337 * 2
def baseEnd_286337 : Nat := 130692009036934612329481

theorem tailTrace_286337 : CollatzResearch.WordTrace tailWord_286337 prefixEnd_286337 130692009036934612329481 := by
  unfold tailWord_286337
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443568363657426311385265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6962378909104950874256843 10443568363657426311385265)
  ·
    refine ⟨7832676272743069733538949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10443568363657426311385265 7832676272743069733538949)
    ·
      refine ⟨1468626801139325575038553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7832676272743069733538949 1468626801139325575038553)
      ·
        refine ⟨1101470100854494181278915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1468626801139325575038553 1101470100854494181278915)
        ·
          refine ⟨1652205151281741271918373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101470100854494181278915 1652205151281741271918373)
          ·
            refine ⟨309788465865326488484695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1652205151281741271918373 309788465865326488484695)
            ·
              refine ⟨464682698797989732727043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309788465865326488484695 464682698797989732727043)
              ·
                refine ⟨697024048196984599090565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464682698797989732727043 697024048196984599090565)
                ·
                  refine ⟨130692009036934612329481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 697024048196984599090565 130692009036934612329481)
                  ·
                    rfl

theorem cell20_286337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_286337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286337 prefixEnd_286337 := by exact prefixLift 286337
  have htrace : WordTrace (prefixWord ++ tailWord_286337) baseStart_286337 baseEnd_286337 := by
    simpa [prefixWord, tailWord_286337, baseEnd_286337] using wordTrace_append hprefix tailTrace_286337
  have hstable : (prefixWord ++ tailWord_286337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286337).length < 2 ^ (prefixWord ++ tailWord_286337).sum := by decide
  have hdescent : baseEnd_286337 < baseStart_286337 := by decide
  rcases family_descends (prefixWord ++ tailWord_286337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286382 : List Nat := [4, 1, 4, 1, 2, 8]
def baseStart_286382 : Nat := 118140960795 + 286382 * 2 ^ 59
def prefixEnd_286382 : Nat := 4983230072969 + 3 ^ 40 * 286382 * 2
def baseEnd_286382 : Nat := 4841205491226461327011

theorem tailTrace_286382 : CollatzResearch.WordTrace tailWord_286382 prefixEnd_286382 4841205491226461327011 := by
  unfold tailWord_286382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305651206061799874596675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6963473098996265997848933 1305651206061799874596675)
  ·
    refine ⟨1958476809092699811895013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305651206061799874596675 1958476809092699811895013)
    ·
      refine ⟨367214401704881214730315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1958476809092699811895013 367214401704881214730315)
      ·
        refine ⟨550821602557321822095473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367214401704881214730315 550821602557321822095473)
        ·
          refine ⟨413116201917991366571605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550821602557321822095473 413116201917991366571605)
          ·
            refine ⟨4841205491226461327011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 413116201917991366571605 4841205491226461327011)
            ·
              rfl

theorem cell20_286382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 8].length) (baseStart_286382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286382 prefixEnd_286382 := by exact prefixLift 286382
  have htrace : WordTrace (prefixWord ++ tailWord_286382) baseStart_286382 baseEnd_286382 := by
    simpa [prefixWord, tailWord_286382, baseEnd_286382] using wordTrace_append hprefix tailTrace_286382
  have hstable : (prefixWord ++ tailWord_286382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286382).length < 2 ^ (prefixWord ++ tailWord_286382).sum := by decide
  have hdescent : baseEnd_286382 < baseStart_286382 := by decide
  rcases family_descends (prefixWord ++ tailWord_286382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_286413 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_286413 : Nat := 118140960795 + 286413 * 2 ^ 59
def prefixEnd_286413 : Nat := 4983230072969 + 3 ^ 40 * 286413 * 2
def baseEnd_286413 : Nat := 130726697507816125795837

theorem tailTrace_286413 : CollatzResearch.WordTrace tailWord_286413 prefixEnd_286413 130726697507816125795837 := by
  unfold tailWord_286413
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446340311382091291151893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6964226874254727527434595 10446340311382091291151893)
  ·
    refine ⟨489672202096035529272745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10446340311382091291151893 489672202096035529272745)
    ·
      refine ⟨367254151572026646954559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 489672202096035529272745 367254151572026646954559)
      ·
        refine ⟨550881227358039970431839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367254151572026646954559 550881227358039970431839)
        ·
          refine ⟨826321841037059955647759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550881227358039970431839 826321841037059955647759)
          ·
            refine ⟨1239482761555589933471639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826321841037059955647759 1239482761555589933471639)
            ·
              refine ⟨1859224142333384900207459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239482761555589933471639 1859224142333384900207459)
              ·
                refine ⟨2788836213500077350311189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859224142333384900207459 2788836213500077350311189)
                ·
                  refine ⟨130726697507816125795837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2788836213500077350311189 130726697507816125795837)
                  ·
                    rfl

theorem cell20_286413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_286413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_286413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_286413 prefixEnd_286413 := by exact prefixLift 286413
  have htrace : WordTrace (prefixWord ++ tailWord_286413) baseStart_286413 baseEnd_286413 := by
    simpa [prefixWord, tailWord_286413, baseEnd_286413] using wordTrace_append hprefix tailTrace_286413
  have hstable : (prefixWord ++ tailWord_286413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_286413).length < 2 ^ (prefixWord ++ tailWord_286413).sum := by decide
  have hdescent : baseEnd_286413 < baseStart_286413 := by decide
  rcases family_descends (prefixWord ++ tailWord_286413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
