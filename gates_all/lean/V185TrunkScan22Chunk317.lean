import V185TrunkScan22Chunk316

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2828194 : List Nat := [3, 3, 1, 2, 3, 1, 1, 8]
def baseStart_2828194 : Nat := 118140960795 + 2828194 * 2 ^ 59
def prefixEnd_2828194 : Nat := 4983230072969 + 3 ^ 40 * 2828194 * 2
def baseEnd_2828194 : Nat := 107572067123112067530991

theorem tailTrace_2828194 : CollatzResearch.WordTrace tailWord_2828194 prefixEnd_2828194 107572067123112067530991 := by
  unfold tailWord_2828194
  simp only [CollatzResearch.WordTrace]
  refine ⟨25788177378985907481338909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68768473010629086616903757 25788177378985907481338909)
  ·
    refine ⟨9670566517119715305502091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25788177378985907481338909 9670566517119715305502091)
    ·
      refine ⟨14505849775679572958253137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9670566517119715305502091 14505849775679572958253137)
      ·
        refine ⟨10879387331759679718689853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14505849775679572958253137 10879387331759679718689853)
        ·
          refine ⟨4079770249409879894508695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10879387331759679718689853 4079770249409879894508695)
          ·
            refine ⟨6119655374114819841763043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079770249409879894508695 6119655374114819841763043)
            ·
              refine ⟨9179483061172229762644565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119655374114819841763043 9179483061172229762644565)
              ·
                refine ⟨107572067123112067530991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9179483061172229762644565 107572067123112067530991)
                ·
                  rfl

theorem cell22_2828194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_2828194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828194 prefixEnd_2828194 := by exact prefixLift 2828194
  have htrace : WordTrace (prefixWord ++ tailWord_2828194) baseStart_2828194 baseEnd_2828194 := by
    simpa [prefixWord, tailWord_2828194, baseEnd_2828194] using wordTrace_append hprefix tailTrace_2828194
  have hstable : (prefixWord ++ tailWord_2828194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828194).length < 2 ^ (prefixWord ++ tailWord_2828194).sum := by decide
  have hdescent : baseEnd_2828194 < baseStart_2828194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828200 : List Nat := [2, 1, 6, 2, 1, 2, 1, 3, 4]
def baseStart_2828200 : Nat := 118140960795 + 2828200 * 2 ^ 59
def prefixEnd_2828200 : Nat := 4983230072969 + 3 ^ 40 * 2828200 * 2
def baseEnd_2828200 : Nat := 322716886010208864042967

theorem tailTrace_2828200 : CollatzResearch.WordTrace tailWord_2828200 prefixEnd_2828200 322716886010208864042967 := by
  unfold tailWord_2828200
  simp only [CollatzResearch.WordTrace]
  refine ⟨51576464176960946475037027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68768618902614595300049369 51576464176960946475037027)
  ·
    refine ⟨77364696265441419712555541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51576464176960946475037027 77364696265441419712555541)
    ·
      refine ⟨3626470137442566549026041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77364696265441419712555541 3626470137442566549026041)
      ·
        refine ⟨2719852603081924911769531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3626470137442566549026041 2719852603081924911769531)
        ·
          refine ⟨4079778904622887367654297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2719852603081924911769531 4079778904622887367654297)
          ·
            refine ⟨3059834178467165525740723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4079778904622887367654297 3059834178467165525740723)
            ·
              refine ⟨4589751267700748288611085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059834178467165525740723 4589751267700748288611085)
              ·
                refine ⟨1721156725387780608229157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4589751267700748288611085 1721156725387780608229157)
                ·
                  refine ⟨322716886010208864042967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721156725387780608229157 322716886010208864042967)
                  ·
                    rfl

theorem cell22_2828200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 4].length) (baseStart_2828200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828200 prefixEnd_2828200 := by exact prefixLift 2828200
  have htrace : WordTrace (prefixWord ++ tailWord_2828200) baseStart_2828200 baseEnd_2828200 := by
    simpa [prefixWord, tailWord_2828200, baseEnd_2828200] using wordTrace_append hprefix tailTrace_2828200
  have hstable : (prefixWord ++ tailWord_2828200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828200).length < 2 ^ (prefixWord ++ tailWord_2828200).sum := by decide
  have hdescent : baseEnd_2828200 < baseStart_2828200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828286 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2828286 : Nat := 118140960795 + 2828286 * 2 ^ 59
def prefixEnd_2828286 : Nat := 4983230072969 + 3 ^ 40 * 2828286 * 2
def baseEnd_2828286 : Nat := 968180097588151034478637

theorem tailTrace_2828286 : CollatzResearch.WordTrace tailWord_2828286 prefixEnd_2828286 968180097588151034478637 := by
  unfold tailWord_2828286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894508128951291204713089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68770710021073553091803141 12894508128951291204713089)
  ·
    refine ⟨9670881096713468403534817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12894508128951291204713089 9670881096713468403534817)
    ·
      refine ⟨7253160822535101302651113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9670881096713468403534817 7253160822535101302651113)
      ·
        refine ⟨5439870616901325976988335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7253160822535101302651113 5439870616901325976988335)
        ·
          refine ⟨8159805925351988965482503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5439870616901325976988335 8159805925351988965482503)
          ·
            refine ⟨12239708888027983448223755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8159805925351988965482503 12239708888027983448223755)
            ·
              refine ⟨18359563332041975172335633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12239708888027983448223755 18359563332041975172335633)
              ·
                refine ⟨13769672499031481379251725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18359563332041975172335633 13769672499031481379251725)
                ·
                  refine ⟨5163627187136805517219397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13769672499031481379251725 5163627187136805517219397)
                  ·
                    refine ⟨968180097588151034478637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163627187136805517219397 968180097588151034478637)
                    ·
                      rfl

theorem cell22_2828286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2828286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828286 prefixEnd_2828286 := by exact prefixLift 2828286
  have htrace : WordTrace (prefixWord ++ tailWord_2828286) baseStart_2828286 baseEnd_2828286 := by
    simpa [prefixWord, tailWord_2828286, baseEnd_2828286] using wordTrace_append hprefix tailTrace_2828286
  have hstable : (prefixWord ++ tailWord_2828286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828286).length < 2 ^ (prefixWord ++ tailWord_2828286).sum := by decide
  have hdescent : baseEnd_2828286 < baseStart_2828286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828299 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 1, 5]
def baseStart_2828299 : Nat := 118140960795 + 2828299 * 2 ^ 59
def prefixEnd_2828299 : Nat := 4983230072969 + 3 ^ 40 * 2828299 * 2
def baseEnd_2828299 : Nat := 968184547753823333903597

theorem tailTrace_2828299 : CollatzResearch.WordTrace tailWord_2828299 prefixEnd_2828299 968184547753823333903597 := by
  unfold tailWord_2828299
  simp only [CollatzResearch.WordTrace]
  refine ⟨103156539180563232857927951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68771026120375488571951967 103156539180563232857927951)
  ·
    refine ⟨154734808770844849286891927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103156539180563232857927951 154734808770844849286891927)
    ·
      refine ⟨232102213156267273930337891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154734808770844849286891927 232102213156267273930337891)
      ·
        refine ⟨348153319734400910895506837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232102213156267273930337891 348153319734400910895506837)
        ·
          refine ⟨16319686862550042698226883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 348153319734400910895506837 16319686862550042698226883)
          ·
            refine ⟨24479530293825064047340325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16319686862550042698226883 24479530293825064047340325)
            ·
              refine ⟨4589911930092199508876311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24479530293825064047340325 4589911930092199508876311)
              ·
                refine ⟨6884867895138299263314467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589911930092199508876311 6884867895138299263314467)
                ·
                  refine ⟨10327301842707448894971701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884867895138299263314467 10327301842707448894971701)
                  ·
                    refine ⟨968184547753823333903597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10327301842707448894971701 968184547753823333903597)
                    ·
                      rfl

theorem cell22_2828299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 5].length) (baseStart_2828299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828299 prefixEnd_2828299 := by exact prefixLift 2828299
  have htrace : WordTrace (prefixWord ++ tailWord_2828299) baseStart_2828299 baseEnd_2828299 := by
    simpa [prefixWord, tailWord_2828299, baseEnd_2828299] using wordTrace_append hprefix tailTrace_2828299
  have hstable : (prefixWord ++ tailWord_2828299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828299).length < 2 ^ (prefixWord ++ tailWord_2828299).sum := by decide
  have hdescent : baseEnd_2828299 < baseStart_2828299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828314 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 1, 6]
def baseStart_2828314 : Nat := 118140960795 + 2828314 * 2 ^ 59
def prefixEnd_2828314 : Nat := 4983230072969 + 3 ^ 40 * 2828314 * 2
def baseEnd_2828314 : Nat := 968189682560368294778551

theorem tailTrace_2828314 : CollatzResearch.WordTrace tailWord_2828314 prefixEnd_2828314 968189682560368294778551 := by
  unfold tailWord_2828314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25789271568877222604930999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68771390850339260279815997 25789271568877222604930999)
  ·
    refine ⟨38683907353315833907396499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25789271568877222604930999 38683907353315833907396499)
    ·
      refine ⟨58025861029973750861094749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38683907353315833907396499 58025861029973750861094749)
      ·
        refine ⟨21759697886240156572910531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58025861029973750861094749 21759697886240156572910531)
        ·
          refine ⟨32639546829360234859365797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21759697886240156572910531 32639546829360234859365797)
          ·
            refine ⟨6119915030505044036131087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32639546829360234859365797 6119915030505044036131087)
            ·
              refine ⟨9179872545757566054196631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119915030505044036131087 9179872545757566054196631)
              ·
                refine ⟨13769808818636349081294947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9179872545757566054196631 13769808818636349081294947)
                ·
                  refine ⟨20654713227954523621942421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13769808818636349081294947 20654713227954523621942421)
                  ·
                    refine ⟨968189682560368294778551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20654713227954523621942421 968189682560368294778551)
                    ·
                      rfl

theorem cell22_2828314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_2828314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828314 prefixEnd_2828314 := by exact prefixLift 2828314
  have htrace : WordTrace (prefixWord ++ tailWord_2828314) baseStart_2828314 baseEnd_2828314 := by
    simpa [prefixWord, tailWord_2828314, baseEnd_2828314] using wordTrace_append hprefix tailTrace_2828314
  have hstable : (prefixWord ++ tailWord_2828314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828314).length < 2 ^ (prefixWord ++ tailWord_2828314).sum := by decide
  have hdescent : baseEnd_2828314 < baseStart_2828314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828350 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2828350 : Nat := 118140960795 + 2828350 * 2 ^ 59
def prefixEnd_2828350 : Nat := 4983230072969 + 3 ^ 40 * 2828350 * 2
def baseEnd_2828350 : Nat := 968202006096076200878441

theorem tailTrace_2828350 : CollatzResearch.WordTrace tailWord_2828350 prefixEnd_2828350 968202006096076200878441 := by
  unfold tailWord_2828350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12894799912922308571004313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68772266202252312378689669 12894799912922308571004313)
  ·
    refine ⟨9671099934691731428253235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12894799912922308571004313 9671099934691731428253235)
    ·
      refine ⟨14506649902037597142379853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9671099934691731428253235 14506649902037597142379853)
      ·
        refine ⟨5439993713264098928392445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14506649902037597142379853 5439993713264098928392445)
        ·
          refine ⟨2039997642474037098147167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5439993713264098928392445 2039997642474037098147167)
          ·
            refine ⟨3059996463711055647220751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039997642474037098147167 3059996463711055647220751)
            ·
              refine ⟨4589994695566583470831127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059996463711055647220751 4589994695566583470831127)
              ·
                refine ⟨6884992043349875206246691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4589994695566583470831127 6884992043349875206246691)
                ·
                  refine ⟨10327488065024812809370037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6884992043349875206246691 10327488065024812809370037)
                  ·
                    refine ⟨968202006096076200878441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10327488065024812809370037 968202006096076200878441)
                    ·
                      rfl

theorem cell22_2828350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2828350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828350 prefixEnd_2828350 := by exact prefixLift 2828350
  have htrace : WordTrace (prefixWord ++ tailWord_2828350) baseStart_2828350 baseEnd_2828350 := by
    simpa [prefixWord, tailWord_2828350, baseEnd_2828350] using wordTrace_append hprefix tailTrace_2828350
  have hstable : (prefixWord ++ tailWord_2828350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828350).length < 2 ^ (prefixWord ++ tailWord_2828350).sum := by decide
  have hdescent : baseEnd_2828350 < baseStart_2828350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828421 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_2828421 : Nat := 118140960795 + 2828421 * 2 ^ 59
def prefixEnd_2828421 : Nat := 4983230072969 + 3 ^ 40 * 2828421 * 2
def baseEnd_2828421 : Nat := 968226310847055682353223

theorem tailTrace_2828421 : CollatzResearch.WordTrace tailWord_2828421 prefixEnd_2828421 968226310847055682353223 := by
  unfold tailWord_2828421
  simp only [CollatzResearch.WordTrace]
  refine ⟨103160988886121247693869117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68773992590747498462579411 103160988886121247693869117)
  ·
    refine ⟨38685370832295467885200919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103160988886121247693869117 38685370832295467885200919)
    ·
      refine ⟨58028056248443201827801379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38685370832295467885200919 58028056248443201827801379)
      ·
        refine ⟨87042084372664802741702069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58028056248443201827801379 87042084372664802741702069)
        ·
          refine ⟨8160195409937325257034569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87042084372664802741702069 8160195409937325257034569)
          ·
            refine ⟨6120146557452993942775927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8160195409937325257034569 6120146557452993942775927)
            ·
              refine ⟨9180219836179490914163891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120146557452993942775927 9180219836179490914163891)
              ·
                refine ⟨13770329754269236371245837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180219836179490914163891 13770329754269236371245837)
                ·
                  refine ⟨5163873657850963639217189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13770329754269236371245837 5163873657850963639217189)
                  ·
                    refine ⟨968226310847055682353223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163873657850963639217189 968226310847055682353223)
                    ·
                      rfl

theorem cell22_2828421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_2828421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828421 prefixEnd_2828421 := by exact prefixLift 2828421
  have htrace : WordTrace (prefixWord ++ tailWord_2828421) baseStart_2828421 baseEnd_2828421 := by
    simpa [prefixWord, tailWord_2828421, baseEnd_2828421] using wordTrace_append hprefix tailTrace_2828421
  have hstable : (prefixWord ++ tailWord_2828421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828421).length < 2 ^ (prefixWord ++ tailWord_2828421).sum := by decide
  have hdescent : baseEnd_2828421 < baseStart_2828421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828446 : List Nat := [4, 3, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_2828446 : Nat := 118140960795 + 2828446 * 2 ^ 59
def prefixEnd_2828446 : Nat := 4983230072969 + 3 ^ 40 * 2828446 * 2
def baseEnd_2828446 : Nat := 968234868857963950478147

theorem tailTrace_2828446 : CollatzResearch.WordTrace tailWord_2828446 prefixEnd_2828446 968234868857963950478147 := by
  unfold tailWord_2828446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895237588878834620441149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68774600474020451309019461 12895237588878834620441149)
  ·
    refine ⟨4835714095829562982665431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12895237588878834620441149 4835714095829562982665431)
    ·
      refine ⟨7253571143744344473998147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835714095829562982665431 7253571143744344473998147)
      ·
        refine ⟨10880356715616516710997221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253571143744344473998147 10880356715616516710997221)
        ·
          refine ⟨2040066884178096883311979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10880356715616516710997221 2040066884178096883311979)
          ·
            refine ⟨3060100326267145324967969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040066884178096883311979 3060100326267145324967969)
            ·
              refine ⟨2295075244700358993725977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3060100326267145324967969 2295075244700358993725977)
              ·
                refine ⟨1721306433525269245294483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2295075244700358993725977 1721306433525269245294483)
                ·
                  refine ⟨2581959650287903867941725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721306433525269245294483 2581959650287903867941725)
                  ·
                    refine ⟨968234868857963950478147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2581959650287903867941725 968234868857963950478147)
                    ·
                      rfl

theorem cell22_2828446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_2828446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828446 prefixEnd_2828446 := by exact prefixLift 2828446
  have htrace : WordTrace (prefixWord ++ tailWord_2828446) baseStart_2828446 baseEnd_2828446 := by
    simpa [prefixWord, tailWord_2828446, baseEnd_2828446] using wordTrace_append hprefix tailTrace_2828446
  have hstable : (prefixWord ++ tailWord_2828446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828446).length < 2 ^ (prefixWord ++ tailWord_2828446).sum := by decide
  have hdescent : baseEnd_2828446 < baseStart_2828446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828502 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2828502 : Nat := 118140960795 + 2828502 * 2 ^ 59
def prefixEnd_2828502 : Nat := 4983230072969 + 3 ^ 40 * 2828502 * 2
def baseEnd_2828502 : Nat := 968254038802398471077975

theorem tailTrace_2828502 : CollatzResearch.WordTrace tailWord_2828502 prefixEnd_2828502 968254038802398471077975 := by
  unfold tailWord_2828502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447746449926737407972985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68775962132551865685045173 6447746449926737407972985)
  ·
    refine ⟨4835809837445053055979739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6447746449926737407972985 4835809837445053055979739)
    ·
      refine ⟨7253714756167579583969609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835809837445053055979739 7253714756167579583969609)
      ·
        refine ⟨5440286067125684687977207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7253714756167579583969609 5440286067125684687977207)
        ·
          refine ⟨8160429100688527031965811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440286067125684687977207 8160429100688527031965811)
          ·
            refine ⟨12240643651032790547948717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8160429100688527031965811 12240643651032790547948717)
            ·
              refine ⟨4590241369137296455480769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12240643651032790547948717 4590241369137296455480769)
              ·
                refine ⟨3442681026852972341610577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4590241369137296455480769 3442681026852972341610577)
                ·
                  refine ⟨2582010770139729256207933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442681026852972341610577 2582010770139729256207933)
                  ·
                    refine ⟨968254038802398471077975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582010770139729256207933 968254038802398471077975)
                    ·
                      rfl

theorem cell22_2828502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2828502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828502 prefixEnd_2828502 := by exact prefixLift 2828502
  have htrace : WordTrace (prefixWord ++ tailWord_2828502) baseStart_2828502 baseEnd_2828502 := by
    simpa [prefixWord, tailWord_2828502, baseEnd_2828502] using wordTrace_append hprefix tailTrace_2828502
  have hstable : (prefixWord ++ tailWord_2828502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828502).length < 2 ^ (prefixWord ++ tailWord_2828502).sum := by decide
  have hdescent : baseEnd_2828502 < baseStart_2828502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828513 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_2828513 : Nat := 118140960795 + 2828513 * 2 ^ 59
def prefixEnd_2828513 : Nat := 4983230072969 + 3 ^ 40 * 2828513 * 2
def baseEnd_2828513 : Nat := 968257804327198109052941

theorem tailTrace_2828513 : CollatzResearch.WordTrace tailWord_2828513 prefixEnd_2828513 968257804327198109052941 := by
  unfold tailWord_2828513
  simp only [CollatzResearch.WordTrace]
  refine ⟨103164344401787947406218193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68776229601191964937478795 103164344401787947406218193)
  ·
    refine ⟨77373258301340960554663645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103164344401787947406218193 77373258301340960554663645)
    ·
      refine ⟨29014971863002860207998867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77373258301340960554663645 29014971863002860207998867)
      ·
        refine ⟨43522457794504290311998301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29014971863002860207998867 43522457794504290311998301)
        ·
          refine ⟨16320921672939108866999363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43522457794504290311998301 16320921672939108866999363)
          ·
            refine ⟨24481382509408663300499045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16320921672939108866999363 24481382509408663300499045)
            ·
              refine ⟨4590259220514124368843571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24481382509408663300499045 4590259220514124368843571)
              ·
                refine ⟨6885388830771186553265357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590259220514124368843571 6885388830771186553265357)
                ·
                  refine ⟨2582020811539194957474509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6885388830771186553265357 2582020811539194957474509)
                  ·
                    refine ⟨968257804327198109052941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582020811539194957474509 968257804327198109052941)
                    ·
                      rfl

theorem cell22_2828513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_2828513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828513 prefixEnd_2828513 := by exact prefixLift 2828513
  have htrace : WordTrace (prefixWord ++ tailWord_2828513) baseStart_2828513 baseEnd_2828513 := by
    simpa [prefixWord, tailWord_2828513, baseEnd_2828513] using wordTrace_append hprefix tailTrace_2828513
  have hstable : (prefixWord ++ tailWord_2828513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828513).length < 2 ^ (prefixWord ++ tailWord_2828513).sum := by decide
  have hdescent : baseEnd_2828513 < baseStart_2828513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828539 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_2828539 : Nat := 118140960795 + 2828539 * 2 ^ 59
def prefixEnd_2828539 : Nat := 4983230072969 + 3 ^ 40 * 2828539 * 2
def baseEnd_2828539 : Nat := 968266704658542707902861

theorem tailTrace_2828539 : CollatzResearch.WordTrace tailWord_2828539 prefixEnd_2828539 968266704658542707902861 := by
  unfold tailWord_2828539
  simp only [CollatzResearch.WordTrace]
  refine ⟨103165292699693753846664671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68776861799795835897776447 103165292699693753846664671)
  ·
    refine ⟨154747939049540630769997007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103165292699693753846664671 154747939049540630769997007)
    ·
      refine ⟨232121908574310946154995511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154747939049540630769997007 232121908574310946154995511)
      ·
        refine ⟨348182862861466419232493267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232121908574310946154995511 348182862861466419232493267)
        ·
          refine ⟨522274294292199628848739901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348182862861466419232493267 522274294292199628848739901)
          ·
            refine ⟨195852860359574860818277463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522274294292199628848739901 195852860359574860818277463)
            ·
              refine ⟨293779290539362291227416195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195852860359574860818277463 293779290539362291227416195)
              ·
                refine ⟨440668935809043436841124293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293779290539362291227416195 440668935809043436841124293)
                ·
                  refine ⟨82625425464195644407710805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440668935809043436841124293 82625425464195644407710805)
                  ·
                    refine ⟨968266704658542707902861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82625425464195644407710805 968266704658542707902861)
                    ·
                      rfl

theorem cell22_2828539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_2828539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828539 prefixEnd_2828539 := by exact prefixLift 2828539
  have htrace : WordTrace (prefixWord ++ tailWord_2828539) baseStart_2828539 baseEnd_2828539 := by
    simpa [prefixWord, tailWord_2828539, baseEnd_2828539] using wordTrace_append hprefix tailTrace_2828539
  have hstable : (prefixWord ++ tailWord_2828539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828539).length < 2 ^ (prefixWord ++ tailWord_2828539).sum := by decide
  have hdescent : baseEnd_2828539 < baseStart_2828539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828571 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 6]
def baseStart_2828571 : Nat := 118140960795 + 2828571 * 2 ^ 59
def prefixEnd_2828571 : Nat := 4983230072969 + 3 ^ 40 * 2828571 * 2
def baseEnd_2828571 : Nat := 322759219637501763700921

theorem tailTrace_2828571 : CollatzResearch.WordTrace tailWord_2828571 prefixEnd_2828571 322759219637501763700921 := by
  unfold tailWord_2828571
  simp only [CollatzResearch.WordTrace]
  refine ⟨103166459835577823311829567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68777639890385215541219711 103166459835577823311829567)
  ·
    refine ⟨154749689753366734967744351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103166459835577823311829567 154749689753366734967744351)
    ·
      refine ⟨232124534630050102451616527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154749689753366734967744351 232124534630050102451616527)
      ·
        refine ⟨348186801945075153677424791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232124534630050102451616527 348186801945075153677424791)
        ·
          refine ⟨522280202917612730516137187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348186801945075153677424791 522280202917612730516137187)
          ·
            refine ⟨783420304376419095774205781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522280202917612730516137187 783420304376419095774205781)
            ·
              refine ⟨4590353345955580639301987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 783420304376419095774205781 4590353345955580639301987)
              ·
                refine ⟨6885530018933370958952981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590353345955580639301987 6885530018933370958952981)
                ·
                  refine ⟨322759219637501763700921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6885530018933370958952981 322759219637501763700921)
                  ·
                    rfl

theorem cell22_2828571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 6].length) (baseStart_2828571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828571 prefixEnd_2828571 := by exact prefixLift 2828571
  have htrace : WordTrace (prefixWord ++ tailWord_2828571) baseStart_2828571 baseEnd_2828571 := by
    simpa [prefixWord, tailWord_2828571, baseEnd_2828571] using wordTrace_append hprefix tailTrace_2828571
  have hstable : (prefixWord ++ tailWord_2828571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828571).length < 2 ^ (prefixWord ++ tailWord_2828571).sum := by decide
  have hdescent : baseEnd_2828571 < baseStart_2828571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828620 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_2828620 : Nat := 118140960795 + 2828620 * 2 ^ 59
def prefixEnd_2828620 : Nat := 4983230072969 + 3 ^ 40 * 2828620 * 2
def baseEnd_2828620 : Nat := 968294432613885496627613

theorem tailTrace_2828620 : CollatzResearch.WordTrace tailWord_2828620 prefixEnd_2828620 968294432613885496627613 := by
  unfold tailWord_2828620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51584123506200152340181657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68778831341600203120242209 51584123506200152340181657)
  ·
    refine ⟨38688092629650114255136243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51584123506200152340181657 38688092629650114255136243)
    ·
      refine ⟨58032138944475171382704365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38688092629650114255136243 58032138944475171382704365)
      ·
        refine ⟨21762052104178189268514137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58032138944475171382704365 21762052104178189268514137)
        ·
          refine ⟨16321539078133641951385603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21762052104178189268514137 16321539078133641951385603)
          ·
            refine ⟨24482308617200462927078405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16321539078133641951385603 24482308617200462927078405)
            ·
              refine ⟨4590432865725086798827201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24482308617200462927078405 4590432865725086798827201)
              ·
                refine ⟨3442824649293815099120401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4590432865725086798827201 3442824649293815099120401)
                ·
                  refine ⟨2582118486970361324340301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3442824649293815099120401 2582118486970361324340301)
                  ·
                    refine ⟨968294432613885496627613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582118486970361324340301 968294432613885496627613)
                    ·
                      rfl

theorem cell22_2828620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_2828620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828620 prefixEnd_2828620 := by exact prefixLift 2828620
  have htrace : WordTrace (prefixWord ++ tailWord_2828620) baseStart_2828620 baseEnd_2828620 := by
    simpa [prefixWord, tailWord_2828620, baseEnd_2828620] using wordTrace_append hprefix tailTrace_2828620
  have hstable : (prefixWord ++ tailWord_2828620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828620).length < 2 ^ (prefixWord ++ tailWord_2828620).sum := by decide
  have hdescent : baseEnd_2828620 < baseStart_2828620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828650 : List Nat := [3, 1, 3, 3, 1, 2, 3, 6]
def baseStart_2828650 : Nat := 118140960795 + 2828650 * 2 ^ 59
def prefixEnd_2828650 : Nat := 4983230072969 + 3 ^ 40 * 2828650 * 2
def baseEnd_2828650 : Nat := 107589411358552824264169

theorem tailTrace_2828650 : CollatzResearch.WordTrace tailWord_2828650 prefixEnd_2828650 107589411358552824264169 := by
  unfold tailWord_2828650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25792335300572904950988851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68779560801527746535970269 25792335300572904950988851)
  ·
    refine ⟨38688502950859357426483277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25792335300572904950988851 38688502950859357426483277)
    ·
      refine ⟨14508188606572259034931229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38688502950859357426483277 14508188606572259034931229)
      ·
        refine ⟨5440570727464597138099211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14508188606572259034931229 5440570727464597138099211)
        ·
          refine ⟨8160856091196895707148817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440570727464597138099211 8160856091196895707148817)
          ·
            refine ⟨6120642068397671780361613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8160856091196895707148817 6120642068397671780361613)
            ·
              refine ⟨2295240775649126917635605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6120642068397671780361613 2295240775649126917635605)
              ·
                refine ⟨107589411358552824264169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2295240775649126917635605 107589411358552824264169)
                ·
                  rfl

theorem cell22_2828650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_2828650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828650 prefixEnd_2828650 := by exact prefixLift 2828650
  have htrace : WordTrace (prefixWord ++ tailWord_2828650) baseStart_2828650 baseEnd_2828650 := by
    simpa [prefixWord, tailWord_2828650, baseEnd_2828650] using wordTrace_append hprefix tailTrace_2828650
  have hstable : (prefixWord ++ tailWord_2828650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828650).length < 2 ^ (prefixWord ++ tailWord_2828650).sum := by decide
  have hdescent : baseEnd_2828650 < baseStart_2828650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828652 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_2828652 : Nat := 118140960795 + 2828652 * 2 ^ 59
def prefixEnd_2828652 : Nat := 4983230072969 + 3 ^ 40 * 2828652 * 2
def baseEnd_2828652 : Nat := 968305386867848079827515

theorem tailTrace_2828652 : CollatzResearch.WordTrace tailWord_2828652 prefixEnd_2828652 968305386867848079827515 := by
  unfold tailWord_2828652
  simp only [CollatzResearch.WordTrace]
  refine ⟨51584707074142187072764105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68779609432189582763685473 51584707074142187072764105)
  ·
    refine ⟨38688530305606640304573079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51584707074142187072764105 38688530305606640304573079)
    ·
      refine ⟨58032795458409960456859619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38688530305606640304573079 58032795458409960456859619)
      ·
        refine ⟨87049193187614940685289429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58032795458409960456859619 87049193187614940685289429)
        ·
          refine ⟨2040215465334725172311471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 87049193187614940685289429 2040215465334725172311471)
          ·
            refine ⟨3060323198002087758467207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040215465334725172311471 3060323198002087758467207)
            ·
              refine ⟨4590484797003131637700811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060323198002087758467207 4590484797003131637700811)
              ·
                refine ⟨6885727195504697456551217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590484797003131637700811 6885727195504697456551217)
                ·
                  refine ⟨5164295396628523092413413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6885727195504697456551217 5164295396628523092413413)
                  ·
                    refine ⟨968305386867848079827515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164295396628523092413413 968305386867848079827515)
                    ·
                      rfl

theorem cell22_2828652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_2828652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828652 prefixEnd_2828652 := by exact prefixLift 2828652
  have htrace : WordTrace (prefixWord ++ tailWord_2828652) baseStart_2828652 baseEnd_2828652 := by
    simpa [prefixWord, tailWord_2828652, baseEnd_2828652] using wordTrace_append hprefix tailTrace_2828652
  have hstable : (prefixWord ++ tailWord_2828652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828652).length < 2 ^ (prefixWord ++ tailWord_2828652).sum := by decide
  have hdescent : baseEnd_2828652 < baseStart_2828652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828708 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2828708 : Nat := 118140960795 + 2828708 * 2 ^ 59
def prefixEnd_2828708 : Nat := 4983230072969 + 3 ^ 40 * 2828708 * 2
def baseEnd_2828708 : Nat := 968324556812282600427343

theorem tailTrace_2828708 : CollatzResearch.WordTrace tailWord_2828708 prefixEnd_2828708 968324556812282600427343 := by
  unfold tailWord_2828708
  simp only [CollatzResearch.WordTrace]
  refine ⟨51585728318040747854783389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68780971090720997139711185 51585728318040747854783389)
  ·
    refine ⟨19344648119265280445543771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51585728318040747854783389 19344648119265280445543771)
    ·
      refine ⟨29016972178897920668315657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19344648119265280445543771 29016972178897920668315657)
      ·
        refine ⟨21762729134173440501236743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29016972178897920668315657 21762729134173440501236743)
        ·
          refine ⟨32644093701260160751855115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21762729134173440501236743 32644093701260160751855115)
          ·
            refine ⟨48966140551890241127782673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32644093701260160751855115 48966140551890241127782673)
            ·
              refine ⟨36724605413917680845837005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48966140551890241127782673 36724605413917680845837005)
              ·
                refine ⟨13771727030219130317188877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36724605413917680845837005 13771727030219130317188877)
                ·
                  refine ⟨5164397636332173868945829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13771727030219130317188877 5164397636332173868945829)
                  ·
                    refine ⟨968324556812282600427343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164397636332173868945829 968324556812282600427343)
                    ·
                      rfl

theorem cell22_2828708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2828708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828708 prefixEnd_2828708 := by exact prefixLift 2828708
  have htrace : WordTrace (prefixWord ++ tailWord_2828708) baseStart_2828708 baseEnd_2828708 := by
    simpa [prefixWord, tailWord_2828708, baseEnd_2828708] using wordTrace_append hprefix tailTrace_2828708
  have hstable : (prefixWord ++ tailWord_2828708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828708).length < 2 ^ (prefixWord ++ tailWord_2828708).sum := by decide
  have hdescent : baseEnd_2828708 < baseStart_2828708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828806 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2828806 : Nat := 118140960795 + 2828806 * 2 ^ 59
def prefixEnd_2828806 : Nat := 4983230072969 + 3 ^ 40 * 2828806 * 2
def baseEnd_2828806 : Nat := 968358104215043011477043

theorem tailTrace_2828806 : CollatzResearch.WordTrace tailWord_2828806 prefixEnd_2828806 968358104215043011477043 := by
  unfold tailWord_2828806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224219718428951826457321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68783353993150972297756181 3224219718428951826457321)
  ·
    refine ⟨2418164788821713869842991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3224219718428951826457321 2418164788821713869842991)
    ·
      refine ⟨3627247183232570804764487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418164788821713869842991 3627247183232570804764487)
      ·
        refine ⟨5440870774848856207146731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627247183232570804764487 5440870774848856207146731)
        ·
          refine ⟨8161306162273284310720097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440870774848856207146731 8161306162273284310720097)
          ·
            refine ⟨6120979621704963233040073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8161306162273284310720097 6120979621704963233040073)
            ·
              refine ⟨4590734716278722424780055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6120979621704963233040073 4590734716278722424780055)
              ·
                refine ⟨6886102074418083637170083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590734716278722424780055 6886102074418083637170083)
                ·
                  refine ⟨10329153111627125455755125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6886102074418083637170083 10329153111627125455755125)
                  ·
                    refine ⟨968358104215043011477043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10329153111627125455755125 968358104215043011477043)
                    ·
                      rfl

theorem cell22_2828806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2828806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828806 prefixEnd_2828806 := by exact prefixLift 2828806
  have htrace : WordTrace (prefixWord ++ tailWord_2828806) baseStart_2828806 baseEnd_2828806 := by
    simpa [prefixWord, tailWord_2828806, baseEnd_2828806] using wordTrace_append hprefix tailTrace_2828806
  have hstable : (prefixWord ++ tailWord_2828806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828806).length < 2 ^ (prefixWord ++ tailWord_2828806).sum := by decide
  have hdescent : baseEnd_2828806 < baseStart_2828806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2828924 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_2828924 : Nat := 118140960795 + 2828924 * 2 ^ 59
def prefixEnd_2828924 : Nat := 4983230072969 + 3 ^ 40 * 2828924 * 2
def baseEnd_2828924 : Nat := 968398498026530037026681

theorem tailTrace_2828924 : CollatzResearch.WordTrace tailWord_2828924 prefixEnd_2828924 968398498026530037026681 := by
  unfold tailWord_2828924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51589667401649482299714913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68786223202199309732953217 51589667401649482299714913)
  ·
    refine ⟨38692250551237111724786185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51589667401649482299714913 38692250551237111724786185)
    ·
      refine ⟨29019187913427833793589639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38692250551237111724786185 29019187913427833793589639)
      ·
        refine ⟨43528781870141750690384459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29019187913427833793589639 43528781870141750690384459)
        ·
          refine ⟨65293172805212626035576689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43528781870141750690384459 65293172805212626035576689)
          ·
            refine ⟨48969879603909469526682517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65293172805212626035576689 48969879603909469526682517)
            ·
              refine ⟨2295463106433256384063243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48969879603909469526682517 2295463106433256384063243)
              ·
                refine ⟨3443194659649884576094865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295463106433256384063243 3443194659649884576094865)
                ·
                  refine ⟨2582395994737413432071149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3443194659649884576094865 2582395994737413432071149)
                  ·
                    refine ⟨968398498026530037026681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582395994737413432071149 968398498026530037026681)
                    ·
                      rfl

theorem cell22_2828924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_2828924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2828924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2828924 prefixEnd_2828924 := by exact prefixLift 2828924
  have htrace : WordTrace (prefixWord ++ tailWord_2828924) baseStart_2828924 baseEnd_2828924 := by
    simpa [prefixWord, tailWord_2828924, baseEnd_2828924] using wordTrace_append hprefix tailTrace_2828924
  have hstable : (prefixWord ++ tailWord_2828924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2828924).length < 2 ^ (prefixWord ++ tailWord_2828924).sum := by decide
  have hdescent : baseEnd_2828924 < baseStart_2828924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2828924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829027 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 6]
def baseStart_2829027 : Nat := 118140960795 + 2829027 * 2 ^ 59
def prefixEnd_2829027 : Nat := 4983230072969 + 3 ^ 40 * 2829027 * 2
def baseEnd_2829027 : Nat := 322811252343824033900455

theorem tailTrace_2829027 : CollatzResearch.WordTrace tailWord_2829027 prefixEnd_2829027 322811252343824033900455 := by
  unfold tailWord_2829027
  simp only [CollatzResearch.WordTrace]
  refine ⟨103183091521925813190429335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68788727681283875460286223 103183091521925813190429335)
  ·
    refine ⟨154774637282888719785644003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103183091521925813190429335 154774637282888719785644003)
    ·
      refine ⟨232161955924333079678466005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154774637282888719785644003 232161955924333079678466005)
      ·
        refine ⟨5441295841976556554964047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 232161955924333079678466005 5441295841976556554964047)
        ·
          refine ⟨8161943762964834832446071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441295841976556554964047 8161943762964834832446071)
          ·
            refine ⟨12242915644447252248669107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161943762964834832446071 12242915644447252248669107)
            ·
              refine ⟨18364373466670878373003661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12242915644447252248669107 18364373466670878373003661)
              ·
                refine ⟨6886640050001579389876373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18364373466670878373003661 6886640050001579389876373)
                ·
                  refine ⟨322811252343824033900455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6886640050001579389876373 322811252343824033900455)
                  ·
                    rfl

theorem cell22_2829027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 6].length) (baseStart_2829027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829027 prefixEnd_2829027 := by exact prefixLift 2829027
  have htrace : WordTrace (prefixWord ++ tailWord_2829027) baseStart_2829027 baseEnd_2829027 := by
    simpa [prefixWord, tailWord_2829027, baseEnd_2829027] using wordTrace_append hprefix tailTrace_2829027
  have hstable : (prefixWord ++ tailWord_2829027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829027).length < 2 ^ (prefixWord ++ tailWord_2829027).sum := by decide
  have hdescent : baseEnd_2829027 < baseStart_2829027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829040 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_2829040 : Nat := 118140960795 + 2829040 * 2 ^ 59
def prefixEnd_2829040 : Nat := 4983230072969 + 3 ^ 40 * 2829040 * 2
def baseEnd_2829040 : Nat := 968438207197144401126325

theorem tailTrace_2829040 : CollatzResearch.WordTrace tailWord_2829040 prefixEnd_2829040 968438207197144401126325 := by
  unfold tailWord_2829040
  simp only [CollatzResearch.WordTrace]
  refine ⟨51591782835439358205326287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68789043780585810940435049 51591782835439358205326287)
  ·
    refine ⟨77387674253159037307989431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51591782835439358205326287 77387674253159037307989431)
    ·
      refine ⟨116081511379738555961984147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77387674253159037307989431 116081511379738555961984147)
      ·
        refine ⟨174122267069607833942976221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116081511379738555961984147 174122267069607833942976221)
        ·
          refine ⟨65295850151102937728616083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174122267069607833942976221 65295850151102937728616083)
          ·
            refine ⟨97943775226654406592924125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65295850151102937728616083 97943775226654406592924125)
            ·
              refine ⟨36728915709995402472346547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97943775226654406592924125 36728915709995402472346547)
              ·
                refine ⟨55093373564993103708519821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36728915709995402472346547 55093373564993103708519821)
                ·
                  refine ⟨20660015086872413890694933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55093373564993103708519821 20660015086872413890694933)
                  ·
                    refine ⟨968438207197144401126325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20660015086872413890694933 968438207197144401126325)
                    ·
                      rfl

theorem cell22_2829040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_2829040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829040 prefixEnd_2829040 := by exact prefixLift 2829040
  have htrace : WordTrace (prefixWord ++ tailWord_2829040) baseStart_2829040 baseEnd_2829040 := by
    simpa [prefixWord, tailWord_2829040, baseEnd_2829040] using wordTrace_append hprefix tailTrace_2829040
  have hstable : (prefixWord ++ tailWord_2829040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829040).length < 2 ^ (prefixWord ++ tailWord_2829040).sum := by decide
  have hdescent : baseEnd_2829040 < baseStart_2829040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829057 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2829057 : Nat := 118140960795 + 2829057 * 2 ^ 59
def prefixEnd_2829057 : Nat := 4983230072969 + 3 ^ 40 * 2829057 * 2
def baseEnd_2829057 : Nat := 968444026644562023451273

theorem tailTrace_2829057 : CollatzResearch.WordTrace tailWord_2829057 prefixEnd_2829057 968444026644562023451273 := by
  unfold tailWord_2829057
  simp only [CollatzResearch.WordTrace]
  refine ⟨103184185711817128314021425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68789457141211418876014283 103184185711817128314021425)
  ·
    refine ⟨77388139283862846235516069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103184185711817128314021425 77388139283862846235516069)
    ·
      refine ⟨14510276115724283669159263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77388139283862846235516069 14510276115724283669159263)
      ·
        refine ⟨21765414173586425503738895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14510276115724283669159263 21765414173586425503738895)
        ·
          refine ⟨32648121260379638255608343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21765414173586425503738895 32648121260379638255608343)
          ·
            refine ⟨48972181890569457383412515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32648121260379638255608343 48972181890569457383412515)
            ·
              refine ⟨73458272835854186075118773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48972181890569457383412515 73458272835854186075118773)
              ·
                refine ⟨6886713078361329944542385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73458272835854186075118773 6886713078361329944542385)
                ·
                  refine ⟨5165034808770997458406789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6886713078361329944542385 5165034808770997458406789)
                  ·
                    refine ⟨968444026644562023451273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165034808770997458406789 968444026644562023451273)
                    ·
                      rfl

theorem cell22_2829057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2829057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829057 prefixEnd_2829057 := by exact prefixLift 2829057
  have htrace : WordTrace (prefixWord ++ tailWord_2829057) baseStart_2829057 baseEnd_2829057 := by
    simpa [prefixWord, tailWord_2829057, baseEnd_2829057] using wordTrace_append hprefix tailTrace_2829057
  have hstable : (prefixWord ++ tailWord_2829057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829057).length < 2 ^ (prefixWord ++ tailWord_2829057).sum := by decide
  have hdescent : baseEnd_2829057 < baseStart_2829057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829164 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_2829164 : Nat := 118140960795 + 2829164 * 2 ^ 59
def prefixEnd_2829164 : Nat := 4983230072969 + 3 ^ 40 * 2829164 * 2
def baseEnd_2829164 : Nat := 968480654931249411025945

theorem tailTrace_2829164 : CollatzResearch.WordTrace tailWord_2829164 prefixEnd_2829164 968480654931249411025945 := by
  unfold tailWord_2829164
  simp only [CollatzResearch.WordTrace]
  refine ⟨51594044161214742794083273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68792058881619657058777697 51594044161214742794083273)
  ·
    refine ⟨38695533120911057095562455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51594044161214742794083273 38695533120911057095562455)
    ·
      refine ⟨58043299681366585643343683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38695533120911057095562455 58043299681366585643343683)
      ·
        refine ⟨87064949522049878465015525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58043299681366585643343683 87064949522049878465015525)
        ·
          refine ⟨16324678035384352212190411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87064949522049878465015525 16324678035384352212190411)
          ·
            refine ⟨24487017053076528318285617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16324678035384352212190411 24487017053076528318285617)
            ·
              refine ⟨18365262789807396238714213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24487017053076528318285617 18365262789807396238714213)
              ·
                refine ⟨3443486773088886794758915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18365262789807396238714213 3443486773088886794758915)
                ·
                  refine ⟨5165230159633330192138373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443486773088886794758915 5165230159633330192138373)
                  ·
                    refine ⟨968480654931249411025945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165230159633330192138373 968480654931249411025945)
                    ·
                      rfl

theorem cell22_2829164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_2829164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829164 prefixEnd_2829164 := by exact prefixLift 2829164
  have htrace : WordTrace (prefixWord ++ tailWord_2829164) baseStart_2829164 baseEnd_2829164 := by
    simpa [prefixWord, tailWord_2829164, baseEnd_2829164] using wordTrace_append hprefix tailTrace_2829164
  have hstable : (prefixWord ++ tailWord_2829164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829164).length < 2 ^ (prefixWord ++ tailWord_2829164).sum := by decide
  have hdescent : baseEnd_2829164 < baseStart_2829164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829179 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 4]
def baseStart_2829179 : Nat := 118140960795 + 2829179 * 2 ^ 59
def prefixEnd_2829179 : Nat := 4983230072969 + 3 ^ 40 * 2829179 * 2
def baseEnd_2829179 : Nat := 322828596579264790633633

theorem tailTrace_2829179 : CollatzResearch.WordTrace tailWord_2829179 prefixEnd_2829179 322828596579264790633633 := by
  unfold tailWord_2829179
  simp only [CollatzResearch.WordTrace]
  refine ⟨103188635417375143149962591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68792423611583428766641727 103188635417375143149962591)
  ·
    refine ⟨154782953126062714724943887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103188635417375143149962591 154782953126062714724943887)
    ·
      refine ⟨232174429689094072087415831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154782953126062714724943887 232174429689094072087415831)
      ·
        refine ⟨348261644533641108131123747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232174429689094072087415831 348261644533641108131123747)
        ·
          refine ⟨522392466800461662196685621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348261644533641108131123747 522392466800461662196685621)
          ·
            refine ⟨48974293762543280830939277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 522392466800461662196685621 48974293762543280830939277)
            ·
              refine ⟨18365360160953730311602229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48974293762543280830939277 18365360160953730311602229)
              ·
                refine ⟨1721752515089412216712709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18365360160953730311602229 1721752515089412216712709)
                ·
                  refine ⟨322828596579264790633633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721752515089412216712709 322828596579264790633633)
                  ·
                    rfl

theorem cell22_2829179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 4].length) (baseStart_2829179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829179 prefixEnd_2829179 := by exact prefixLift 2829179
  have htrace : WordTrace (prefixWord ++ tailWord_2829179) baseStart_2829179 baseEnd_2829179 := by
    simpa [prefixWord, tailWord_2829179, baseEnd_2829179] using wordTrace_append hprefix tailTrace_2829179
  have hstable : (prefixWord ++ tailWord_2829179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829179).length < 2 ^ (prefixWord ++ tailWord_2829179).sum := by decide
  have hdescent : baseEnd_2829179 < baseStart_2829179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829181 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_2829181 : Nat := 118140960795 + 2829181 * 2 ^ 59
def prefixEnd_2829181 : Nat := 4983230072969 + 3 ^ 40 * 2829181 * 2
def baseEnd_2829181 : Nat := 968486474378667033350893

theorem tailTrace_2829181 : CollatzResearch.WordTrace tailWord_2829181 prefixEnd_2829181 968486474378667033350893 := by
  unfold tailWord_2829181
  simp only [CollatzResearch.WordTrace]
  refine ⟨103188708363367897491535397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68792472242245264994356931 103188708363367897491535397)
  ·
    refine ⟨19347882818131480779662887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103188708363367897491535397 19347882818131480779662887)
    ·
      refine ⟨29021824227197221169494331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19347882818131480779662887 29021824227197221169494331)
      ·
        refine ⟨43532736340795831754241497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29021824227197221169494331 43532736340795831754241497)
        ·
          refine ⟨32649552255596873815681123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43532736340795831754241497 32649552255596873815681123)
          ·
            refine ⟨48974328383395310723521685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32649552255596873815681123 48974328383395310723521685)
            ·
              refine ⟨2295671642971655190165079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48974328383395310723521685 2295671642971655190165079)
              ·
                refine ⟨3443507464457482785247619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295671642971655190165079 3443507464457482785247619)
                ·
                  refine ⟨5165261196686224177871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443507464457482785247619 5165261196686224177871429)
                  ·
                    refine ⟨968486474378667033350893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165261196686224177871429 968486474378667033350893)
                    ·
                      rfl

theorem cell22_2829181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_2829181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829181 prefixEnd_2829181 := by exact prefixLift 2829181
  have htrace : WordTrace (prefixWord ++ tailWord_2829181) baseStart_2829181 baseEnd_2829181 := by
    simpa [prefixWord, tailWord_2829181, baseEnd_2829181] using wordTrace_append hprefix tailTrace_2829181
  have hstable : (prefixWord ++ tailWord_2829181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829181).length < 2 ^ (prefixWord ++ tailWord_2829181).sum := by decide
  have hdescent : baseEnd_2829181 < baseStart_2829181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829207 : List Nat := [1, 1, 3, 3, 1, 2, 2, 9]
def baseStart_2829207 : Nat := 118140960795 + 2829207 * 2 ^ 59
def prefixEnd_2829207 : Nat := 4983230072969 + 3 ^ 40 * 2829207 * 2
def baseEnd_2829207 : Nat := 107610597190001292466757

theorem tailTrace_2829207 : CollatzResearch.WordTrace tailWord_2829207 prefixEnd_2829207 107610597190001292466757 := by
  unfold tailWord_2829207
  simp only [CollatzResearch.WordTrace]
  refine ⟨103189656661273703931981875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68793104440849135954654583 103189656661273703931981875)
  ·
    refine ⟨154784484991910555897972813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103189656661273703931981875 154784484991910555897972813)
    ·
      refine ⟨58044181871966458461739805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154784484991910555897972813 58044181871966458461739805)
      ·
        refine ⟨21766568201987421923152427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58044181871966458461739805 21766568201987421923152427)
        ·
          refine ⟨32649852302981132884728641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21766568201987421923152427 32649852302981132884728641)
          ·
            refine ⟨24487389227235849663546481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32649852302981132884728641 24487389227235849663546481)
            ·
              refine ⟨18365541920426887247659861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24487389227235849663546481 18365541920426887247659861)
              ·
                refine ⟨107610597190001292466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18365541920426887247659861 107610597190001292466757)
                ·
                  rfl

theorem cell22_2829207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 9].length) (baseStart_2829207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829207 prefixEnd_2829207 := by exact prefixLift 2829207
  have htrace : WordTrace (prefixWord ++ tailWord_2829207) baseStart_2829207 baseEnd_2829207 := by
    simpa [prefixWord, tailWord_2829207, baseEnd_2829207] using wordTrace_append hprefix tailTrace_2829207
  have hstable : (prefixWord ++ tailWord_2829207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829207).length < 2 ^ (prefixWord ++ tailWord_2829207).sum := by decide
  have hdescent : baseEnd_2829207 < baseStart_2829207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829239 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 5, 3]
def baseStart_2829239 : Nat := 118140960795 + 2829239 * 2 ^ 59
def prefixEnd_2829239 : Nat := 4983230072969 + 3 ^ 40 * 2829239 * 2
def baseEnd_2829239 : Nat := 968506328963974215400715

theorem tailTrace_2829239 : CollatzResearch.WordTrace tailWord_2829239 prefixEnd_2829239 968506328963974215400715 := by
  unfold tailWord_2829239
  simp only [CollatzResearch.WordTrace]
  refine ⟨103190823797157773397146771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68793882531438515598097847 103190823797157773397146771)
  ·
    refine ⟨154786235695736660095720157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103190823797157773397146771 154786235695736660095720157)
    ·
      refine ⟨58044838385901247535895059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154786235695736660095720157 58044838385901247535895059)
      ·
        refine ⟨87067257578851871303842589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58044838385901247535895059 87067257578851871303842589)
        ·
          refine ⟨32650221592069451738940971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87067257578851871303842589 32650221592069451738940971)
          ·
            refine ⟨48975332388104177608411457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32650221592069451738940971 48975332388104177608411457)
            ·
              refine ⟨36731499291078133206308593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48975332388104177608411457 36731499291078133206308593)
              ·
                refine ⟨27548624468308599904731445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36731499291078133206308593 27548624468308599904731445)
                ·
                  refine ⟨2582683543903931241068573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27548624468308599904731445 2582683543903931241068573)
                  ·
                    refine ⟨968506328963974215400715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582683543903931241068573 968506328963974215400715)
                    ·
                      rfl

theorem cell22_2829239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_2829239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829239 prefixEnd_2829239 := by exact prefixLift 2829239
  have htrace : WordTrace (prefixWord ++ tailWord_2829239) baseStart_2829239 baseEnd_2829239 := by
    simpa [prefixWord, tailWord_2829239, baseEnd_2829239] using wordTrace_append hprefix tailTrace_2829239
  have hstable : (prefixWord ++ tailWord_2829239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829239).length < 2 ^ (prefixWord ++ tailWord_2829239).sum := by decide
  have hdescent : baseEnd_2829239 < baseStart_2829239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829346 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2829346 : Nat := 118140960795 + 2829346 * 2 ^ 59
def prefixEnd_2829346 : Nat := 4983230072969 + 3 ^ 40 * 2829346 * 2
def baseEnd_2829346 : Nat := 968542957250661602975387

theorem tailTrace_2829346 : CollatzResearch.WordTrace tailWord_2829346 prefixEnd_2829346 968542957250661602975387 := by
  unfold tailWord_2829346
  simp only [CollatzResearch.WordTrace]
  refine ⟨25798681601942532667822973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68796484271846753780861261 25798681601942532667822973)
  ·
    refine ⟨9674505600728449750433615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25798681601942532667822973 9674505600728449750433615)
    ·
      refine ⟨14511758401092674625650423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9674505600728449750433615 14511758401092674625650423)
      ·
        refine ⟨21767637601639011938475635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14511758401092674625650423 21767637601639011938475635)
        ·
          refine ⟨32651456402458517907713453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21767637601639011938475635 32651456402458517907713453)
          ·
            refine ⟨12244296150921944215392545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32651456402458517907713453 12244296150921944215392545)
            ·
              refine ⟨9183222113191458161544409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12244296150921944215392545 9183222113191458161544409)
              ·
                refine ⟨6887416584893593621158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9183222113191458161544409 6887416584893593621158307)
                ·
                  refine ⟨10331124877340390431737461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6887416584893593621158307 10331124877340390431737461)
                  ·
                    refine ⟨968542957250661602975387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10331124877340390431737461 968542957250661602975387)
                    ·
                      rfl

theorem cell22_2829346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2829346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829346 prefixEnd_2829346 := by exact prefixLift 2829346
  have htrace : WordTrace (prefixWord ++ tailWord_2829346) baseStart_2829346 baseEnd_2829346 := by
    simpa [prefixWord, tailWord_2829346, baseEnd_2829346] using wordTrace_append hprefix tailTrace_2829346
  have hstable : (prefixWord ++ tailWord_2829346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829346).length < 2 ^ (prefixWord ++ tailWord_2829346).sum := by decide
  have hdescent : baseEnd_2829346 < baseStart_2829346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829348 : List Nat := [2, 3, 1, 4, 1, 1, 1, 5, 4]
def baseStart_2829348 : Nat := 118140960795 + 2829348 * 2 ^ 59
def prefixEnd_2829348 : Nat := 4983230072969 + 3 ^ 40 * 2829348 * 2
def baseEnd_2829348 : Nat := 322847880630511421475127

theorem tailTrace_2829348 : CollatzResearch.WordTrace tailWord_2829348 prefixEnd_2829348 322847880630511421475127 := by
  unfold tailWord_2829348
  simp only [CollatzResearch.WordTrace]
  refine ⟨51597399676881442506432349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68796532902508590008576465 51597399676881442506432349)
  ·
    refine ⟨19349024878830540939912131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51597399676881442506432349 19349024878830540939912131)
    ·
      refine ⟨29023537318245811409868197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19349024878830540939912131 29023537318245811409868197)
      ·
        refine ⟨5441913247171089639350287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29023537318245811409868197 5441913247171089639350287)
        ·
          refine ⟨8162869870756634459025431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5441913247171089639350287 8162869870756634459025431)
          ·
            refine ⟨12244304806134951688538147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8162869870756634459025431 12244304806134951688538147)
            ·
              refine ⟨18366457209202427532807221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244304806134951688538147 18366457209202427532807221)
              ·
                refine ⟨1721855363362727581200677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18366457209202427532807221 1721855363362727581200677)
                ·
                  refine ⟨322847880630511421475127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721855363362727581200677 322847880630511421475127)
                  ·
                    rfl

theorem cell22_2829348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_2829348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829348 prefixEnd_2829348 := by exact prefixLift 2829348
  have htrace : WordTrace (prefixWord ++ tailWord_2829348) baseStart_2829348 baseEnd_2829348 := by
    simpa [prefixWord, tailWord_2829348, baseEnd_2829348] using wordTrace_append hprefix tailTrace_2829348
  have hstable : (prefixWord ++ tailWord_2829348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829348).length < 2 ^ (prefixWord ++ tailWord_2829348).sum := by decide
  have hdescent : baseEnd_2829348 < baseStart_2829348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829421 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2829421 : Nat := 118140960795 + 2829421 * 2 ^ 59
def prefixEnd_2829421 : Nat := 4983230072969 + 3 ^ 40 * 2829421 * 2
def baseEnd_2829421 : Nat := 322856210427795469116719

theorem tailTrace_2829421 : CollatzResearch.WordTrace tailWord_2829421 prefixEnd_2829421 322856210427795469116719 := by
  unfold tailWord_2829421
  simp only [CollatzResearch.WordTrace]
  refine ⟨103197461882498418480272117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68798307921665612320181411 103197461882498418480272117)
  ·
    refine ⟨9674762051484226732525511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103197461882498418480272117 9674762051484226732525511)
    ·
      refine ⟨14512143077226340098788267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9674762051484226732525511 14512143077226340098788267)
      ·
        refine ⟨21768214615839510148182401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14512143077226340098788267 21768214615839510148182401)
        ·
          refine ⟨16326160961879632611136801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21768214615839510148182401 16326160961879632611136801)
          ·
            refine ⟨12244620721409724458352601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16326160961879632611136801 12244620721409724458352601)
            ·
              refine ⟨9183465541057293343764451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12244620721409724458352601 9183465541057293343764451)
              ·
                refine ⟨13775198311585940015646677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9183465541057293343764451 13775198311585940015646677)
                ·
                  refine ⟨322856210427795469116719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13775198311585940015646677 322856210427795469116719)
                  ·
                    rfl

theorem cell22_2829421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2829421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829421 prefixEnd_2829421 := by exact prefixLift 2829421
  have htrace : WordTrace (prefixWord ++ tailWord_2829421) baseStart_2829421 baseEnd_2829421 := by
    simpa [prefixWord, tailWord_2829421, baseEnd_2829421] using wordTrace_append hprefix tailTrace_2829421
  have hstable : (prefixWord ++ tailWord_2829421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829421).length < 2 ^ (prefixWord ++ tailWord_2829421).sum := by decide
  have hdescent : baseEnd_2829421 < baseStart_2829421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829594 : List Nat := [3, 1, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_2829594 : Nat := 118140960795 + 2829594 * 2 ^ 59
def prefixEnd_2829594 : Nat := 4983230072969 + 3 ^ 40 * 2829594 * 2
def baseEnd_2829594 : Nat := 968627852718871622774627

theorem tailTrace_2829594 : CollatzResearch.WordTrace tailWord_2829594 prefixEnd_2829594 968627852718871622774627 := by
  unfold tailWord_2829594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25800942927717917256579959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68802514473914446017546557 25800942927717917256579959)
  ·
    refine ⟨38701414391576875884869939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25800942927717917256579959 38701414391576875884869939)
    ·
      refine ⟨58052121587365313827304909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38701414391576875884869939 58052121587365313827304909)
      ·
        refine ⟨21769545595261992685239341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58052121587365313827304909 21769545595261992685239341)
        ·
          refine ⟨8163579598223247256964753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21769545595261992685239341 8163579598223247256964753)
          ·
            refine ⟨6122684698667435442723565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8163579598223247256964753 6122684698667435442723565)
            ·
              refine ⟨2296006762000288291021337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6122684698667435442723565 2296006762000288291021337)
              ·
                refine ⟨1722005071500216218266003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296006762000288291021337 1722005071500216218266003)
                ·
                  refine ⟨2583007607250324327399005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722005071500216218266003 2583007607250324327399005)
                  ·
                    refine ⟨968627852718871622774627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2583007607250324327399005 968627852718871622774627)
                    ·
                      rfl

theorem cell22_2829594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_2829594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829594 prefixEnd_2829594 := by exact prefixLift 2829594
  have htrace : WordTrace (prefixWord ++ tailWord_2829594) baseStart_2829594 baseEnd_2829594 := by
    simpa [prefixWord, tailWord_2829594, baseEnd_2829594] using wordTrace_append hprefix tailTrace_2829594
  have hstable : (prefixWord ++ tailWord_2829594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829594).length < 2 ^ (prefixWord ++ tailWord_2829594).sum := by decide
  have hdescent : baseEnd_2829594 < baseStart_2829594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829620 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2829620 : Nat := 118140960795 + 2829620 * 2 ^ 59
def prefixEnd_2829620 : Nat := 4983230072969 + 3 ^ 40 * 2829620 * 2
def baseEnd_2829620 : Nat := 968636753050216221624547

theorem tailTrace_2829620 : CollatzResearch.WordTrace tailWord_2829620 prefixEnd_2829620 968636753050216221624547 := by
  unfold tailWord_2829620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51602360004388737733383157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68803146672518316977844209 51602360004388737733383157)
  ·
    refine ⟨4837721250411444162504671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51602360004388737733383157 4837721250411444162504671)
    ·
      refine ⟨7256581875617166243757007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837721250411444162504671 7256581875617166243757007)
      ·
        refine ⟨10884872813425749365635511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7256581875617166243757007 10884872813425749365635511)
        ·
          refine ⟨16327309220138624048453267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10884872813425749365635511 16327309220138624048453267)
          ·
            refine ⟨24490963830207936072679901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16327309220138624048453267 24490963830207936072679901)
            ·
              refine ⟨9184111436327976027254963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24490963830207936072679901 9184111436327976027254963)
              ·
                refine ⟨13776167154491964040882445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9184111436327976027254963 13776167154491964040882445)
                ·
                  refine ⟨5166062682934486515330917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13776167154491964040882445 5166062682934486515330917)
                  ·
                    refine ⟨968636753050216221624547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166062682934486515330917 968636753050216221624547)
                    ·
                      rfl

theorem cell22_2829620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2829620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829620 prefixEnd_2829620 := by exact prefixLift 2829620
  have htrace : WordTrace (prefixWord ++ tailWord_2829620) baseStart_2829620 baseEnd_2829620 := by
    simpa [prefixWord, tailWord_2829620, baseEnd_2829620] using wordTrace_append hprefix tailTrace_2829620
  have hstable : (prefixWord ++ tailWord_2829620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829620).length < 2 ^ (prefixWord ++ tailWord_2829620).sum := by decide
  have hdescent : baseEnd_2829620 < baseStart_2829620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829645 : List Nat := [1, 6, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2829645 : Nat := 118140960795 + 2829645 * 2 ^ 59
def prefixEnd_2829645 : Nat := 4983230072969 + 3 ^ 40 * 2829645 * 2
def baseEnd_2829645 : Nat := 968645311061124489749471

theorem tailTrace_2829645 : CollatzResearch.WordTrace tailWord_2829645 prefixEnd_2829645 968645311061124489749471 := by
  unfold tailWord_2829645
  simp only [CollatzResearch.WordTrace]
  refine ⟨103205631833686904736426389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68803754555791269824284259 103205631833686904736426389)
  ·
    refine ⟨4837763992204073659519987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103205631833686904736426389 4837763992204073659519987)
    ·
      refine ⟨7256645988306110489279981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837763992204073659519987 7256645988306110489279981)
      ·
        refine ⟨2721242245614791433479993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7256645988306110489279981 2721242245614791433479993)
        ·
          refine ⟨2040931684211093575109995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2721242245614791433479993 2040931684211093575109995)
          ·
            refine ⟨3061397526316640362664993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040931684211093575109995 3061397526316640362664993)
            ·
              refine ⟨2296048144737480271998745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061397526316640362664993 2296048144737480271998745)
              ·
                refine ⟨1722036108553110203999059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296048144737480271998745 1722036108553110203999059)
                ·
                  refine ⟨2583054162829665305998589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722036108553110203999059 2583054162829665305998589)
                  ·
                    refine ⟨968645311061124489749471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2583054162829665305998589 968645311061124489749471)
                    ·
                      rfl

theorem cell22_2829645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2829645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829645 prefixEnd_2829645 := by exact prefixLift 2829645
  have htrace : WordTrace (prefixWord ++ tailWord_2829645) baseStart_2829645 baseEnd_2829645 := by
    simpa [prefixWord, tailWord_2829645, baseEnd_2829645] using wordTrace_append hprefix tailTrace_2829645
  have hstable : (prefixWord ++ tailWord_2829645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829645).length < 2 ^ (prefixWord ++ tailWord_2829645).sum := by decide
  have hdescent : baseEnd_2829645 < baseStart_2829645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829648 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_2829648 : Nat := 118140960795 + 2829648 * 2 ^ 59
def prefixEnd_2829648 : Nat := 4983230072969 + 3 ^ 40 * 2829648 * 2
def baseEnd_2829648 : Nat := 968646338022433481924461

theorem tailTrace_2829648 : CollatzResearch.WordTrace tailWord_2829648 prefixEnd_2829648 968646338022433481924461 := by
  unfold tailWord_2829648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51602870626338018124392799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68803827501784024165857065 51602870626338018124392799)
  ·
    refine ⟨77404305939507027186589199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51602870626338018124392799 77404305939507027186589199)
    ·
      refine ⟨116106458909260540779883799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77404305939507027186589199 116106458909260540779883799)
      ·
        refine ⟨174159688363890811169825699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116106458909260540779883799 174159688363890811169825699)
        ·
          refine ⟨261239532545836216754738549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174159688363890811169825699 261239532545836216754738549)
          ·
            refine ⟨24491206176172145320756739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261239532545836216754738549 24491206176172145320756739)
            ·
              refine ⟨36736809264258217981135109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24491206176172145320756739 36736809264258217981135109)
              ·
                refine ⟨6888151737048415871462833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36736809264258217981135109 6888151737048415871462833)
                ·
                  refine ⟨5166113802786311903597125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6888151737048415871462833 5166113802786311903597125)
                  ·
                    refine ⟨968646338022433481924461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166113802786311903597125 968646338022433481924461)
                    ·
                      rfl

theorem cell22_2829648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_2829648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829648 prefixEnd_2829648 := by exact prefixLift 2829648
  have htrace : WordTrace (prefixWord ++ tailWord_2829648) baseStart_2829648 baseEnd_2829648 := by
    simpa [prefixWord, tailWord_2829648, baseEnd_2829648] using wordTrace_append hprefix tailTrace_2829648
  have hstable : (prefixWord ++ tailWord_2829648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829648).length < 2 ^ (prefixWord ++ tailWord_2829648).sum := by decide
  have hdescent : baseEnd_2829648 < baseStart_2829648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829708 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_2829708 : Nat := 118140960795 + 2829708 * 2 ^ 59
def prefixEnd_2829708 : Nat := 4983230072969 + 3 ^ 40 * 2829708 * 2
def baseEnd_2829708 : Nat := 322888959082871108474759

theorem tailTrace_2829708 : CollatzResearch.WordTrace tailWord_2829708 prefixEnd_2829708 322888959082871108474759 := by
  unfold tailWord_2829708
  simp only [CollatzResearch.WordTrace]
  refine ⟨51603964816229333247984889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68805286421639110997313185 51603964816229333247984889)
  ·
    refine ⟨38702973612171999935988667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51603964816229333247984889 38702973612171999935988667)
    ·
      refine ⟨58054460418257999903983001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38702973612171999935988667 58054460418257999903983001)
      ·
        refine ⟨43540845313693499927987251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58054460418257999903983001 43540845313693499927987251)
        ·
          refine ⟨65311267970540249891980877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43540845313693499927987251 65311267970540249891980877)
          ·
            refine ⟨24491725488952593709492829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65311267970540249891980877 24491725488952593709492829)
            ·
              refine ⟨9184397058357222641059811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24491725488952593709492829 9184397058357222641059811)
              ·
                refine ⟨13776595587535833961589717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9184397058357222641059811 13776595587535833961589717)
                ·
                  refine ⟨322888959082871108474759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13776595587535833961589717 322888959082871108474759)
                  ·
                    rfl

theorem cell22_2829708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_2829708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829708 prefixEnd_2829708 := by exact prefixLift 2829708
  have htrace : WordTrace (prefixWord ++ tailWord_2829708) baseStart_2829708 baseEnd_2829708 := by
    simpa [prefixWord, tailWord_2829708, baseEnd_2829708] using wordTrace_append hprefix tailTrace_2829708
  have hstable : (prefixWord ++ tailWord_2829708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829708).length < 2 ^ (prefixWord ++ tailWord_2829708).sum := by decide
  have hdescent : baseEnd_2829708 < baseStart_2829708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829770 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_2829770 : Nat := 118140960795 + 2829770 * 2 ^ 59
def prefixEnd_2829770 : Nat := 4983230072969 + 3 ^ 40 * 2829770 * 2
def baseEnd_2829770 : Nat := 322896033705221943458029

theorem tailTrace_2829770 : CollatzResearch.WordTrace tailWord_2829770 prefixEnd_2829770 322896033705221943458029 := by
  unfold tailWord_2829770
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802547739558512771181691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68806793972156034056484509 25802547739558512771181691)
  ·
    refine ⟨38703821609337769156772537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25802547739558512771181691 38703821609337769156772537)
    ·
      refine ⟨29027866207003326867579403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38703821609337769156772537 29027866207003326867579403)
      ·
        refine ⟨43541799310504990301369105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29027866207003326867579403 43541799310504990301369105)
        ·
          refine ⟨32656349482878742726026829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43541799310504990301369105 32656349482878742726026829)
          ·
            refine ⟨12246131056079528522260061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32656349482878742726026829 12246131056079528522260061)
            ·
              refine ⟨4592299146029823195847523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12246131056079528522260061 4592299146029823195847523)
              ·
                refine ⟨6888448719044734793771285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592299146029823195847523 6888448719044734793771285)
                ·
                  refine ⟨322896033705221943458029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6888448719044734793771285 322896033705221943458029)
                  ·
                    rfl

theorem cell22_2829770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_2829770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829770 prefixEnd_2829770 := by exact prefixLift 2829770
  have htrace : WordTrace (prefixWord ++ tailWord_2829770) baseStart_2829770 baseEnd_2829770 := by
    simpa [prefixWord, tailWord_2829770, baseEnd_2829770] using wordTrace_append hprefix tailTrace_2829770
  have hstable : (prefixWord ++ tailWord_2829770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829770).length < 2 ^ (prefixWord ++ tailWord_2829770).sum := by decide
  have hdescent : baseEnd_2829770 < baseStart_2829770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829783 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_2829783 : Nat := 118140960795 + 2829783 * 2 ^ 59
def prefixEnd_2829783 : Nat := 4983230072969 + 3 ^ 40 * 2829783 * 2
def baseEnd_2829783 : Nat := 968692551281338129799047

theorem tailTrace_2829783 : CollatzResearch.WordTrace tailWord_2829783 prefixEnd_2829783 968692551281338129799047 := by
  unfold tailWord_2829783
  simp only [CollatzResearch.WordTrace]
  refine ⟨103210665107186954304950003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68807110071457969536633335 103210665107186954304950003)
  ·
    refine ⟨154815997660780431457425005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103210665107186954304950003 154815997660780431457425005)
    ·
      refine ⟨58055999122792661796534377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154815997660780431457425005 58055999122792661796534377)
      ·
        refine ⟨43541999342094496347400783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58055999122792661796534377 43541999342094496347400783)
        ·
          refine ⟨65312999013141744521101175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43541999342094496347400783 65312999013141744521101175)
          ·
            refine ⟨97969498519712616781651763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65312999013141744521101175 97969498519712616781651763)
            ·
              refine ⟨146954247779568925172477645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97969498519712616781651763 146954247779568925172477645)
              ·
                refine ⟨55107842917338346939679117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146954247779568925172477645 55107842917338346939679117)
                ·
                  refine ⟨20665441094001880102379669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55107842917338346939679117 20665441094001880102379669)
                  ·
                    refine ⟨968692551281338129799047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20665441094001880102379669 968692551281338129799047)
                    ·
                      rfl

theorem cell22_2829783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_2829783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829783 prefixEnd_2829783 := by exact prefixLift 2829783
  have htrace : WordTrace (prefixWord ++ tailWord_2829783) baseStart_2829783 baseEnd_2829783 := by
    simpa [prefixWord, tailWord_2829783, baseEnd_2829783] using wordTrace_append hprefix tailTrace_2829783
  have hstable : (prefixWord ++ tailWord_2829783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829783).length < 2 ^ (prefixWord ++ tailWord_2829783).sum := by decide
  have hdescent : baseEnd_2829783 < baseStart_2829783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829789 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2829789 : Nat := 118140960795 + 2829789 * 2 ^ 59
def prefixEnd_2829789 : Nat := 4983230072969 + 3 ^ 40 * 2829789 * 2
def baseEnd_2829789 : Nat := 968694605203956114149029

theorem tailTrace_2829789 : CollatzResearch.WordTrace tailWord_2829789 prefixEnd_2829789 968694605203956114149029 := by
  unfold tailWord_2829789
  simp only [CollatzResearch.WordTrace]
  refine ⟨103210883945165217329668421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68807255963443478219778947 103210883945165217329668421)
  ·
    refine ⟨19352040739718478249312829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103210883945165217329668421 19352040739718478249312829)
    ·
      refine ⟨7257015277394429343492311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19352040739718478249312829 7257015277394429343492311)
      ·
        refine ⟨10885522916091644015238467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257015277394429343492311 10885522916091644015238467)
        ·
          refine ⟨16328284374137466022857701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10885522916091644015238467 16328284374137466022857701)
          ·
            refine ⟨3061553320150774879285819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16328284374137466022857701 3061553320150774879285819)
            ·
              refine ⟨4592329980226162318928729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061553320150774879285819 4592329980226162318928729)
              ·
                refine ⟨3444247485169621739196547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592329980226162318928729 3444247485169621739196547)
                ·
                  refine ⟨5166371227754432608794821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444247485169621739196547 5166371227754432608794821)
                  ·
                    refine ⟨968694605203956114149029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5166371227754432608794821 968694605203956114149029)
                    ·
                      rfl

theorem cell22_2829789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2829789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829789 prefixEnd_2829789 := by exact prefixLift 2829789
  have htrace : WordTrace (prefixWord ++ tailWord_2829789) baseStart_2829789 baseEnd_2829789 := by
    simpa [prefixWord, tailWord_2829789, baseEnd_2829789] using wordTrace_append hprefix tailTrace_2829789
  have hstable : (prefixWord ++ tailWord_2829789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829789).length < 2 ^ (prefixWord ++ tailWord_2829789).sum := by decide
  have hdescent : baseEnd_2829789 < baseStart_2829789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829802 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2829802 : Nat := 118140960795 + 2829802 * 2 ^ 59
def prefixEnd_2829802 : Nat := 4983230072969 + 3 ^ 40 * 2829802 * 2
def baseEnd_2829802 : Nat := 968699055369628413573989

theorem tailTrace_2829802 : CollatzResearch.WordTrace tailWord_2829802 prefixEnd_2829802 968699055369628413573989 := by
  unfold tailWord_2829802
  simp only [CollatzResearch.WordTrace]
  refine ⟨25802839523529530137472915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68807572062745413699927773 25802839523529530137472915)
  ·
    refine ⟨38704259285294295206209373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25802839523529530137472915 38704259285294295206209373)
    ·
      refine ⟨14514097231985360702328515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38704259285294295206209373 14514097231985360702328515)
      ·
        refine ⟨21771145847978041053492773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14514097231985360702328515 21771145847978041053492773)
        ·
          refine ⟨4082089846495882697529895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21771145847978041053492773 4082089846495882697529895)
          ·
            refine ⟨6123134769743824046294843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4082089846495882697529895 6123134769743824046294843)
            ·
              refine ⟨9184702154615736069442265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6123134769743824046294843 9184702154615736069442265)
              ·
                refine ⟨6888526615961802052081699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9184702154615736069442265 6888526615961802052081699)
                ·
                  refine ⟨10332789923942703078122549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6888526615961802052081699 10332789923942703078122549)
                  ·
                    refine ⟨968699055369628413573989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10332789923942703078122549 968699055369628413573989)
                    ·
                      rfl

theorem cell22_2829802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2829802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829802 prefixEnd_2829802 := by exact prefixLift 2829802
  have htrace : WordTrace (prefixWord ++ tailWord_2829802) baseStart_2829802 baseEnd_2829802 := by
    simpa [prefixWord, tailWord_2829802, baseEnd_2829802] using wordTrace_append hprefix tailTrace_2829802
  have hstable : (prefixWord ++ tailWord_2829802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829802).length < 2 ^ (prefixWord ++ tailWord_2829802).sum := by decide
  have hdescent : baseEnd_2829802 < baseStart_2829802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829875 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_2829875 : Nat := 118140960795 + 2829875 * 2 ^ 59
def prefixEnd_2829875 : Nat := 4983230072969 + 3 ^ 40 * 2829875 * 2
def baseEnd_2829875 : Nat := 968724044761480556498765

theorem tailTrace_2829875 : CollatzResearch.WordTrace tailWord_2829875 prefixEnd_2829875 968724044761480556498765 := by
  unfold tailWord_2829875
  simp only [CollatzResearch.WordTrace]
  refine ⟨103214020622853654017299079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68809347081902436011532719 103214020622853654017299079)
  ·
    refine ⟨154821030934280481025948619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103214020622853654017299079 154821030934280481025948619)
    ·
      refine ⟨232231546401420721538922929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154821030934280481025948619 232231546401420721538922929)
      ·
        refine ⟨174173659801065541154192197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232231546401420721538922929 174173659801065541154192197)
        ·
          refine ⟨32657561212699788966411037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174173659801065541154192197 32657561212699788966411037)
          ·
            refine ⟨12246585454762420862404139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32657561212699788966411037 12246585454762420862404139)
            ·
              refine ⟨18369878182143631293606209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12246585454762420862404139 18369878182143631293606209)
              ·
                refine ⟨13777408636607723470204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18369878182143631293606209 13777408636607723470204657)
                ·
                  refine ⟨10333056477455792602653493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13777408636607723470204657 10333056477455792602653493)
                  ·
                    refine ⟨968724044761480556498765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10333056477455792602653493 968724044761480556498765)
                    ·
                      rfl

theorem cell22_2829875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_2829875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829875 prefixEnd_2829875 := by exact prefixLift 2829875
  have htrace : WordTrace (prefixWord ++ tailWord_2829875) baseStart_2829875 baseEnd_2829875 := by
    simpa [prefixWord, tailWord_2829875, baseEnd_2829875] using wordTrace_append hprefix tailTrace_2829875
  have hstable : (prefixWord ++ tailWord_2829875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829875).length < 2 ^ (prefixWord ++ tailWord_2829875).sum := by decide
  have hdescent : baseEnd_2829875 < baseStart_2829875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829877 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 5]
def baseStart_2829877 : Nat := 118140960795 + 2829877 * 2 ^ 59
def prefixEnd_2829877 : Nat := 4983230072969 + 3 ^ 40 * 2829877 * 2
def baseEnd_2829877 : Nat := 322908243134117739316253

theorem tailTrace_2829877 : CollatzResearch.WordTrace tailWord_2829877 prefixEnd_2829877 322908243134117739316253 := by
  unfold tailWord_2829877
  simp only [CollatzResearch.WordTrace]
  refine ⟨103214093568846408358871885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68809395712564272239247923 103214093568846408358871885)
  ·
    refine ⟨38705285088317403134576957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103214093568846408358871885 38705285088317403134576957)
    ·
      refine ⟨14514481908119026175466359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38705285088317403134576957 14514481908119026175466359)
      ·
        refine ⟨21771722862178539263199539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14514481908119026175466359 21771722862178539263199539)
        ·
          refine ⟨32657584293267808894799309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21771722862178539263199539 32657584293267808894799309)
          ·
            refine ⟨12246594109975428335549741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32657584293267808894799309 12246594109975428335549741)
            ·
              refine ⟨4592472791240785625831153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12246594109975428335549741 4592472791240785625831153)
              ·
                refine ⟨3444354593430589219373365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4592472791240785625831153 3444354593430589219373365)
                ·
                  refine ⟨322908243134117739316253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444354593430589219373365 322908243134117739316253)
                  ·
                    rfl

theorem cell22_2829877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_2829877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829877 prefixEnd_2829877 := by exact prefixLift 2829877
  have htrace : WordTrace (prefixWord ++ tailWord_2829877) baseStart_2829877 baseEnd_2829877 := by
    simpa [prefixWord, tailWord_2829877, baseEnd_2829877] using wordTrace_append hprefix tailTrace_2829877
  have hstable : (prefixWord ++ tailWord_2829877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829877).length < 2 ^ (prefixWord ++ tailWord_2829877).sum := by decide
  have hdescent : baseEnd_2829877 < baseStart_2829877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829905 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 6]
def baseStart_2829905 : Nat := 118140960795 + 2829905 * 2 ^ 59
def prefixEnd_2829905 : Nat := 4983230072969 + 3 ^ 40 * 2829905 * 2
def baseEnd_2829905 : Nat := 322911438124856826082891

theorem tailTrace_2829905 : CollatzResearch.WordTrace tailWord_2829905 prefixEnd_2829905 322911438124856826082891 := by
  unfold tailWord_2829905
  simp only [CollatzResearch.WordTrace]
  refine ⟨103215114812744969140891169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68810076541829979427260779 103215114812744969140891169)
  ·
    refine ⟨77411336109558726855668377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103215114812744969140891169 77411336109558726855668377)
    ·
      refine ⟨58058502082169045141751283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77411336109558726855668377 58058502082169045141751283)
      ·
        refine ⟨87087753123253567712626925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58058502082169045141751283 87087753123253567712626925)
        ·
          refine ⟨32657907421220087892235097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87087753123253567712626925 32657907421220087892235097)
          ·
            refine ⟨24493430565915065919176323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32657907421220087892235097 24493430565915065919176323)
            ·
              refine ⟨36740145848872598878764485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24493430565915065919176323 36740145848872598878764485)
              ·
                refine ⟨6888777346663612289768341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36740145848872598878764485 6888777346663612289768341)
                ·
                  refine ⟨322911438124856826082891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6888777346663612289768341 322911438124856826082891)
                  ·
                    rfl

theorem cell22_2829905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_2829905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829905 prefixEnd_2829905 := by exact prefixLift 2829905
  have htrace : WordTrace (prefixWord ++ tailWord_2829905) baseStart_2829905 baseEnd_2829905 := by
    simpa [prefixWord, tailWord_2829905, baseEnd_2829905] using wordTrace_append hprefix tailTrace_2829905
  have hstable : (prefixWord ++ tailWord_2829905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829905).length < 2 ^ (prefixWord ++ tailWord_2829905).sum := by decide
  have hdescent : baseEnd_2829905 < baseStart_2829905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829920 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_2829920 : Nat := 118140960795 + 2829920 * 2 ^ 59
def prefixEnd_2829920 : Nat := 4983230072969 + 3 ^ 40 * 2829920 * 2
def baseEnd_2829920 : Nat := 968739449181115439123627

theorem tailTrace_2829920 : CollatzResearch.WordTrace tailWord_2829920 prefixEnd_2829920 968739449181115439123627 := by
  unfold tailWord_2829920
  simp only [CollatzResearch.WordTrace]
  refine ⟨51607830953845313351343607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68810441271793751135124809 51607830953845313351343607)
  ·
    refine ⟨77411746430767970027015411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51607830953845313351343607 77411746430767970027015411)
    ·
      refine ⟨116117619646151955040523117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77411746430767970027015411 116117619646151955040523117)
      ·
        refine ⟨43544107367306983140196169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116117619646151955040523117 43544107367306983140196169)
        ·
          refine ⟨32658080525480237355147127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43544107367306983140196169 32658080525480237355147127)
          ·
            refine ⟨48987120788220356032720691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32658080525480237355147127 48987120788220356032720691)
            ·
              refine ⟨73480681182330534049081037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48987120788220356032720691 73480681182330534049081037)
              ·
                refine ⟨27555255443373950268405389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73480681182330534049081037 27555255443373950268405389)
                ·
                  refine ⟨10333220791265231350652021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27555255443373950268405389 10333220791265231350652021)
                  ·
                    refine ⟨968739449181115439123627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10333220791265231350652021 968739449181115439123627)
                    ·
                      rfl

theorem cell22_2829920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_2829920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829920 prefixEnd_2829920 := by exact prefixLift 2829920
  have htrace : WordTrace (prefixWord ++ tailWord_2829920) baseStart_2829920 baseEnd_2829920 := by
    simpa [prefixWord, tailWord_2829920, baseEnd_2829920] using wordTrace_append hprefix tailTrace_2829920
  have hstable : (prefixWord ++ tailWord_2829920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829920).length < 2 ^ (prefixWord ++ tailWord_2829920).sum := by decide
  have hdescent : baseEnd_2829920 < baseStart_2829920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2829997 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2829997 : Nat := 118140960795 + 2829997 * 2 ^ 59
def prefixEnd_2829997 : Nat := 4983230072969 + 3 ^ 40 * 2829997 * 2
def baseEnd_2829997 : Nat := 968765807854712904948391

theorem tailTrace_2829997 : CollatzResearch.WordTrace tailWord_2829997 prefixEnd_2829997 968765807854712904948391 := by
  unfold tailWord_2829997
  simp only [CollatzResearch.WordTrace]
  refine ⟨103218470328411668853240245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68812313552274445902160163 103218470328411668853240245)
  ·
    refine ⟨9676731593288593954991273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103218470328411668853240245 9676731593288593954991273)
    ·
      refine ⟨7257548694966445466243455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9676731593288593954991273 7257548694966445466243455)
      ·
        refine ⟨10886323042449668199365183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7257548694966445466243455 10886323042449668199365183)
        ·
          refine ⟨16329484563674502299047775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10886323042449668199365183 16329484563674502299047775)
          ·
            refine ⟨24494226845511753448571663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16329484563674502299047775 24494226845511753448571663)
            ·
              refine ⟨36741340268267630172857495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24494226845511753448571663 36741340268267630172857495)
              ·
                refine ⟨55112010402401445259286243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36741340268267630172857495 55112010402401445259286243)
                ·
                  refine ⟨82668015603602167888929365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55112010402401445259286243 82668015603602167888929365)
                  ·
                    refine ⟨968765807854712904948391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82668015603602167888929365 968765807854712904948391)
                    ·
                      rfl

theorem cell22_2829997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2829997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2829997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2829997 prefixEnd_2829997 := by exact prefixLift 2829997
  have htrace : WordTrace (prefixWord ++ tailWord_2829997) baseStart_2829997 baseEnd_2829997 := by
    simpa [prefixWord, tailWord_2829997, baseEnd_2829997] using wordTrace_append hprefix tailTrace_2829997
  have hstable : (prefixWord ++ tailWord_2829997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2829997).length < 2 ^ (prefixWord ++ tailWord_2829997).sum := by decide
  have hdescent : baseEnd_2829997 < baseStart_2829997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2829997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830072 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_2830072 : Nat := 118140960795 + 2830072 * 2 ^ 59
def prefixEnd_2830072 : Nat := 4983230072969 + 3 ^ 40 * 2830072 * 2
def baseEnd_2830072 : Nat := 968791481887437709323161

theorem tailTrace_2830072 : CollatzResearch.WordTrace tailWord_2830072 prefixEnd_2830072 968791481887437709323161 := by
  unfold tailWord_2830072
  simp only [CollatzResearch.WordTrace]
  refine ⟨51610602901569978331110235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68814137202093304441480313 51610602901569978331110235)
  ·
    refine ⟨77415904352354967496665353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51610602901569978331110235 77415904352354967496665353)
    ·
      refine ⟨58061928264266225622499015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77415904352354967496665353 58061928264266225622499015)
      ·
        refine ⟨87092892396399338433748523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58061928264266225622499015 87092892396399338433748523)
        ·
          refine ⟨130639338594599007650622785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87092892396399338433748523 130639338594599007650622785)
          ·
            refine ⟨97979503945949255737967089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130639338594599007650622785 97979503945949255737967089)
            ·
              refine ⟨73484627959461941803475317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97979503945949255737967089 73484627959461941803475317)
              ·
                refine ⟨6889183871199557044075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73484627959461941803475317 6889183871199557044075811)
                ·
                  refine ⟨10333775806799335566113717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6889183871199557044075811 10333775806799335566113717)
                  ·
                    refine ⟨968791481887437709323161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10333775806799335566113717 968791481887437709323161)
                    ·
                      rfl

theorem cell22_2830072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_2830072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830072 prefixEnd_2830072 := by exact prefixLift 2830072
  have htrace : WordTrace (prefixWord ++ tailWord_2830072) baseStart_2830072 baseEnd_2830072 := by
    simpa [prefixWord, tailWord_2830072, baseEnd_2830072] using wordTrace_append hprefix tailTrace_2830072
  have hstable : (prefixWord ++ tailWord_2830072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830072).length < 2 ^ (prefixWord ++ tailWord_2830072).sum := by decide
  have hdescent : baseEnd_2830072 < baseStart_2830072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830211 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 1, 4]
def baseStart_2830211 : Nat := 118140960795 + 2830211 * 2 ^ 59
def prefixEnd_2830211 : Nat := 4983230072969 + 3 ^ 40 * 2830211 * 2
def baseEnd_2830211 : Nat := 968839064428087680097735

theorem tailTrace_2830211 : CollatzResearch.WordTrace tailWord_2830211 prefixEnd_2830211 968839064428087680097735 := by
  unfold tailWord_2830211
  simp only [CollatzResearch.WordTrace]
  refine ⟨103226275549636383401530487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68817517033090922267686991 103226275549636383401530487)
  ·
    refine ⟨154839413324454575102295731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103226275549636383401530487 154839413324454575102295731)
    ·
      refine ⟨232259119986681862653443597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154839413324454575102295731 232259119986681862653443597)
      ·
        refine ⟨87097169995005698495041349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232259119986681862653443597 87097169995005698495041349)
        ·
          refine ⟨16330719374063568467820253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87097169995005698495041349 16330719374063568467820253)
          ·
            refine ⟨6124019765273838175432595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16330719374063568467820253 6124019765273838175432595)
            ·
              refine ⟨9186029647910757263148893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6124019765273838175432595 9186029647910757263148893)
              ·
                refine ⟨3444761117966533973680835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9186029647910757263148893 3444761117966533973680835)
                ·
                  refine ⟨5167141676949800960521253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3444761117966533973680835 5167141676949800960521253)
                  ·
                    refine ⟨968839064428087680097735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167141676949800960521253 968839064428087680097735)
                    ·
                      rfl

theorem cell22_2830211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 4].length) (baseStart_2830211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830211 prefixEnd_2830211 := by exact prefixLift 2830211
  have htrace : WordTrace (prefixWord ++ tailWord_2830211) baseStart_2830211 baseEnd_2830211 := by
    simpa [prefixWord, tailWord_2830211, baseEnd_2830211] using wordTrace_append hprefix tailTrace_2830211
  have hstable : (prefixWord ++ tailWord_2830211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830211).length < 2 ^ (prefixWord ++ tailWord_2830211).sum := by decide
  have hdescent : baseEnd_2830211 < baseStart_2830211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830226 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_2830226 : Nat := 118140960795 + 2830226 * 2 ^ 59
def prefixEnd_2830226 : Nat := 4983230072969 + 3 ^ 40 * 2830226 * 2
def baseEnd_2830226 : Nat := 322948066411544213657563

theorem tailTrace_2830226 : CollatzResearch.WordTrace tailWord_2830226 prefixEnd_2830226 322948066411544213657563 := by
  unfold tailWord_2830226
  simp only [CollatzResearch.WordTrace]
  refine ⟨25806705661145510240831633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68817881763054693975551021 25806705661145510240831633)
  ·
    refine ⟨19355029245859132680623725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25806705661145510240831633 19355029245859132680623725)
    ·
      refine ⟨7258135967197174755233897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19355029245859132680623725 7258135967197174755233897)
      ·
        refine ⟨5443601975397881066425423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7258135967197174755233897 5443601975397881066425423)
        ·
          refine ⟨8165402963096821599638135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5443601975397881066425423 8165402963096821599638135)
          ·
            refine ⟨12248104444645232399457203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8165402963096821599638135 12248104444645232399457203)
            ·
              refine ⟨18372156666967848599185805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12248104444645232399457203 18372156666967848599185805)
              ·
                refine ⟨6889558750112943224694677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18372156666967848599185805 6889558750112943224694677)
                ·
                  refine ⟨322948066411544213657563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6889558750112943224694677 322948066411544213657563)
                  ·
                    rfl

theorem cell22_2830226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_2830226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830226 prefixEnd_2830226 := by exact prefixLift 2830226
  have htrace : WordTrace (prefixWord ++ tailWord_2830226) baseStart_2830226 baseEnd_2830226 := by
    simpa [prefixWord, tailWord_2830226, baseEnd_2830226] using wordTrace_append hprefix tailTrace_2830226
  have hstable : (prefixWord ++ tailWord_2830226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830226).length < 2 ^ (prefixWord ++ tailWord_2830226).sum := by decide
  have hdescent : baseEnd_2830226 < baseStart_2830226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830391 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 2, 4]
def baseStart_2830391 : Nat := 118140960795 + 2830391 * 2 ^ 59
def prefixEnd_2830391 : Nat := 4983230072969 + 3 ^ 40 * 2830391 * 2
def baseEnd_2830391 : Nat := 968900682106627210597183

theorem tailTrace_2830391 : CollatzResearch.WordTrace tailWord_2830391 prefixEnd_2830391 968900682106627210597183 := by
  unfold tailWord_2830391
  simp only [CollatzResearch.WordTrace]
  refine ⟨103232840688984274143083027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68821893792656182762055351 103232840688984274143083027)
  ·
    refine ⟨154849261033476411214624541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103232840688984274143083027 154849261033476411214624541)
    ·
      refine ⟨58068472887553654205484203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154849261033476411214624541 58068472887553654205484203)
      ·
        refine ⟨87102709331330481308226305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58068472887553654205484203 87102709331330481308226305)
        ·
          refine ⟨65327031998497860981169729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87102709331330481308226305 65327031998497860981169729)
          ·
            refine ⟨48995273998873395735877297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65327031998497860981169729 48995273998873395735877297)
            ·
              refine ⟨36746455499155046801907973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48995273998873395735877297 36746455499155046801907973)
              ·
                refine ⟨6889960406091571275357745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36746455499155046801907973 6889960406091571275357745)
                ·
                  refine ⟨5167470304568678456518309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6889960406091571275357745 5167470304568678456518309)
                  ·
                    refine ⟨968900682106627210597183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167470304568678456518309 968900682106627210597183)
                    ·
                      rfl

theorem cell22_2830391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_2830391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830391 prefixEnd_2830391 := by exact prefixLift 2830391
  have htrace : WordTrace (prefixWord ++ tailWord_2830391) baseStart_2830391 baseEnd_2830391 := by
    simpa [prefixWord, tailWord_2830391, baseEnd_2830391] using wordTrace_append hprefix tailTrace_2830391
  have hstable : (prefixWord ++ tailWord_2830391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830391).length < 2 ^ (prefixWord ++ tailWord_2830391).sum := by decide
  have hdescent : baseEnd_2830391 < baseStart_2830391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830455 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 3, 3]
def baseStart_2830455 : Nat := 118140960795 + 2830455 * 2 ^ 59
def prefixEnd_2830455 : Nat := 4983230072969 + 3 ^ 40 * 2830455 * 2
def baseEnd_2830455 : Nat := 968922590614552376996987

theorem tailTrace_2830455 : CollatzResearch.WordTrace tailWord_2830455 prefixEnd_2830455 968922590614552376996987 := by
  unfold tailWord_2830455
  simp only [CollatzResearch.WordTrace]
  refine ⟨103235174960752413073412819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68823449973834942048941879 103235174960752413073412819)
  ·
    refine ⟨154852762441128619610119229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103235174960752413073412819 154852762441128619610119229)
    ·
      refine ⟨58069785915423232353794711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154852762441128619610119229 58069785915423232353794711)
      ·
        refine ⟨87104678873134848530692067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58069785915423232353794711 87104678873134848530692067)
        ·
          refine ⟨130657018309702272796038101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87104678873134848530692067 130657018309702272796038101)
          ·
            refine ⟨3062273866633647018657143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 130657018309702272796038101 3062273866633647018657143)
            ·
              refine ⟨4593410799950470527985715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062273866633647018657143 4593410799950470527985715)
              ·
                refine ⟨6890116199925705791978573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593410799950470527985715 6890116199925705791978573)
                ·
                  refine ⟨2583793574972139671991965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6890116199925705791978573 2583793574972139671991965)
                  ·
                    refine ⟨968922590614552376996987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2583793574972139671991965 968922590614552376996987)
                    ·
                      rfl

theorem cell22_2830455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_2830455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830455 prefixEnd_2830455 := by exact prefixLift 2830455
  have htrace : WordTrace (prefixWord ++ tailWord_2830455) baseStart_2830455 baseEnd_2830455 := by
    simpa [prefixWord, tailWord_2830455, baseEnd_2830455] using wordTrace_append hprefix tailTrace_2830455
  have hstable : (prefixWord ++ tailWord_2830455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830455).length < 2 ^ (prefixWord ++ tailWord_2830455).sum := by decide
  have hdescent : baseEnd_2830455 < baseStart_2830455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830468 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_2830468 : Nat := 118140960795 + 2830468 * 2 ^ 59
def prefixEnd_2830468 : Nat := 4983230072969 + 3 ^ 40 * 2830468 * 2
def baseEnd_2830468 : Nat := 322975680260074892140649

theorem tailTrace_2830468 : CollatzResearch.WordTrace tailWord_2830468 prefixEnd_2830468 322975680260074892140649 := by
  unfold tailWord_2830468
  simp only [CollatzResearch.WordTrace]
  refine ⟨51617824554852658146818029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68823766073136877529090705 51617824554852658146818029)
  ·
    refine ⟨19356684208069746805056761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51617824554852658146818029 19356684208069746805056761)
    ·
      refine ⟨14517513156052310103792571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19356684208069746805056761 14517513156052310103792571)
      ·
        refine ⟨21776269734078465155688857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517513156052310103792571 21776269734078465155688857)
        ·
          refine ⟨16332202300558848866766643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21776269734078465155688857 16332202300558848866766643)
          ·
            refine ⟨24498303450838273300149965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16332202300558848866766643 24498303450838273300149965)
            ·
              refine ⟨9186863794064352487556237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24498303450838273300149965 9186863794064352487556237)
              ·
                refine ⟨3445073922774132182833589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9186863794064352487556237 3445073922774132182833589)
                ·
                  refine ⟨322975680260074892140649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445073922774132182833589 322975680260074892140649)
                  ·
                    rfl

theorem cell22_2830468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_2830468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830468 prefixEnd_2830468 := by exact prefixLift 2830468
  have htrace : WordTrace (prefixWord ++ tailWord_2830468) baseStart_2830468 baseEnd_2830468 := by
    simpa [prefixWord, tailWord_2830468, baseEnd_2830468] using wordTrace_append hprefix tailTrace_2830468
  have hstable : (prefixWord ++ tailWord_2830468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830468).length < 2 ^ (prefixWord ++ tailWord_2830468).sum := by decide
  have hdescent : baseEnd_2830468 < baseStart_2830468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830511 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_2830511 : Nat := 118140960795 + 2830511 * 2 ^ 59
def prefixEnd_2830511 : Nat := 4983230072969 + 3 ^ 40 * 2830511 * 2
def baseEnd_2830511 : Nat := 968941760558986897596815

theorem tailTrace_2830511 : CollatzResearch.WordTrace tailWord_2830511 prefixEnd_2830511 968941760558986897596815 := by
  unfold tailWord_2830511
  simp only [CollatzResearch.WordTrace]
  refine ⟨103237217448549534637451387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68824811632366356424967591 103237217448549534637451387)
  ·
    refine ⟨154855826172824301956177081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103237217448549534637451387 154855826172824301956177081)
    ·
      refine ⟨116141869629618226467132811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154855826172824301956177081 116141869629618226467132811)
      ·
        refine ⟨174212804444427339700699217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116141869629618226467132811 174212804444427339700699217)
        ·
          refine ⟨130659603333320504775524413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174212804444427339700699217 130659603333320504775524413)
          ·
            refine ⟨48997351249995189290821655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130659603333320504775524413 48997351249995189290821655)
            ·
              refine ⟨73496026874992783936232483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48997351249995189290821655 73496026874992783936232483)
              ·
                refine ⟨110244040312489175904348725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73496026874992783936232483 110244040312489175904348725)
                ·
                  refine ⟨10335378779295860241032693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110244040312489175904348725 10335378779295860241032693)
                  ·
                    refine ⟨968941760558986897596815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10335378779295860241032693 968941760558986897596815)
                    ·
                      rfl

theorem cell22_2830511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_2830511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830511 prefixEnd_2830511 := by exact prefixLift 2830511
  have htrace : WordTrace (prefixWord ++ tailWord_2830511) baseStart_2830511 baseEnd_2830511 := by
    simpa [prefixWord, tailWord_2830511, baseEnd_2830511] using wordTrace_append hprefix tailTrace_2830511
  have hstable : (prefixWord ++ tailWord_2830511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830511).length < 2 ^ (prefixWord ++ tailWord_2830511).sum := by decide
  have hdescent : baseEnd_2830511 < baseStart_2830511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830528 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_2830528 : Nat := 118140960795 + 2830528 * 2 ^ 59
def prefixEnd_2830528 : Nat := 4983230072969 + 3 ^ 40 * 2830528 * 2
def baseEnd_2830528 : Nat := 968947580006404519921763

theorem tailTrace_2830528 : CollatzResearch.WordTrace tailWord_2830528 prefixEnd_2830528 968947580006404519921763 := by
  unfold tailWord_2830528
  simp only [CollatzResearch.WordTrace]
  refine ⟨51618918744743973270410119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68825224992991964360546825 51618918744743973270410119)
  ·
    refine ⟨77428378117115959905615179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51618918744743973270410119 77428378117115959905615179)
    ·
      refine ⟨116142567175673939858422769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77428378117115959905615179 116142567175673939858422769)
      ·
        refine ⟨87106925381755454893817077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116142567175673939858422769 87106925381755454893817077)
        ·
          refine ⟨8166274254539573896295351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87106925381755454893817077 8166274254539573896295351)
          ·
            refine ⟨12249411381809360844443027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166274254539573896295351 12249411381809360844443027)
            ·
              refine ⟨18374117072714041266664541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12249411381809360844443027 18374117072714041266664541)
              ·
                refine ⟨6890293902267765474999203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18374117072714041266664541 6890293902267765474999203)
                ·
                  refine ⟨10335440853401648212498805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6890293902267765474999203 10335440853401648212498805)
                  ·
                    refine ⟨968947580006404519921763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10335440853401648212498805 968947580006404519921763)
                    ·
                      rfl

theorem cell22_2830528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_2830528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830528 prefixEnd_2830528 := by exact prefixLift 2830528
  have htrace : WordTrace (prefixWord ++ tailWord_2830528) baseStart_2830528 baseEnd_2830528 := by
    simpa [prefixWord, tailWord_2830528, baseEnd_2830528] using wordTrace_append hprefix tailTrace_2830528
  have hstable : (prefixWord ++ tailWord_2830528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830528).length < 2 ^ (prefixWord ++ tailWord_2830528).sum := by decide
  have hdescent : baseEnd_2830528 < baseStart_2830528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830549 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2830549 : Nat := 118140960795 + 2830549 * 2 ^ 59
def prefixEnd_2830549 : Nat := 4983230072969 + 3 ^ 40 * 2830549 * 2
def baseEnd_2830549 : Nat := 968954768735567465146699

theorem tailTrace_2830549 : CollatzResearch.WordTrace tailWord_2830549 prefixEnd_2830549 968954768735567465146699 := by
  unfold tailWord_2830549
  simp only [CollatzResearch.WordTrace]
  refine ⟨103238603422411867127334701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68825735614941244751556467 103238603422411867127334701)
  ·
    refine ⟨38714476283404450172750513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103238603422411867127334701 38714476283404450172750513)
    ·
      refine ⟨29035857212553337629562885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38714476283404450172750513 29035857212553337629562885)
      ·
        refine ⟨5444223227353750805543041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29035857212553337629562885 5444223227353750805543041)
        ·
          refine ⟨4083167420515313104157281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5444223227353750805543041 4083167420515313104157281)
          ·
            refine ⟨3062375565386484828117961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4083167420515313104157281 3062375565386484828117961)
            ·
              refine ⟨2296781674039863621088471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062375565386484828117961 2296781674039863621088471)
              ·
                refine ⟨3445172511059795431632707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296781674039863621088471 3445172511059795431632707)
                ·
                  refine ⟨5167758766589693147449061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445172511059795431632707 5167758766589693147449061)
                  ·
                    refine ⟨968954768735567465146699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167758766589693147449061 968954768735567465146699)
                    ·
                      rfl

theorem cell22_2830549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2830549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830549 prefixEnd_2830549 := by exact prefixLift 2830549
  have htrace : WordTrace (prefixWord ++ tailWord_2830549) baseStart_2830549 baseEnd_2830549 := by
    simpa [prefixWord, tailWord_2830549, baseEnd_2830549] using wordTrace_append hprefix tailTrace_2830549
  have hstable : (prefixWord ++ tailWord_2830549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830549).length < 2 ^ (prefixWord ++ tailWord_2830549).sum := by decide
  have hdescent : baseEnd_2830549 < baseStart_2830549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830648 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_2830648 : Nat := 118140960795 + 2830648 * 2 ^ 59
def prefixEnd_2830648 : Nat := 4983230072969 + 3 ^ 40 * 2830648 * 2
def baseEnd_2830648 : Nat := 322996219486254735640465

theorem tailTrace_2830648 : CollatzResearch.WordTrace tailWord_2830648 prefixEnd_2830648 322996219486254735640465 := by
  unfold tailWord_2830648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51621107124526603517594299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68828142832702138023459065 51621107124526603517594299)
  ·
    refine ⟨77431660686789905276391449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51621107124526603517594299 77431660686789905276391449)
    ·
      refine ⟨58073745515092428957293587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77431660686789905276391449 58073745515092428957293587)
      ·
        refine ⟨87110618272638643435940381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58073745515092428957293587 87110618272638643435940381)
        ·
          refine ⟨32666481852239491288477643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87110618272638643435940381 32666481852239491288477643)
          ·
            refine ⟨48999722778359236932716465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32666481852239491288477643 48999722778359236932716465)
            ·
              refine ⟨36749792083769427699537349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48999722778359236932716465 36749792083769427699537349)
              ·
                refine ⟨6890586015706767693663253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36749792083769427699537349 6890586015706767693663253)
                ·
                  refine ⟨322996219486254735640465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6890586015706767693663253 322996219486254735640465)
                  ·
                    rfl

theorem cell22_2830648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_2830648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830648 prefixEnd_2830648 := by exact prefixLift 2830648
  have htrace : WordTrace (prefixWord ++ tailWord_2830648) baseStart_2830648 baseEnd_2830648 := by
    simpa [prefixWord, tailWord_2830648, baseEnd_2830648] using wordTrace_append hprefix tailTrace_2830648
  have hstable : (prefixWord ++ tailWord_2830648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830648).length < 2 ^ (prefixWord ++ tailWord_2830648).sum := by decide
  have hdescent : baseEnd_2830648 < baseStart_2830648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830650 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_2830650 : Nat := 118140960795 + 2830650 * 2 ^ 59
def prefixEnd_2830650 : Nat := 4983230072969 + 3 ^ 40 * 2830650 * 2
def baseEnd_2830650 : Nat := 968989343099636868371389

theorem tailTrace_2830650 : CollatzResearch.WordTrace tailWord_2830650 prefixEnd_2830650 968989343099636868371389 := by
  unfold tailWord_2830650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810571798761490344190351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68828191463363974251174269 25810571798761490344190351)
  ·
    refine ⟨38715857698142235516285527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25810571798761490344190351 38715857698142235516285527)
    ·
      refine ⟨58073786547213353274428291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38715857698142235516285527 58073786547213353274428291)
      ·
        refine ⟨87110679820820029911642437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58073786547213353274428291 87110679820820029911642437)
        ·
          refine ⟨16333252466403755608432957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87110679820820029911642437 16333252466403755608432957)
          ·
            refine ⟨6124969674901408353162359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16333252466403755608432957 6124969674901408353162359)
            ·
              refine ⟨9187454512352112529743539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6124969674901408353162359 9187454512352112529743539)
              ·
                refine ⟨13781181768528168794615309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9187454512352112529743539 13781181768528168794615309)
                ·
                  refine ⟨5167943163198063297980741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13781181768528168794615309 5167943163198063297980741)
                  ·
                    refine ⟨968989343099636868371389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167943163198063297980741 968989343099636868371389)
                    ·
                      rfl

theorem cell22_2830650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_2830650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830650 prefixEnd_2830650 := by exact prefixLift 2830650
  have htrace : WordTrace (prefixWord ++ tailWord_2830650) baseStart_2830650 baseEnd_2830650 := by
    simpa [prefixWord, tailWord_2830650, baseEnd_2830650] using wordTrace_append hprefix tailTrace_2830650
  have hstable : (prefixWord ++ tailWord_2830650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830650).length < 2 ^ (prefixWord ++ tailWord_2830650).sum := by decide
  have hdescent : baseEnd_2830650 < baseStart_2830650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830665 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 4]
def baseStart_2830665 : Nat := 118140960795 + 2830665 * 2 ^ 59
def prefixEnd_2830665 : Nat := 4983230072969 + 3 ^ 40 * 2830665 * 2
def baseEnd_2830665 : Nat := 322998159302060609748781

theorem tailTrace_2830665 : CollatzResearch.WordTrace tailWord_2830665 prefixEnd_2830665 322998159302060609748781 := by
  unfold tailWord_2830665
  simp only [CollatzResearch.WordTrace]
  refine ⟨103242834289991618938557449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68828556193327745959038299 103242834289991618938557449)
  ·
    refine ⟨77432125717493714203918087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103242834289991618938557449 77432125717493714203918087)
    ·
      refine ⟨116148188576240571305877131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77432125717493714203918087 116148188576240571305877131)
      ·
        refine ⟨174222282864360856958815697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116148188576240571305877131 174222282864360856958815697)
        ·
          refine ⟨130666712148270642719111773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174222282864360856958815697 130666712148270642719111773)
          ·
            refine ⟨49000017055601491019666915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130666712148270642719111773 49000017055601491019666915)
            ·
              refine ⟨73500025583402236529500373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49000017055601491019666915 73500025583402236529500373)
              ·
                refine ⟨1722656849610989918660165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73500025583402236529500373 1722656849610989918660165)
                ·
                  refine ⟨322998159302060609748781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722656849610989918660165 322998159302060609748781)
                  ·
                    rfl

theorem cell22_2830665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_2830665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830665 prefixEnd_2830665 := by exact prefixLift 2830665
  have htrace : WordTrace (prefixWord ++ tailWord_2830665) baseStart_2830665 baseEnd_2830665 := by
    simpa [prefixWord, tailWord_2830665, baseEnd_2830665] using wordTrace_append hprefix tailTrace_2830665
  have hstable : (prefixWord ++ tailWord_2830665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830665).length < 2 ^ (prefixWord ++ tailWord_2830665).sum := by decide
  have hdescent : baseEnd_2830665 < baseStart_2830665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830725 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_2830725 : Nat := 118140960795 + 2830725 * 2 ^ 59
def prefixEnd_2830725 : Nat := 4983230072969 + 3 ^ 40 * 2830725 * 2
def baseEnd_2830725 : Nat := 969015017132361672746159

theorem tailTrace_2830725 : CollatzResearch.WordTrace tailWord_2830725 prefixEnd_2830725 969015017132361672746159 := by
  unfold tailWord_2830725
  simp only [CollatzResearch.WordTrace]
  refine ⟨103245022669774249185741629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68830015113182832790494419 103245022669774249185741629)
  ·
    refine ⟨38716883501165343444653111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103245022669774249185741629 38716883501165343444653111)
    ·
      refine ⟨58075325251748015166979667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38716883501165343444653111 58075325251748015166979667)
      ·
        refine ⟨87112987877622022750469501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58075325251748015166979667 87112987877622022750469501)
        ·
          refine ⟨32667370454108258531426063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87112987877622022750469501 32667370454108258531426063)
          ·
            refine ⟨49001055681162387797139095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32667370454108258531426063 49001055681162387797139095)
            ·
              refine ⟨73501583521743581695708643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49001055681162387797139095 73501583521743581695708643)
              ·
                refine ⟨110252375282615372543562965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73501583521743581695708643 110252375282615372543562965)
                ·
                  refine ⟨2584040045686297793989757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110252375282615372543562965 2584040045686297793989757)
                  ·
                    refine ⟨969015017132361672746159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584040045686297793989757 969015017132361672746159)
                    ·
                      rfl

theorem cell22_2830725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_2830725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830725 prefixEnd_2830725 := by exact prefixLift 2830725
  have htrace : WordTrace (prefixWord ++ tailWord_2830725) baseStart_2830725 baseEnd_2830725 := by
    simpa [prefixWord, tailWord_2830725, baseEnd_2830725] using wordTrace_append hprefix tailTrace_2830725
  have hstable : (prefixWord ++ tailWord_2830725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830725).length < 2 ^ (prefixWord ++ tailWord_2830725).sum := by decide
  have hdescent : baseEnd_2830725 < baseStart_2830725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830849 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2830849 : Nat := 118140960795 + 2830849 * 2 ^ 59
def prefixEnd_2830849 : Nat := 4983230072969 + 3 ^ 40 * 2830849 * 2
def baseEnd_2830849 : Nat := 969057464866466682645779

theorem tailTrace_2830849 : CollatzResearch.WordTrace tailWord_2830849 prefixEnd_2830849 969057464866466682645779 := by
  unfold tailWord_2830849
  simp only [CollatzResearch.WordTrace]
  refine ⟨103249545321325018363255601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68833030214216678908837067 103249545321325018363255601)
  ·
    refine ⟨77437158990993763772441701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103249545321325018363255601 77437158990993763772441701)
    ·
      refine ⟨14519467310811330707332819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77437158990993763772441701 14519467310811330707332819)
      ·
        refine ⟨21779200966216996060999229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14519467310811330707332819 21779200966216996060999229)
        ·
          refine ⟨8167200362331373522874711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21779200966216996060999229 8167200362331373522874711)
          ·
            refine ⟨12250800543497060284312067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8167200362331373522874711 12250800543497060284312067)
            ·
              refine ⟨18376200815245590426468101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12250800543497060284312067 18376200815245590426468101)
              ·
                refine ⟨3445537652858548204962769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18376200815245590426468101 3445537652858548204962769)
                ·
                  refine ⟨2584153239643911153722077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3445537652858548204962769 2584153239643911153722077)
                  ·
                    refine ⟨969057464866466682645779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584153239643911153722077 969057464866466682645779)
                    ·
                      rfl

theorem cell22_2830849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2830849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830849 prefixEnd_2830849 := by exact prefixLift 2830849
  have htrace : WordTrace (prefixWord ++ tailWord_2830849) baseStart_2830849 baseEnd_2830849 := by
    simpa [prefixWord, tailWord_2830849, baseEnd_2830849] using wordTrace_append hprefix tailTrace_2830849
  have hstable : (prefixWord ++ tailWord_2830849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830849).length < 2 ^ (prefixWord ++ tailWord_2830849).sum := by decide
  have hdescent : baseEnd_2830849 < baseStart_2830849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830862 : List Nat := [4, 1, 1, 2, 3, 1, 3, 7]
def baseStart_2830862 : Nat := 118140960795 + 2830862 * 2 ^ 59
def prefixEnd_2830862 : Nat := 4983230072969 + 3 ^ 40 * 2830862 * 2
def baseEnd_2830862 : Nat := 107673546114682109118971

theorem tailTrace_2830862 : CollatzResearch.WordTrace tailWord_2830862 prefixEnd_2830862 107673546114682109118971 := by
  unfold tailWord_2830862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12906252433784740197934855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68833346313518614388985893 12906252433784740197934855)
  ·
    refine ⟨19359378650677110296902283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12906252433784740197934855 19359378650677110296902283)
    ·
      refine ⟨29039067976015665445353425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19359378650677110296902283 29039067976015665445353425)
      ·
        refine ⟨21779300982011749084015069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29039067976015665445353425 21779300982011749084015069)
        ·
          refine ⟨8167237868254405906505651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21779300982011749084015069 8167237868254405906505651)
          ·
            refine ⟨12250856802381608859758477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8167237868254405906505651 12250856802381608859758477)
            ·
              refine ⟨4594071300893103322409429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12250856802381608859758477 4594071300893103322409429)
              ·
                refine ⟨107673546114682109118971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4594071300893103322409429 107673546114682109118971)
                ·
                  rfl

theorem cell22_2830862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_2830862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830862 prefixEnd_2830862 := by exact prefixLift 2830862
  have htrace : WordTrace (prefixWord ++ tailWord_2830862) baseStart_2830862 baseEnd_2830862 := by
    simpa [prefixWord, tailWord_2830862, baseEnd_2830862] using wordTrace_append hprefix tailTrace_2830862
  have hstable : (prefixWord ++ tailWord_2830862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830862).length < 2 ^ (prefixWord ++ tailWord_2830862).sum := by decide
  have hdescent : baseEnd_2830862 < baseStart_2830862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830900 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_2830900 : Nat := 118140960795 + 2830900 * 2 ^ 59
def prefixEnd_2830900 : Nat := 4983230072969 + 3 ^ 40 * 2830900 * 2
def baseEnd_2830900 : Nat := 969074923208719549620623

theorem tailTrace_2830900 : CollatzResearch.WordTrace tailWord_2830900 prefixEnd_2830900 969074923208719549620623 := by
  unfold tailWord_2830900
  simp only [CollatzResearch.WordTrace]
  refine ⟨51625702722070127036681077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68834270296093502715574769 51625702722070127036681077)
  ·
    refine ⟨4839909630194074409688851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51625702722070127036681077 4839909630194074409688851)
    ·
      refine ⟨7259864445291111614533277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839909630194074409688851 7259864445291111614533277)
      ·
        refine ⟨2722449166984166855449979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7259864445291111614533277 2722449166984166855449979)
        ·
          refine ⟨4083673750476250283174969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722449166984166855449979 4083673750476250283174969)
          ·
            refine ⟨3062755312857187712381227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4083673750476250283174969 3062755312857187712381227)
            ·
              refine ⟨4594132969285781568571841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062755312857187712381227 4594132969285781568571841)
              ·
                refine ⟨3445599726964336176428881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594132969285781568571841 3445599726964336176428881)
                ·
                  refine ⟨2584199795223252132321661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3445599726964336176428881 2584199795223252132321661)
                  ·
                    refine ⟨969074923208719549620623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584199795223252132321661 969074923208719549620623)
                    ·
                      rfl

theorem cell22_2830900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_2830900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830900 prefixEnd_2830900 := by exact prefixLift 2830900
  have htrace : WordTrace (prefixWord ++ tailWord_2830900) baseStart_2830900 baseEnd_2830900 := by
    simpa [prefixWord, tailWord_2830900, baseEnd_2830900] using wordTrace_append hprefix tailTrace_2830900
  have hstable : (prefixWord ++ tailWord_2830900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830900).length < 2 ^ (prefixWord ++ tailWord_2830900).sum := by decide
  have hdescent : baseEnd_2830900 < baseStart_2830900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830922 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_2830922 : Nat := 118140960795 + 2830922 * 2 ^ 59
def prefixEnd_2830922 : Nat := 4983230072969 + 3 ^ 40 * 2830922 * 2
def baseEnd_2830922 : Nat := 969082454258318825570555

theorem tailTrace_2830922 : CollatzResearch.WordTrace tailWord_2830922 prefixEnd_2830922 969082454258318825570555 := by
  unfold tailWord_2830922
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813051962515137957665755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68834805233373701220442013 25813051962515137957665755)
  ·
    refine ⟨38719577943772706936498633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25813051962515137957665755 38719577943772706936498633)
    ·
      refine ⟨29039683457829530202373975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38719577943772706936498633 29039683457829530202373975)
      ·
        refine ⟨43559525186744295303560963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29039683457829530202373975 43559525186744295303560963)
        ·
          refine ⟨65339287780116442955341445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43559525186744295303560963 65339287780116442955341445)
          ·
            refine ⟨12251116458771833054126521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65339287780116442955341445 12251116458771833054126521)
            ·
              refine ⟨9188337344078874790594891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12251116458771833054126521 9188337344078874790594891)
              ·
                refine ⟨13782506016118312185892337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9188337344078874790594891 13782506016118312185892337)
                ·
                  refine ⟨10336879512088734139419253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13782506016118312185892337 10336879512088734139419253)
                  ·
                    refine ⟨969082454258318825570555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10336879512088734139419253 969082454258318825570555)
                    ·
                      rfl

theorem cell22_2830922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_2830922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830922 prefixEnd_2830922 := by exact prefixLift 2830922
  have htrace : WordTrace (prefixWord ++ tailWord_2830922) baseStart_2830922 baseEnd_2830922 := by
    simpa [prefixWord, tailWord_2830922, baseEnd_2830922] using wordTrace_append hprefix tailTrace_2830922
  have hstable : (prefixWord ++ tailWord_2830922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830922).length < 2 ^ (prefixWord ++ tailWord_2830922).sum := by decide
  have hdescent : baseEnd_2830922 < baseStart_2830922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830924 : List Nat := [2, 2, 1, 3, 1, 2, 5, 1, 5]
def baseStart_2830924 : Nat := 118140960795 + 2830924 * 2 ^ 59
def prefixEnd_2830924 : Nat := 4983230072969 + 3 ^ 40 * 2830924 * 2
def baseEnd_2830924 : Nat := 323027712966397162340183

theorem tailTrace_2830924 : CollatzResearch.WordTrace tailWord_2830924 prefixEnd_2830924 323027712966397162340183 := by
  unfold tailWord_2830924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51626140398026653086117913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68834853864035537448157217 51626140398026653086117913)
  ·
    refine ⟨38719605298519989814588435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51626140398026653086117913 38719605298519989814588435)
    ·
      refine ⟨58079407947779984721882653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38719605298519989814588435 58079407947779984721882653)
      ·
        refine ⟨21779777980417494270705995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58079407947779984721882653 21779777980417494270705995)
        ·
          refine ⟨32669666970626241406058993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21779777980417494270705995 32669666970626241406058993)
          ·
            refine ⟨24502250227969681054544245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32669666970626241406058993 24502250227969681054544245)
            ·
              refine ⟨2297085958872157598863523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24502250227969681054544245 2297085958872157598863523)
              ·
                refine ⟨3445628938308236398295285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297085958872157598863523 3445628938308236398295285)
                ·
                  refine ⟨323027712966397162340183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445628938308236398295285 323027712966397162340183)
                  ·
                    rfl

theorem cell22_2830924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_2830924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830924 prefixEnd_2830924 := by exact prefixLift 2830924
  have htrace : WordTrace (prefixWord ++ tailWord_2830924) baseStart_2830924 baseEnd_2830924 := by
    simpa [prefixWord, tailWord_2830924, baseEnd_2830924] using wordTrace_append hprefix tailTrace_2830924
  have hstable : (prefixWord ++ tailWord_2830924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830924).length < 2 ^ (prefixWord ++ tailWord_2830924).sum := by decide
  have hdescent : baseEnd_2830924 < baseStart_2830924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830954 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2830954 : Nat := 118140960795 + 2830954 * 2 ^ 59
def prefixEnd_2830954 : Nat := 4983230072969 + 3 ^ 40 * 2830954 * 2
def baseEnd_2830954 : Nat := 969093408512281408770457

theorem tailTrace_2830954 : CollatzResearch.WordTrace tailWord_2830954 prefixEnd_2830954 969093408512281408770457 := by
  unfold tailWord_2830954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25813343746486155323956979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68835583323963080863885277 25813343746486155323956979)
  ·
    refine ⟨38720015619729232985935469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25813343746486155323956979 38720015619729232985935469)
    ·
      refine ⟨14520005857398462369725801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38720015619729232985935469 14520005857398462369725801)
      ·
        refine ⟨10890004393048846777294351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14520005857398462369725801 10890004393048846777294351)
        ·
          refine ⟨16335006589573270165941527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10890004393048846777294351 16335006589573270165941527)
          ·
            refine ⟨24502509884359905248912291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16335006589573270165941527 24502509884359905248912291)
            ·
              refine ⟨36753764826539857873368437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24502509884359905248912291 36753764826539857873368437)
              ·
                refine ⟨3445665452488111675628291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36753764826539857873368437 3445665452488111675628291)
                ·
                  refine ⟨5168498178732167513442437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445665452488111675628291 5168498178732167513442437)
                  ·
                    refine ⟨969093408512281408770457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5168498178732167513442437 969093408512281408770457)
                    ·
                      rfl

theorem cell22_2830954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2830954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830954 prefixEnd_2830954 := by exact prefixLift 2830954
  have htrace : WordTrace (prefixWord ++ tailWord_2830954) baseStart_2830954 baseEnd_2830954 := by
    simpa [prefixWord, tailWord_2830954, baseEnd_2830954] using wordTrace_append hprefix tailTrace_2830954
  have hstable : (prefixWord ++ tailWord_2830954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830954).length < 2 ^ (prefixWord ++ tailWord_2830954).sum := by decide
  have hdescent : baseEnd_2830954 < baseStart_2830954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830969 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 6]
def baseStart_2830969 : Nat := 118140960795 + 2830969 * 2 ^ 59
def prefixEnd_2830969 : Nat := 4983230072969 + 3 ^ 40 * 2830969 * 2
def baseEnd_2830969 : Nat := 323032847772942123215137

theorem tailTrace_2830969 : CollatzResearch.WordTrace tailWord_2830969 prefixEnd_2830969 323032847772942123215137 := by
  unfold tailWord_2830969
  simp only [CollatzResearch.WordTrace]
  refine ⟨103253922080890278857623961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68835948053926852571749307 103253922080890278857623961)
  ·
    refine ⟨77440441560667709143217971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103253922080890278857623961 77440441560667709143217971)
    ·
      refine ⟨116160662341001563714826957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77440441560667709143217971 116160662341001563714826957)
      ·
        refine ⟨43560248377875586393060109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116160662341001563714826957 43560248377875586393060109)
        ·
          refine ⟨16335093141703344897397541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43560248377875586393060109 16335093141703344897397541)
          ·
            refine ⟨3062829964069377168262039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16335093141703344897397541 3062829964069377168262039)
            ·
              refine ⟨4594244946104065752393059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062829964069377168262039 4594244946104065752393059)
              ·
                refine ⟨6891367419156098628589589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594244946104065752393059 6891367419156098628589589)
                ·
                  refine ⟨323032847772942123215137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6891367419156098628589589 323032847772942123215137)
                  ·
                    rfl

theorem cell22_2830969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_2830969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830969 prefixEnd_2830969 := by exact prefixLift 2830969
  have htrace : WordTrace (prefixWord ++ tailWord_2830969) baseStart_2830969 baseEnd_2830969 := by
    simpa [prefixWord, tailWord_2830969, baseEnd_2830969] using wordTrace_append hprefix tailTrace_2830969
  have hstable : (prefixWord ++ tailWord_2830969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830969).length < 2 ^ (prefixWord ++ tailWord_2830969).sum := by decide
  have hdescent : baseEnd_2830969 < baseStart_2830969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2830999 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 2, 4]
def baseStart_2830999 : Nat := 118140960795 + 2830999 * 2 ^ 59
def prefixEnd_2830999 : Nat := 4983230072969 + 3 ^ 40 * 2830999 * 2
def baseEnd_2830999 : Nat := 969108812931916291395319

theorem tailTrace_2830999 : CollatzResearch.WordTrace tailWord_2830999 prefixEnd_2830999 969108812931916291395319 := by
  unfold tailWord_2830999
  simp only [CollatzResearch.WordTrace]
  refine ⟨103255016270781593981216051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68836677513854395987477367 103255016270781593981216051)
  ·
    refine ⟨154882524406172390971824077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103255016270781593981216051 154882524406172390971824077)
    ·
      refine ⟨58080946652314646614434029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154882524406172390971824077 58080946652314646614434029)
      ·
        refine ⟨21780354994617992480412761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58080946652314646614434029 21780354994617992480412761)
        ·
          refine ⟨16335266245963494360309571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21780354994617992480412761 16335266245963494360309571)
          ·
            refine ⟨24502899368945241540464357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16335266245963494360309571 24502899368945241540464357)
            ·
              refine ⟨4594293631677232788837067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24502899368945241540464357 4594293631677232788837067)
              ·
                refine ⟨6891440447515849183255601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594293631677232788837067 6891440447515849183255601)
                ·
                  refine ⟨5168580335636886887441701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6891440447515849183255601 5168580335636886887441701)
                  ·
                    refine ⟨969108812931916291395319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5168580335636886887441701 969108812931916291395319)
                    ·
                      rfl

theorem cell22_2830999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_2830999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2830999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2830999 prefixEnd_2830999 := by exact prefixLift 2830999
  have htrace : WordTrace (prefixWord ++ tailWord_2830999) baseStart_2830999 baseEnd_2830999 := by
    simpa [prefixWord, tailWord_2830999, baseEnd_2830999] using wordTrace_append hprefix tailTrace_2830999
  have hstable : (prefixWord ++ tailWord_2830999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2830999).length < 2 ^ (prefixWord ++ tailWord_2830999).sum := by decide
  have hdescent : baseEnd_2830999 < baseStart_2830999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2830999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831027 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_2831027 : Nat := 118140960795 + 2831027 * 2 ^ 59
def prefixEnd_2831027 : Nat := 4983230072969 + 3 ^ 40 * 2831027 * 2
def baseEnd_2831027 : Nat := 969118397904133551695233

theorem tailTrace_2831027 : CollatzResearch.WordTrace tailWord_2831027 prefixEnd_2831027 969118397904133551695233 := by
  unfold tailWord_2831027
  simp only [CollatzResearch.WordTrace]
  refine ⟨103256037514680154763235335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68837358343120103175490223 103256037514680154763235335)
  ·
    refine ⟨154884056272020232144853003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103256037514680154763235335 154884056272020232144853003)
    ·
      refine ⟨232326084408030348217279505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154884056272020232144853003 232326084408030348217279505)
      ·
        refine ⟨174244563306022761162959629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232326084408030348217279505 174244563306022761162959629)
        ·
          refine ⟨65341711239758535436109861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174244563306022761162959629 65341711239758535436109861)
          ·
            refine ⟨12251570857454725394270599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65341711239758535436109861 12251570857454725394270599)
            ·
              refine ⟨18377356286182088091405899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251570857454725394270599 18377356286182088091405899)
              ·
                refine ⟨27566034429273132137108849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18377356286182088091405899 27566034429273132137108849)
                ·
                  refine ⟨20674525821954849102831637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27566034429273132137108849 20674525821954849102831637)
                  ·
                    refine ⟨969118397904133551695233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20674525821954849102831637 969118397904133551695233)
                    ·
                      rfl

theorem cell22_2831027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_2831027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831027 prefixEnd_2831027 := by exact prefixLift 2831027
  have htrace : WordTrace (prefixWord ++ tailWord_2831027) baseStart_2831027 baseEnd_2831027 := by
    simpa [prefixWord, tailWord_2831027, baseEnd_2831027] using wordTrace_append hprefix tailTrace_2831027
  have hstable : (prefixWord ++ tailWord_2831027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831027).length < 2 ^ (prefixWord ++ tailWord_2831027).sum := by decide
  have hdescent : baseEnd_2831027 < baseStart_2831027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831031 : List Nat := [1, 1, 3, 1, 7, 1, 1, 7]
def baseStart_2831031 : Nat := 118140960795 + 2831031 * 2 ^ 59
def prefixEnd_2831031 : Nat := 4983230072969 + 3 ^ 40 * 2831031 * 2
def baseEnd_2831031 : Nat := 107679974131764319399469

theorem tailTrace_2831031 : CollatzResearch.WordTrace tailWord_2831031 prefixEnd_2831031 107679974131764319399469 := by
  unfold tailWord_2831031
  simp only [CollatzResearch.WordTrace]
  refine ⟨103256183406665663446380947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68837455604443775630920631 103256183406665663446380947)
  ·
    refine ⟨154884275109998495169571421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103256183406665663446380947 154884275109998495169571421)
    ·
      refine ⟨58081603166249435688589283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154884275109998495169571421 58081603166249435688589283)
      ·
        refine ⟨87122404749374153532883925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58081603166249435688589283 87122404749374153532883925)
        ·
          refine ⟨2041931361313456723426967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 87122404749374153532883925 2041931361313456723426967)
          ·
            refine ⟨3062897041970185085140451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041931361313456723426967 3062897041970185085140451)
            ·
              refine ⟨4594345562955277627710677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062897041970185085140451 4594345562955277627710677)
              ·
                refine ⟨107679974131764319399469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4594345562955277627710677 107679974131764319399469)
                ·
                  rfl

theorem cell22_2831031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 7].length) (baseStart_2831031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831031 prefixEnd_2831031 := by exact prefixLift 2831031
  have htrace : WordTrace (prefixWord ++ tailWord_2831031) baseStart_2831031 baseEnd_2831031 := by
    simpa [prefixWord, tailWord_2831031, baseEnd_2831031] using wordTrace_append hprefix tailTrace_2831031
  have hstable : (prefixWord ++ tailWord_2831031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831031).length < 2 ^ (prefixWord ++ tailWord_2831031).sum := by decide
  have hdescent : baseEnd_2831031 < baseStart_2831031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831057 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_2831057 : Nat := 118140960795 + 2831057 * 2 ^ 59
def prefixEnd_2831057 : Nat := 4983230072969 + 3 ^ 40 * 2831057 * 2
def baseEnd_2831057 : Nat := 969128667517223473445141

theorem tailTrace_2831057 : CollatzResearch.WordTrace tailWord_2831057 prefixEnd_2831057 969128667517223473445141 := by
  unfold tailWord_2831057
  simp only [CollatzResearch.WordTrace]
  refine ⟨103257131704571469886827425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68838087803047646591218283 103257131704571469886827425)
  ·
    refine ⟨77442848778428602415120569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103257131704571469886827425 77442848778428602415120569)
    ·
      refine ⟨58082136583821451811340427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77442848778428602415120569 58082136583821451811340427)
      ·
        refine ⟨87123204875732177717010641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58082136583821451811340427 87123204875732177717010641)
        ·
          refine ⟨65342403656799133287757981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87123204875732177717010641 65342403656799133287757981)
          ·
            refine ⟨24503401371299674982909243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65342403656799133287757981 24503401371299674982909243)
            ·
              refine ⟨36755102056949512474363865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24503401371299674982909243 36755102056949512474363865)
              ·
                refine ⟨27566326542712134355772899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36755102056949512474363865 27566326542712134355772899)
                ·
                  refine ⟨41349489814068201533659349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27566326542712134355772899 41349489814068201533659349)
                  ·
                    refine ⟨969128667517223473445141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41349489814068201533659349 969128667517223473445141)
                    ·
                      rfl

theorem cell22_2831057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_2831057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831057 prefixEnd_2831057 := by exact prefixLift 2831057
  have htrace : WordTrace (prefixWord ++ tailWord_2831057) baseStart_2831057 baseEnd_2831057 := by
    simpa [prefixWord, tailWord_2831057, baseEnd_2831057] using wordTrace_append hprefix tailTrace_2831057
  have hstable : (prefixWord ++ tailWord_2831057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831057).length < 2 ^ (prefixWord ++ tailWord_2831057).sum := by decide
  have hdescent : baseEnd_2831057 < baseStart_2831057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831063 : List Nat := [1, 1, 3, 2, 1, 5, 2, 3, 1, 3]
def baseStart_2831063 : Nat := 118140960795 + 2831063 * 2 ^ 59
def prefixEnd_2831063 : Nat := 4983230072969 + 3 ^ 40 * 2831063 * 2
def baseEnd_2831063 : Nat := 969130721439841457795123

theorem tailTrace_2831063 : CollatzResearch.WordTrace tailWord_2831063 prefixEnd_2831063 969130721439841457795123 := by
  unfold tailWord_2831063
  simp only [CollatzResearch.WordTrace]
  refine ⟨103257350542549732911545843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68838233695033155274363895 103257350542549732911545843)
  ·
    refine ⟨154886025813824599367318765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103257350542549732911545843 154886025813824599367318765)
    ·
      refine ⟨58082259680184224762744537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154886025813824599367318765 58082259680184224762744537)
      ·
        refine ⟨43561694760138168572058403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58082259680184224762744537 43561694760138168572058403)
        ·
          refine ⟨65342542140207252858087605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43561694760138168572058403 65342542140207252858087605)
          ·
            refine ⟨6125863325644429955445713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65342542140207252858087605 6125863325644429955445713)
            ·
              refine ⟨4594397494233322466584285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6125863325644429955445713 4594397494233322466584285)
              ·
                refine ⟨1722899060337495924969107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4594397494233322466584285 1722899060337495924969107)
                ·
                  refine ⟨2584348590506243887453661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1722899060337495924969107 2584348590506243887453661)
                  ·
                    refine ⟨969130721439841457795123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584348590506243887453661 969130721439841457795123)
                    ·
                      rfl

theorem cell22_2831063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_2831063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831063 prefixEnd_2831063 := by exact prefixLift 2831063
  have htrace : WordTrace (prefixWord ++ tailWord_2831063) baseStart_2831063 baseEnd_2831063 := by
    simpa [prefixWord, tailWord_2831063, baseEnd_2831063] using wordTrace_append hprefix tailTrace_2831063
  have hstable : (prefixWord ++ tailWord_2831063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831063).length < 2 ^ (prefixWord ++ tailWord_2831063).sum := by decide
  have hdescent : baseEnd_2831063 < baseStart_2831063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831076 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 5]
def baseStart_2831076 : Nat := 118140960795 + 2831076 * 2 ^ 59
def prefixEnd_2831076 : Nat := 4983230072969 + 3 ^ 40 * 2831076 * 2
def baseEnd_2831076 : Nat := 323045057201837919073361

theorem tailTrace_2831076 : CollatzResearch.WordTrace tailWord_2831076 prefixEnd_2831076 323045057201837919073361 := by
  unfold tailWord_2831076
  simp only [CollatzResearch.WordTrace]
  refine ⟨51628912345751318065884541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68838549794335090754512721 51628912345751318065884541)
  ·
    refine ⟨19360842129656744274706703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51628912345751318065884541 19360842129656744274706703)
    ·
      refine ⟨29041263194485116412060055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19360842129656744274706703 29041263194485116412060055)
      ·
        refine ⟨43561894791727674618090083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29041263194485116412060055 43561894791727674618090083)
        ·
          refine ⟨65342842187591511927135125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43561894791727674618090083 65342842187591511927135125)
          ·
            refine ⟨3062945727543352121584459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65342842187591511927135125 3062945727543352121584459)
            ·
              refine ⟨4594418591315028182376689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062945727543352121584459 4594418591315028182376689)
              ·
                refine ⟨3445813943486271136782517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594418591315028182376689 3445813943486271136782517)
                ·
                  refine ⟨323045057201837919073361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445813943486271136782517 323045057201837919073361)
                  ·
                    rfl

theorem cell22_2831076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_2831076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831076 prefixEnd_2831076 := by exact prefixLift 2831076
  have htrace : WordTrace (prefixWord ++ tailWord_2831076) baseStart_2831076 baseEnd_2831076 := by
    simpa [prefixWord, tailWord_2831076, baseEnd_2831076] using wordTrace_append hprefix tailTrace_2831076
  have hstable : (prefixWord ++ tailWord_2831076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831076).length < 2 ^ (prefixWord ++ tailWord_2831076).sum := by decide
  have hdescent : baseEnd_2831076 < baseStart_2831076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831119 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 6, 3]
def baseStart_2831119 : Nat := 118140960795 + 2831119 * 2 ^ 59
def prefixEnd_2831119 : Nat := 4983230072969 + 3 ^ 40 * 2831119 * 2
def baseEnd_2831119 : Nat := 969149891384275978394951

theorem tailTrace_2831119 : CollatzResearch.WordTrace tailWord_2831119 prefixEnd_2831119 969149891384275978394951 := by
  unfold tailWord_2831119
  simp only [CollatzResearch.WordTrace]
  refine ⟨103259393030346854475584411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68839595353564569650389607 103259393030346854475584411)
  ·
    refine ⟨154889089545520281713376617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103259393030346854475584411 154889089545520281713376617)
    ·
      refine ⟨116166817159140211285032463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154889089545520281713376617 116166817159140211285032463)
      ·
        refine ⟨174250225738710316927548695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116166817159140211285032463 174250225738710316927548695)
        ·
          refine ⟨261375338608065475391323043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174250225738710316927548695 261375338608065475391323043)
          ·
            refine ⟨392063007912098213086984565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261375338608065475391323043 392063007912098213086984565)
            ·
              refine ⟨36755906991759207476904803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 392063007912098213086984565 36755906991759207476904803)
              ·
                refine ⟨55133860487638811215357205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36755906991759207476904803 55133860487638811215357205)
                ·
                  refine ⟨2584399710358069275719869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55133860487638811215357205 2584399710358069275719869)
                  ·
                    refine ⟨969149891384275978394951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584399710358069275719869 969149891384275978394951)
                    ·
                      rfl

theorem cell22_2831119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_2831119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831119 prefixEnd_2831119 := by exact prefixLift 2831119
  have htrace : WordTrace (prefixWord ++ tailWord_2831119) baseStart_2831119 baseEnd_2831119 := by
    simpa [prefixWord, tailWord_2831119, baseEnd_2831119] using wordTrace_append hprefix tailTrace_2831119
  have hstable : (prefixWord ++ tailWord_2831119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831119).length < 2 ^ (prefixWord ++ tailWord_2831119).sum := by decide
  have hdescent : baseEnd_2831119 < baseStart_2831119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831121 : List Nat := [1, 2, 2, 1, 1, 3, 5, 3, 4]
def baseStart_2831121 : Nat := 118140960795 + 2831121 * 2 ^ 59
def prefixEnd_2831121 : Nat := 4983230072969 + 3 ^ 40 * 2831121 * 2
def baseEnd_2831121 : Nat := 323050192008382879948315

theorem tailTrace_2831121 : CollatzResearch.WordTrace tailWord_2831121 prefixEnd_2831121 323050192008382879948315 := by
  unfold tailWord_2831121
  simp only [CollatzResearch.WordTrace]
  refine ⟨103259465976339608817157217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68839643984226405878104811 103259465976339608817157217)
  ·
    refine ⟨77444599482254706612867913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103259465976339608817157217 77444599482254706612867913)
    ·
      refine ⟨58083449611691029959650935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77444599482254706612867913 58083449611691029959650935)
      ·
        refine ⟨87125174417536544939476403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58083449611691029959650935 87125174417536544939476403)
        ·
          refine ⟨130687761626304817409214605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87125174417536544939476403 130687761626304817409214605)
          ·
            refine ⟨49007910609864306528455477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130687761626304817409214605 49007910609864306528455477)
            ·
              refine ⟨4594491619674778737042701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49007910609864306528455477 4594491619674778737042701)
              ·
                refine ⟨1722934357378042026391013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4594491619674778737042701 1722934357378042026391013)
                ·
                  refine ⟨323050192008382879948315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722934357378042026391013 323050192008382879948315)
                  ·
                    rfl

theorem cell22_2831121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_2831121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831121 prefixEnd_2831121 := by exact prefixLift 2831121
  have htrace : WordTrace (prefixWord ++ tailWord_2831121) baseStart_2831121 baseEnd_2831121 := by
    simpa [prefixWord, tailWord_2831121, baseEnd_2831121] using wordTrace_append hprefix tailTrace_2831121
  have hstable : (prefixWord ++ tailWord_2831121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831121).length < 2 ^ (prefixWord ++ tailWord_2831121).sum := by decide
  have hdescent : baseEnd_2831121 < baseStart_2831121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831136 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_2831136 : Nat := 118140960795 + 2831136 * 2 ^ 59
def prefixEnd_2831136 : Nat := 4983230072969 + 3 ^ 40 * 2831136 * 2
def baseEnd_2831136 : Nat := 969155710831693600719899

theorem tailTrace_2831136 : CollatzResearch.WordTrace tailWord_2831136 prefixEnd_2831136 969155710831693600719899 := by
  unfold tailWord_2831136
  simp only [CollatzResearch.WordTrace]
  refine ⟨51630006535642633189476631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68840008714190177585968841 51630006535642633189476631)
  ·
    refine ⟨77445009803463949784214947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51630006535642633189476631 77445009803463949784214947)
    ·
      refine ⟨116167514705195924676322421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77445009803463949784214947 116167514705195924676322421)
      ·
        refine ⟨10890704503612117938405227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116167514705195924676322421 10890704503612117938405227)
        ·
          refine ⟨16336056755418176907607841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10890704503612117938405227 16336056755418176907607841)
          ·
            refine ⟨12252042566563632680705881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16336056755418176907607841 12252042566563632680705881)
            ·
              refine ⟨9189031924922724510529411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12252042566563632680705881 9189031924922724510529411)
              ·
                refine ⟨13783547887384086765794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9189031924922724510529411 13783547887384086765794117)
                ·
                  refine ⟨2584415228884516268586397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13783547887384086765794117 2584415228884516268586397)
                  ·
                    refine ⟨969155710831693600719899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584415228884516268586397 969155710831693600719899)
                    ·
                      rfl

theorem cell22_2831136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_2831136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831136 prefixEnd_2831136 := by exact prefixLift 2831136
  have htrace : WordTrace (prefixWord ++ tailWord_2831136) baseStart_2831136 baseEnd_2831136 := by
    simpa [prefixWord, tailWord_2831136, baseEnd_2831136] using wordTrace_append hprefix tailTrace_2831136
  have hstable : (prefixWord ++ tailWord_2831136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831136).length < 2 ^ (prefixWord ++ tailWord_2831136).sum := by decide
  have hdescent : baseEnd_2831136 < baseStart_2831136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831196 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2831196 : Nat := 118140960795 + 2831196 * 2 ^ 59
def prefixEnd_2831196 : Nat := 4983230072969 + 3 ^ 40 * 2831196 * 2
def baseEnd_2831196 : Nat := 969176250057873444219715

theorem tailTrace_2831196 : CollatzResearch.WordTrace tailWord_2831196 prefixEnd_2831196 969176250057873444219715 := by
  unfold tailWord_2831196
  simp only [CollatzResearch.WordTrace]
  refine ⟨51631100725533948313068721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68841467634045264417424961 51631100725533948313068721)
  ·
    refine ⟨38723325544150461234801541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51631100725533948313068721 38723325544150461234801541)
    ·
      refine ⟨7260623539528211481525289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38723325544150461234801541 7260623539528211481525289)
      ·
        refine ⟨5445467654646158611143967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7260623539528211481525289 5445467654646158611143967)
        ·
          refine ⟨8168201481969237916715951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445467654646158611143967 8168201481969237916715951)
          ·
            refine ⟨12252302222953856875073927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8168201481969237916715951 12252302222953856875073927)
            ·
              refine ⟨18378453334430785312610891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12252302222953856875073927 18378453334430785312610891)
              ·
                refine ⟨27567680001646177968916337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18378453334430785312610891 27567680001646177968916337)
                ·
                  refine ⟨20675760001234633476687253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27567680001646177968916337 20675760001234633476687253)
                  ·
                    refine ⟨969176250057873444219715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20675760001234633476687253 969176250057873444219715)
                    ·
                      rfl

theorem cell22_2831196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2831196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831196 prefixEnd_2831196 := by exact prefixLift 2831196
  have htrace : WordTrace (prefixWord ++ tailWord_2831196) baseStart_2831196 baseEnd_2831196 := by
    simpa [prefixWord, tailWord_2831196, baseEnd_2831196] using wordTrace_append hprefix tailTrace_2831196
  have hstable : (prefixWord ++ tailWord_2831196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831196).length < 2 ^ (prefixWord ++ tailWord_2831196).sum := by decide
  have hdescent : baseEnd_2831196 < baseStart_2831196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831299 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_2831299 : Nat := 118140960795 + 2831299 * 2 ^ 59
def prefixEnd_2831299 : Nat := 4983230072969 + 3 ^ 40 * 2831299 * 2
def baseEnd_2831299 : Nat := 969211509062815508894399

theorem tailTrace_2831299 : CollatzResearch.WordTrace tailWord_2831299 prefixEnd_2831299 969211509062815508894399 := by
  unfold tailWord_2831299
  simp only [CollatzResearch.WordTrace]
  refine ⟨103265958169694745217136951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68843972113129830144757967 103265958169694745217136951)
  ·
    refine ⟨154898937254542117825705427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103265958169694745217136951 154898937254542117825705427)
    ·
      refine ⟨232348405881813176738558141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154898937254542117825705427 232348405881813176738558141)
      ·
        refine ⟨87130652205679941276959303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232348405881813176738558141 87130652205679941276959303)
        ·
          refine ⟨130695978308519911915438955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87130652205679941276959303 130695978308519911915438955)
          ·
            refine ⟨196043967462779867873158433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130695978308519911915438955 196043967462779867873158433)
            ·
              refine ⟨147032975597084900904868825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196043967462779867873158433 147032975597084900904868825)
              ·
                refine ⟨110274731697813675678651619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147032975597084900904868825 110274731697813675678651619)
                ·
                  refine ⟨165412097546720513517977429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110274731697813675678651619 165412097546720513517977429)
                  ·
                    refine ⟨969211509062815508894399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 165412097546720513517977429 969211509062815508894399)
                    ·
                      rfl

theorem cell22_2831299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_2831299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831299 prefixEnd_2831299 := by exact prefixLift 2831299
  have htrace : WordTrace (prefixWord ++ tailWord_2831299) baseStart_2831299 baseEnd_2831299 := by
    simpa [prefixWord, tailWord_2831299, baseEnd_2831299] using wordTrace_append hprefix tailTrace_2831299
  have hstable : (prefixWord ++ tailWord_2831299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831299).length < 2 ^ (prefixWord ++ tailWord_2831299).sum := by decide
  have hdescent : baseEnd_2831299 < baseStart_2831299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831318 : List Nat := [5, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2831318 : Nat := 118140960795 + 2831318 * 2 ^ 59
def prefixEnd_2831318 : Nat := 4983230072969 + 3 ^ 40 * 2831318 * 2
def baseEnd_2831318 : Nat := 107690890350122865852149

theorem tailTrace_2831318 : CollatzResearch.WordTrace tailWord_2831318 prefixEnd_2831318 107690890350122865852149 := by
  unfold tailWord_2831318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454165697289119466379913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68844434104417274308052405 6454165697289119466379913)
  ·
    refine ⟨4840624272966839599784935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6454165697289119466379913 4840624272966839599784935)
    ·
      refine ⟨7260936409450259399677403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4840624272966839599784935 7260936409450259399677403)
      ·
        refine ⟨10891404614175389099516105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7260936409450259399677403 10891404614175389099516105)
        ·
          refine ⟨8168553460631541824637079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10891404614175389099516105 8168553460631541824637079)
          ·
            refine ⟨12252830190947312736955619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8168553460631541824637079 12252830190947312736955619)
            ·
              refine ⟨18379245286420969105433429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12252830190947312736955619 18379245286420969105433429)
              ·
                refine ⟨107690890350122865852149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18379245286420969105433429 107690890350122865852149)
                ·
                  rfl

theorem cell22_2831318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2831318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831318 prefixEnd_2831318 := by exact prefixLift 2831318
  have htrace : WordTrace (prefixWord ++ tailWord_2831318) baseStart_2831318 baseEnd_2831318 := by
    simpa [prefixWord, tailWord_2831318, baseEnd_2831318] using wordTrace_append hprefix tailTrace_2831318
  have hstable : (prefixWord ++ tailWord_2831318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831318).length < 2 ^ (prefixWord ++ tailWord_2831318).sum := by decide
  have hdescent : baseEnd_2831318 < baseStart_2831318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831322 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_2831322 : Nat := 118140960795 + 2831322 * 2 ^ 59
def prefixEnd_2831322 : Nat := 4983230072969 + 3 ^ 40 * 2831322 * 2
def baseEnd_2831322 : Nat := 969219382432851115569329

theorem tailTrace_2831322 : CollatzResearch.WordTrace tailWord_2831322 prefixEnd_2831322 969219382432851115569329 := by
  unfold tailWord_2831322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25816699262152855036306055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68844531365740946763482813 25816699262152855036306055)
  ·
    refine ⟨38725048893229282554459083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25816699262152855036306055 38725048893229282554459083)
    ·
      refine ⟨58087573339843923831688625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38725048893229282554459083 58087573339843923831688625)
      ·
        refine ⟨43565680004882942873766469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58087573339843923831688625 43565680004882942873766469)
        ·
          refine ⟨8168565000915551788831213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43565680004882942873766469 8168565000915551788831213)
          ·
            refine ⟨3063211875343331920811705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8168565000915551788831213 3063211875343331920811705)
            ·
              refine ⟨2297408906507498940608779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063211875343331920811705 2297408906507498940608779)
              ·
                refine ⟨3446113359761248410913169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297408906507498940608779 3446113359761248410913169)
                ·
                  refine ⟨2584585019820936308184877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3446113359761248410913169 2584585019820936308184877)
                  ·
                    refine ⟨969219382432851115569329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584585019820936308184877 969219382432851115569329)
                    ·
                      rfl

theorem cell22_2831322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_2831322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831322 prefixEnd_2831322 := by exact prefixLift 2831322
  have htrace : WordTrace (prefixWord ++ tailWord_2831322) baseStart_2831322 baseEnd_2831322 := by
    simpa [prefixWord, tailWord_2831322, baseEnd_2831322] using wordTrace_append hprefix tailTrace_2831322
  have hstable : (prefixWord ++ tailWord_2831322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831322).length < 2 ^ (prefixWord ++ tailWord_2831322).sum := by decide
  have hdescent : baseEnd_2831322 < baseStart_2831322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831391 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 8]
def baseStart_2831391 : Nat := 118140960795 + 2831391 * 2 ^ 59
def prefixEnd_2831391 : Nat := 4983230072969 + 3 ^ 40 * 2831391 * 2
def baseEnd_2831391 : Nat := 323081000847652645198039

theorem tailTrace_2831391 : CollatzResearch.WordTrace tailWord_2831391 prefixEnd_2831391 323081000847652645198039 := by
  unfold tailWord_2831391
  simp only [CollatzResearch.WordTrace]
  refine ⟨103269313685361444929486027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68846209123574296619657351 103269313685361444929486027)
  ·
    refine ⟨154903970528042167394229041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103269313685361444929486027 154903970528042167394229041)
    ·
      refine ⟨116177977896031625545671781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154903970528042167394229041 116177977896031625545671781)
      ·
        refine ⟨21783370855505929789813459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116177977896031625545671781 21783370855505929789813459)
        ·
          refine ⟨32675056283258894684720189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21783370855505929789813459 32675056283258894684720189)
          ·
            refine ⟨12253146106222085506770071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32675056283258894684720189 12253146106222085506770071)
            ·
              refine ⟨18379719159333128260155107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12253146106222085506770071 18379719159333128260155107)
              ·
                refine ⟨27569578738999692390232661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18379719159333128260155107 27569578738999692390232661)
                ·
                  refine ⟨323081000847652645198039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27569578738999692390232661 323081000847652645198039)
                  ·
                    rfl

theorem cell22_2831391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_2831391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831391 prefixEnd_2831391 := by exact prefixLift 2831391
  have htrace : WordTrace (prefixWord ++ tailWord_2831391) baseStart_2831391 baseEnd_2831391 := by
    simpa [prefixWord, tailWord_2831391, baseEnd_2831391] using wordTrace_append hprefix tailTrace_2831391
  have hstable : (prefixWord ++ tailWord_2831391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831391).length < 2 ^ (prefixWord ++ tailWord_2831391).sum := by decide
  have hdescent : baseEnd_2831391 < baseStart_2831391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831393 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2831393 : Nat := 118140960795 + 2831393 * 2 ^ 59
def prefixEnd_2831393 : Nat := 4983230072969 + 3 ^ 40 * 2831393 * 2
def baseEnd_2831393 : Nat := 969243687183830597044111

theorem tailTrace_2831393 : CollatzResearch.WordTrace tailWord_2831393 prefixEnd_2831393 969243687183830597044111 := by
  unfold tailWord_2831393
  simp only [CollatzResearch.WordTrace]
  refine ⟨103269386631354199271058833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68846257754236132847372555 103269386631354199271058833)
  ·
    refine ⟨77452039973515649453294125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103269386631354199271058833 77452039973515649453294125)
    ·
      refine ⟨29044514990068368544985297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77452039973515649453294125 29044514990068368544985297)
      ·
        refine ⟨21783386242551276408738973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29044514990068368544985297 21783386242551276408738973)
        ·
          refine ⟨8168769840956728653277115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21783386242551276408738973 8168769840956728653277115)
          ·
            refine ⟨12253154761435092979915673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8168769840956728653277115 12253154761435092979915673)
            ·
              refine ⟨9189866071076319734936755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12253154761435092979915673 9189866071076319734936755)
              ·
                refine ⟨13784799106614479602405133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9189866071076319734936755 13784799106614479602405133)
                ·
                  refine ⟨5169299664980429850901925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13784799106614479602405133 5169299664980429850901925)
                  ·
                    refine ⟨969243687183830597044111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5169299664980429850901925 969243687183830597044111)
                    ·
                      rfl

theorem cell22_2831393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2831393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831393 prefixEnd_2831393 := by exact prefixLift 2831393
  have htrace : WordTrace (prefixWord ++ tailWord_2831393) baseStart_2831393 baseEnd_2831393 := by
    simpa [prefixWord, tailWord_2831393, baseEnd_2831393] using wordTrace_append hprefix tailTrace_2831393
  have hstable : (prefixWord ++ tailWord_2831393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831393).length < 2 ^ (prefixWord ++ tailWord_2831393).sum := by decide
  have hdescent : baseEnd_2831393 < baseStart_2831393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831425 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 6]
def baseStart_2831425 : Nat := 118140960795 + 2831425 * 2 ^ 59
def prefixEnd_2831425 : Nat := 4983230072969 + 3 ^ 40 * 2831425 * 2
def baseEnd_2831425 : Nat := 323084880479264393414671

theorem tailTrace_2831425 : CollatzResearch.WordTrace tailWord_2831425 prefixEnd_2831425 323084880479264393414671 := by
  unfold tailWord_2831425
  simp only [CollatzResearch.WordTrace]
  refine ⟨103270553767238268736223729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68847035844825512490815819 103270553767238268736223729)
  ·
    refine ⟨77452915325428701552167797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103270553767238268736223729 77452915325428701552167797)
    ·
      refine ⟨7261210811758940770515731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77452915325428701552167797 7261210811758940770515731)
      ·
        refine ⟨10891816217638411155773597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7261210811758940770515731 10891816217638411155773597)
        ·
          refine ⟨4084431081614404183415099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10891816217638411155773597 4084431081614404183415099)
          ·
            refine ⟨6126646622421606275122649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084431081614404183415099 6126646622421606275122649)
            ·
              refine ⟨4594984966816204706341987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126646622421606275122649 4594984966816204706341987)
              ·
                refine ⟨6892477450224307059512981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594984966816204706341987 6892477450224307059512981)
                ·
                  refine ⟨323084880479264393414671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6892477450224307059512981 323084880479264393414671)
                  ·
                    rfl

theorem cell22_2831425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_2831425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831425 prefixEnd_2831425 := by exact prefixLift 2831425
  have htrace : WordTrace (prefixWord ++ tailWord_2831425) baseStart_2831425 baseEnd_2831425 := by
    simpa [prefixWord, tailWord_2831425, baseEnd_2831425] using wordTrace_append hprefix tailTrace_2831425
  have hstable : (prefixWord ++ tailWord_2831425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831425).length < 2 ^ (prefixWord ++ tailWord_2831425).sum := by decide
  have hdescent : baseEnd_2831425 < baseStart_2831425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831436 : List Nat := [2, 2, 1, 3, 1, 1, 1, 11]
def baseStart_2831436 : Nat := 118140960795 + 2831436 * 2 ^ 59
def prefixEnd_2831436 : Nat := 4983230072969 + 3 ^ 40 * 2831436 * 2
def baseEnd_2831436 : Nat := 107695378551399202024331

theorem tailTrace_2831436 : CollatzResearch.WordTrace tailWord_2831436 prefixEnd_2831436 107695378551399202024331 := by
  unfold tailWord_2831436
  simp only [CollatzResearch.WordTrace]
  refine ⟨51635477485099208807437081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68847303313465611743249441 51635477485099208807437081)
  ·
    refine ⟨38726608113824406605577811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51635477485099208807437081 38726608113824406605577811)
    ·
      refine ⟨58089912170736609908366717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38726608113824406605577811 58089912170736609908366717)
      ·
        refine ⟨21783717064026228715637519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58089912170736609908366717 21783717064026228715637519)
        ·
          refine ⟨32675575596039343073456279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21783717064026228715637519 32675575596039343073456279)
          ·
            refine ⟨49013363394059014610184419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32675575596039343073456279 49013363394059014610184419)
            ·
              refine ⟨73520045091088521915276629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49013363394059014610184419 73520045091088521915276629)
              ·
                refine ⟨107695378551399202024331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 73520045091088521915276629 107695378551399202024331)
                ·
                  rfl

theorem cell22_2831436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_2831436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831436 prefixEnd_2831436 := by exact prefixLift 2831436
  have htrace : WordTrace (prefixWord ++ tailWord_2831436) baseStart_2831436 baseEnd_2831436 := by
    simpa [prefixWord, tailWord_2831436, baseEnd_2831436] using wordTrace_append hprefix tailTrace_2831436
  have hstable : (prefixWord ++ tailWord_2831436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831436).length < 2 ^ (prefixWord ++ tailWord_2831436).sum := by decide
  have hdescent : baseEnd_2831436 < baseStart_2831436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831543 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 6]
def baseStart_2831543 : Nat := 118140960795 + 2831543 * 2 ^ 59
def prefixEnd_2831543 : Nat := 4983230072969 + 3 ^ 40 * 2831543 * 2
def baseEnd_2831543 : Nat := 323098345083093401931217

theorem tailTrace_2831543 : CollatzResearch.WordTrace tailWord_2831543 prefixEnd_2831543 323098345083093401931217 := by
  unfold tailWord_2831543
  simp only [CollatzResearch.WordTrace]
  refine ⟨103274857580810774889019283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68849905053873849926012855 103274857580810774889019283)
  ·
    refine ⟨154912286371216162333528925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103274857580810774889019283 154912286371216162333528925)
    ·
      refine ⟨58092107389206060875073347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154912286371216162333528925 58092107389206060875073347)
      ·
        refine ⟨87138161083809091312610021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58092107389206060875073347 87138161083809091312610021)
        ·
          refine ⟨16338405203214204621114379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87138161083809091312610021 16338405203214204621114379)
          ·
            refine ⟨24507607804821306931671569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16338405203214204621114379 24507607804821306931671569)
            ·
              refine ⟨18380705853615980198753677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24507607804821306931671569 18380705853615980198753677)
              ·
                refine ⟨6892764695105992574532629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18380705853615980198753677 6892764695105992574532629)
                ·
                  refine ⟨323098345083093401931217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6892764695105992574532629 323098345083093401931217)
                  ·
                    rfl

theorem cell22_2831543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 6].length) (baseStart_2831543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831543 prefixEnd_2831543 := by exact prefixLift 2831543
  have htrace : WordTrace (prefixWord ++ tailWord_2831543) baseStart_2831543 baseEnd_2831543 := by
    simpa [prefixWord, tailWord_2831543, baseEnd_2831543] using wordTrace_append hprefix tailTrace_2831543
  have hstable : (prefixWord ++ tailWord_2831543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831543).length < 2 ^ (prefixWord ++ tailWord_2831543).sum := by decide
  have hdescent : baseEnd_2831543 < baseStart_2831543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831633 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 9]
def baseStart_2831633 : Nat := 118140960795 + 2831633 * 2 ^ 59
def prefixEnd_2831633 : Nat := 4983230072969 + 3 ^ 40 * 2831633 * 2
def baseEnd_2831633 : Nat := 323108614696183323681125

theorem tailTrace_2831633 : CollatzResearch.WordTrace tailWord_2831633 prefixEnd_2831633 323108614696183323681125 := by
  unfold tailWord_2831633
  simp only [CollatzResearch.WordTrace]
  refine ⟨103278140150484720259795553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68852093433656480173197035 103278140150484720259795553)
  ·
    refine ⟨77458605112863540194846665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103278140150484720259795553 77458605112863540194846665)
    ·
      refine ⟨58093953834647655146134999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77458605112863540194846665 58093953834647655146134999)
      ·
        refine ⟨87140930751971482719202499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58093953834647655146134999 87140930751971482719202499)
        ·
          refine ⟨130711396127957224078803749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87140930751971482719202499 130711396127957224078803749)
          ·
            refine ⟨24508386773991979514775703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130711396127957224078803749 24508386773991979514775703)
            ·
              refine ⟨36762580160987969272163555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24508386773991979514775703 36762580160987969272163555)
              ·
                refine ⟨55143870241481953908245333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36762580160987969272163555 55143870241481953908245333)
                ·
                  refine ⟨323108614696183323681125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55143870241481953908245333 323108614696183323681125)
                  ·
                    rfl

theorem cell22_2831633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_2831633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831633 prefixEnd_2831633 := by exact prefixLift 2831633
  have htrace : WordTrace (prefixWord ++ tailWord_2831633) baseStart_2831633 baseEnd_2831633 := by
    simpa [prefixWord, tailWord_2831633, baseEnd_2831633] using wordTrace_append hprefix tailTrace_2831633
  have hstable : (prefixWord ++ tailWord_2831633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831633).length < 2 ^ (prefixWord ++ tailWord_2831633).sum := by decide
  have hdescent : baseEnd_2831633 < baseStart_2831633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831663 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_2831663 : Nat := 118140960795 + 2831663 * 2 ^ 59
def prefixEnd_2831663 : Nat := 4983230072969 + 3 ^ 40 * 2831663 * 2
def baseEnd_2831663 : Nat := 969336113701639892793283

theorem tailTrace_2831663 : CollatzResearch.WordTrace tailWord_2831663 prefixEnd_2831663 969336113701639892793283 := by
  unfold tailWord_2831663
  simp only [CollatzResearch.WordTrace]
  refine ⟨103279234340376035383387643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68852822893584023588925095 103279234340376035383387643)
  ·
    refine ⟨154918851510564053075081465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103279234340376035383387643 154918851510564053075081465)
    ·
      refine ⟨116189138632923039806311099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154918851510564053075081465 116189138632923039806311099)
      ·
        refine ⟨174283707949384559709466649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116189138632923039806311099 174283707949384559709466649)
        ·
          refine ⟨130712780962038419782099987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174283707949384559709466649 130712780962038419782099987)
          ·
            refine ⟨196069171443057629673149981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130712780962038419782099987 196069171443057629673149981)
            ·
              refine ⟨73525939291146611127431243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196069171443057629673149981 73525939291146611127431243)
              ·
                refine ⟨110288908936719916691146865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73525939291146611127431243 110288908936719916691146865)
                ·
                  refine ⟨82716681702539937518360149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110288908936719916691146865 82716681702539937518360149)
                  ·
                    refine ⟨969336113701639892793283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82716681702539937518360149 969336113701639892793283)
                    ·
                      rfl

theorem cell22_2831663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_2831663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831663 prefixEnd_2831663 := by exact prefixLift 2831663
  have htrace : WordTrace (prefixWord ++ tailWord_2831663) baseStart_2831663 baseEnd_2831663 := by
    simpa [prefixWord, tailWord_2831663, baseEnd_2831663] using wordTrace_append hprefix tailTrace_2831663
  have hstable : (prefixWord ++ tailWord_2831663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831663).length < 2 ^ (prefixWord ++ tailWord_2831663).sum := by decide
  have hdescent : baseEnd_2831663 < baseStart_2831663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831667 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 5]
def baseStart_2831667 : Nat := 118140960795 + 2831667 * 2 ^ 59
def prefixEnd_2831667 : Nat := 4983230072969 + 3 ^ 40 * 2831667 * 2
def baseEnd_2831667 : Nat := 323112494327795071897757

theorem tailTrace_2831667 : CollatzResearch.WordTrace tailWord_2831667 prefixEnd_2831667 323112494327795071897757 := by
  unfold tailWord_2831667
  simp only [CollatzResearch.WordTrace]
  refine ⟨103279380232361544066533255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68852920154907696044355503 103279380232361544066533255)
  ·
    refine ⟨154919070348542316099799883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103279380232361544066533255 154919070348542316099799883)
    ·
      refine ⟨232378605522813474149699825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154919070348542316099799883 232378605522813474149699825)
      ·
        refine ⟨174283954142110105612274869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232378605522813474149699825 174283954142110105612274869)
        ·
          refine ⟨16339120700822822401150769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174283954142110105612274869 16339120700822822401150769)
          ·
            refine ⟨12254340525617116800863077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16339120700822822401150769 12254340525617116800863077)
            ·
              refine ⟨2297688848553209400161827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12254340525617116800863077 2297688848553209400161827)
              ·
                refine ⟨3446533272829814100242741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297688848553209400161827 3446533272829814100242741)
                ·
                  refine ⟨323112494327795071897757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3446533272829814100242741 323112494327795071897757)
                  ·
                    rfl

theorem cell22_2831667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 5].length) (baseStart_2831667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831667 prefixEnd_2831667 := by exact prefixLift 2831667
  have htrace : WordTrace (prefixWord ++ tailWord_2831667) baseStart_2831667 baseEnd_2831667 := by
    simpa [prefixWord, tailWord_2831667, baseEnd_2831667] using wordTrace_append hprefix tailTrace_2831667
  have hstable : (prefixWord ++ tailWord_2831667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831667).length < 2 ^ (prefixWord ++ tailWord_2831667).sum := by decide
  have hdescent : baseEnd_2831667 < baseStart_2831667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831680 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_2831680 : Nat := 118140960795 + 2831680 * 2 ^ 59
def prefixEnd_2831680 : Nat := 4983230072969 + 3 ^ 40 * 2831680 * 2
def baseEnd_2831680 : Nat := 969341933149057515118231

theorem tailTrace_2831680 : CollatzResearch.WordTrace tailWord_2831680 prefixEnd_2831680 969341933149057515118231 := by
  unfold tailWord_2831680
  simp only [CollatzResearch.WordTrace]
  refine ⟨51639927190657223643378247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68853236254209631524504329 51639927190657223643378247)
  ·
    refine ⟨77459890785985835465067371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51639927190657223643378247 77459890785985835465067371)
    ·
      refine ⟨116189836178978753197601057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77459890785985835465067371 116189836178978753197601057)
      ·
        refine ⟨87142377134234064898200793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116189836178978753197601057 87142377134234064898200793)
        ·
          refine ⟨65356782850675548673650595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87142377134234064898200793 65356782850675548673650595)
          ·
            refine ⟨98035174276013323010475893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65356782850675548673650595 98035174276013323010475893)
            ·
              refine ⟨9190797588376249032232115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98035174276013323010475893 9190797588376249032232115)
              ·
                refine ⟨13786196382564373548348173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9190797588376249032232115 13786196382564373548348173)
                ·
                  refine ⟨5169823643461640080630565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13786196382564373548348173 5169823643461640080630565)
                  ·
                    refine ⟨969341933149057515118231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5169823643461640080630565 969341933149057515118231)
                    ·
                      rfl

theorem cell22_2831680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_2831680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831680 prefixEnd_2831680 := by exact prefixLift 2831680
  have htrace : WordTrace (prefixWord ++ tailWord_2831680) baseStart_2831680 baseEnd_2831680 := by
    simpa [prefixWord, tailWord_2831680, baseEnd_2831680] using wordTrace_append hprefix tailTrace_2831680
  have hstable : (prefixWord ++ tailWord_2831680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831680).length < 2 ^ (prefixWord ++ tailWord_2831680).sum := by decide
  have hdescent : baseEnd_2831680 < baseStart_2831680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831727 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 2, 3]
def baseStart_2831727 : Nat := 118140960795 + 2831727 * 2 ^ 59
def prefixEnd_2831727 : Nat := 4983230072969 + 3 ^ 40 * 2831727 * 2
def baseEnd_2831727 : Nat := 969358022209565059193087

theorem tailTrace_2831727 : CollatzResearch.WordTrace tailWord_2831727 prefixEnd_2831727 969358022209565059193087 := by
  unfold tailWord_2831727
  simp only [CollatzResearch.WordTrace]
  refine ⟨103281568612144174313717435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68854379074762782875811623 103281568612144174313717435)
  ·
    refine ⟨154922352918216261470576153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103281568612144174313717435 154922352918216261470576153)
    ·
      refine ⟨116191764688662196102932115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154922352918216261470576153 116191764688662196102932115)
      ·
        refine ⟨174287647032993294154398173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116191764688662196102932115 174287647032993294154398173)
        ·
          refine ⟨65357867637372485307899315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174287647032993294154398173 65357867637372485307899315)
          ·
            refine ⟨98036801456058727961848973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65357867637372485307899315 98036801456058727961848973)
            ·
              refine ⟨36763800546022022985693365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98036801456058727961848973 36763800546022022985693365)
              ·
                refine ⟨3446606301189564654908753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36763800546022022985693365 3446606301189564654908753)
                ·
                  refine ⟨2584954725892173491181565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3446606301189564654908753 2584954725892173491181565)
                  ·
                    refine ⟨969358022209565059193087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584954725892173491181565 969358022209565059193087)
                    ·
                      rfl

theorem cell22_2831727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_2831727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831727 prefixEnd_2831727 := by exact prefixLift 2831727
  have htrace : WordTrace (prefixWord ++ tailWord_2831727) baseStart_2831727 baseEnd_2831727 := by
    simpa [prefixWord, tailWord_2831727, baseEnd_2831727] using wordTrace_append hprefix tailTrace_2831727
  have hstable : (prefixWord ++ tailWord_2831727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831727).length < 2 ^ (prefixWord ++ tailWord_2831727).sum := by decide
  have hdescent : baseEnd_2831727 < baseStart_2831727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831746 : List Nat := [3, 4, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2831746 : Nat := 118140960795 + 2831746 * 2 ^ 59
def prefixEnd_2831746 : Nat := 4983230072969 + 3 ^ 40 * 2831746 * 2
def baseEnd_2831746 : Nat := 323121508765951780989343

theorem tailTrace_2831746 : CollatzResearch.WordTrace tailWord_2831746 prefixEnd_2831746 323121508765951780989343 := by
  unfold tailWord_2831746
  simp only [CollatzResearch.WordTrace]
  refine ⟨25820565399768835139664773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68854841066050227039106061 25820565399768835139664773)
  ·
    refine ⟨4841356012456656588687145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25820565399768835139664773 4841356012456656588687145)
    ·
      refine ⟨3631017009342492441515359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4841356012456656588687145 3631017009342492441515359)
      ·
        refine ⟨5446525514013738662273039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631017009342492441515359 5446525514013738662273039)
        ·
          refine ⟨8169788271020607993409559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5446525514013738662273039 8169788271020607993409559)
          ·
            refine ⟨12254682406530911990114339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8169788271020607993409559 12254682406530911990114339)
            ·
              refine ⟨18382023609796367985171509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12254682406530911990114339 18382023609796367985171509)
              ·
                refine ⟨1723314713418409498609829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18382023609796367985171509 1723314713418409498609829)
                ·
                  refine ⟨323121508765951780989343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1723314713418409498609829 323121508765951780989343)
                  ·
                    rfl

theorem cell22_2831746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2831746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831746 prefixEnd_2831746 := by exact prefixLift 2831746
  have htrace : WordTrace (prefixWord ++ tailWord_2831746) baseStart_2831746 baseEnd_2831746 := by
    simpa [prefixWord, tailWord_2831746, baseEnd_2831746] using wordTrace_append hprefix tailTrace_2831746
  have hstable : (prefixWord ++ tailWord_2831746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831746).length < 2 ^ (prefixWord ++ tailWord_2831746).sum := by decide
  have hdescent : baseEnd_2831746 < baseStart_2831746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831800 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_2831800 : Nat := 118140960795 + 2831800 * 2 ^ 59
def prefixEnd_2831800 : Nat := 4983230072969 + 3 ^ 40 * 2831800 * 2
def baseEnd_2831800 : Nat := 969383011601417202117863

theorem tailTrace_2831800 : CollatzResearch.WordTrace tailWord_2831800 prefixEnd_2831800 969383011601417202117863 := by
  unfold tailWord_2831800
  simp only [CollatzResearch.WordTrace]
  refine ⟨51642115570439853890562427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68856154093919805187416569 51642115570439853890562427)
  ·
    refine ⟨77463173355659780835843641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51642115570439853890562427 77463173355659780835843641)
    ·
      refine ⟨58097380016744835626882731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77463173355659780835843641 58097380016744835626882731)
      ·
        refine ⟨87146070025117253440324097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58097380016744835626882731 87146070025117253440324097)
        ·
          refine ⟨65359552518837940080243073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87146070025117253440324097 65359552518837940080243073)
          ·
            refine ⟨49019664389128455060182305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65359552518837940080243073 49019664389128455060182305)
            ·
              refine ⟨36764748291846341295136729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49019664389128455060182305 36764748291846341295136729)
              ·
                refine ⟨27573561218884755971352547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36764748291846341295136729 27573561218884755971352547)
                ·
                  refine ⟨41360341828327133957028821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27573561218884755971352547 41360341828327133957028821)
                  ·
                    refine ⟨969383011601417202117863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41360341828327133957028821 969383011601417202117863)
                    ·
                      rfl

theorem cell22_2831800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_2831800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831800 prefixEnd_2831800 := by exact prefixLift 2831800
  have htrace : WordTrace (prefixWord ++ tailWord_2831800) baseStart_2831800 baseEnd_2831800 := by
    simpa [prefixWord, tailWord_2831800, baseEnd_2831800] using wordTrace_append hprefix tailTrace_2831800
  have hstable : (prefixWord ++ tailWord_2831800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831800).length < 2 ^ (prefixWord ++ tailWord_2831800).sum := by decide
  have hdescent : baseEnd_2831800 < baseStart_2831800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831810 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2831810 : Nat := 118140960795 + 2831810 * 2 ^ 59
def prefixEnd_2831810 : Nat := 4983230072969 + 3 ^ 40 * 2831810 * 2
def baseEnd_2831810 : Nat := 969386434805780509367833

theorem tailTrace_2831810 : CollatzResearch.WordTrace tailWord_2831810 prefixEnd_2831810 969386434805780509367833 := by
  unfold tailWord_2831810
  simp only [CollatzResearch.WordTrace]
  refine ⟨25821148967710869872247221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68856397247228986325992589 25821148967710869872247221)
  ·
    refine ⟨2420732715722894050523177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25821148967710869872247221 2420732715722894050523177)
    ·
      refine ⟨1815549536792170537892383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2420732715722894050523177 1815549536792170537892383)
      ·
        refine ⟨2723324305188255806838575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1815549536792170537892383 2723324305188255806838575)
        ·
          refine ⟨4084986457782383710257863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723324305188255806838575 4084986457782383710257863)
          ·
            refine ⟨6127479686673575565386795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084986457782383710257863 6127479686673575565386795)
            ·
              refine ⟨9191219530010363348080193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6127479686673575565386795 9191219530010363348080193)
              ·
                refine ⟨6893414647507772511060145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9191219530010363348080193 6893414647507772511060145)
                ·
                  refine ⟨5170060985630829383295109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6893414647507772511060145 5170060985630829383295109)
                  ·
                    refine ⟨969386434805780509367833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170060985630829383295109 969386434805780509367833)
                    ·
                      rfl

theorem cell22_2831810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2831810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831810 prefixEnd_2831810 := by exact prefixLift 2831810
  have htrace : WordTrace (prefixWord ++ tailWord_2831810) baseStart_2831810 baseEnd_2831810 := by
    simpa [prefixWord, tailWord_2831810, baseEnd_2831810] using wordTrace_append hprefix tailTrace_2831810
  have hstable : (prefixWord ++ tailWord_2831810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831810).length < 2 ^ (prefixWord ++ tailWord_2831810).sum := by decide
  have hdescent : baseEnd_2831810 < baseStart_2831810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831941 : List Nat := [1, 3, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_2831941 : Nat := 118140960795 + 2831941 * 2 ^ 59
def prefixEnd_2831941 : Nat := 4983230072969 + 3 ^ 40 * 2831941 * 2
def baseEnd_2831941 : Nat := 969431278782939834342431

theorem tailTrace_2831941 : CollatzResearch.WordTrace tailWord_2831941 prefixEnd_2831941 969431278782939834342431 := by
  unfold tailWord_2831941
  simp only [CollatzResearch.WordTrace]
  refine ⟨103289373833368888862007677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68859582555579259241338451 103289373833368888862007677)
  ·
    refine ⟨38733515187513333323252879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103289373833368888862007677 38733515187513333323252879)
    ·
      refine ⟨58100272781269999984879319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38733515187513333323252879 58100272781269999984879319)
      ·
        refine ⟨87150409171904999977318979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58100272781269999984879319 87150409171904999977318979)
        ·
          refine ⟨130725613757857499965978469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87150409171904999977318979 130725613757857499965978469)
          ·
            refine ⟨24511052579598281243620963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130725613757857499965978469 24511052579598281243620963)
            ·
              refine ⟨36766578869397421865431445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24511052579598281243620963 36766578869397421865431445)
              ·
                refine ⟨1723433384503004149942099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36766578869397421865431445 1723433384503004149942099)
                ·
                  refine ⟨2585150076754506224913149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1723433384503004149942099 2585150076754506224913149)
                  ·
                    refine ⟨969431278782939834342431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2585150076754506224913149 969431278782939834342431)
                    ·
                      rfl

theorem cell22_2831941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_2831941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831941 prefixEnd_2831941 := by exact prefixLift 2831941
  have htrace : WordTrace (prefixWord ++ tailWord_2831941) baseStart_2831941 baseEnd_2831941 := by
    simpa [prefixWord, tailWord_2831941, baseEnd_2831941] using wordTrace_append hprefix tailTrace_2831941
  have hstable : (prefixWord ++ tailWord_2831941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831941).length < 2 ^ (prefixWord ++ tailWord_2831941).sum := by decide
  have hdescent : baseEnd_2831941 < baseStart_2831941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2831952 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_2831952 : Nat := 118140960795 + 2831952 * 2 ^ 59
def prefixEnd_2831952 : Nat := 4983230072969 + 3 ^ 40 * 2831952 * 2
def baseEnd_2831952 : Nat := 969435044307739472317397

theorem tailTrace_2831952 : CollatzResearch.WordTrace tailWord_2831952 prefixEnd_2831952 969435044307739472317397 := by
  unfold tailWord_2831952
  simp only [CollatzResearch.WordTrace]
  refine ⟨51644887518164518870329055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68859850024219358493772073 51644887518164518870329055)
  ·
    refine ⟨77467331277246778305493583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51644887518164518870329055 77467331277246778305493583)
    ·
      refine ⟨116200996915870167458240375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77467331277246778305493583 116200996915870167458240375)
      ·
        refine ⟨174301495373805251187360563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116200996915870167458240375 174301495373805251187360563)
        ·
          refine ⟨261452243060707876781040845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174301495373805251187360563 261452243060707876781040845)
          ·
            refine ⟨98044591147765453792890317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261452243060707876781040845 98044591147765453792890317)
            ·
              refine ⟨36766721680412045172333869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98044591147765453792890317 36766721680412045172333869)
              ·
                refine ⟨13787520630154516939625201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36766721680412045172333869 13787520630154516939625201)
                ·
                  refine ⟨10340640472615887704718901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13787520630154516939625201 10340640472615887704718901)
                  ·
                    refine ⟨969435044307739472317397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10340640472615887704718901 969435044307739472317397)
                    ·
                      rfl

theorem cell22_2831952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_2831952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2831952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2831952 prefixEnd_2831952 := by exact prefixLift 2831952
  have htrace : WordTrace (prefixWord ++ tailWord_2831952) baseStart_2831952 baseEnd_2831952 := by
    simpa [prefixWord, tailWord_2831952, baseEnd_2831952] using wordTrace_append hprefix tailTrace_2831952
  have hstable : (prefixWord ++ tailWord_2831952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2831952).length < 2 ^ (prefixWord ++ tailWord_2831952).sum := by decide
  have hdescent : baseEnd_2831952 < baseStart_2831952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2831952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832059 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 7, 3]
def baseStart_2832059 : Nat := 118140960795 + 2832059 * 2 ^ 59
def prefixEnd_2832059 : Nat := 4983230072969 + 3 ^ 40 * 2832059 * 2
def baseEnd_2832059 : Nat := 969471672594426859892069

theorem tailTrace_2832059 : CollatzResearch.WordTrace tailWord_2832059 prefixEnd_2832059 969471672594426859892069 := by
  unfold tailWord_2832059
  simp only [CollatzResearch.WordTrace]
  refine ⟨103293677646941395014803231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68862451764627596676535487 103293677646941395014803231)
  ·
    refine ⟨154940516470412092522204847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103293677646941395014803231 154940516470412092522204847)
    ·
      refine ⟨232410774705618138783307271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154940516470412092522204847 232410774705618138783307271)
      ·
        refine ⟨348616162058427208174960907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232410774705618138783307271 348616162058427208174960907)
        ·
          refine ⟨522924243087640812262441361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348616162058427208174960907 522924243087640812262441361)
          ·
            refine ⟨392193182315730609196831021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522924243087640812262441361 392193182315730609196831021)
            ·
              refine ⟨147072443368398978448811633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392193182315730609196831021 147072443368398978448811633)
              ·
                refine ⟨110304332526299233836608725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147072443368398978448811633 110304332526299233836608725)
                ·
                  refine ⟨2585257793585138293045517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110304332526299233836608725 2585257793585138293045517)
                  ·
                    refine ⟨969471672594426859892069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2585257793585138293045517 969471672594426859892069)
                    ·
                      rfl

theorem cell22_2832059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 3].length) (baseStart_2832059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832059 prefixEnd_2832059 := by exact prefixLift 2832059
  have htrace : WordTrace (prefixWord ++ tailWord_2832059) baseStart_2832059 baseEnd_2832059 := by
    simpa [prefixWord, tailWord_2832059, baseEnd_2832059] using wordTrace_append hprefix tailTrace_2832059
  have hstable : (prefixWord ++ tailWord_2832059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832059).length < 2 ^ (prefixWord ++ tailWord_2832059).sum := by decide
  have hdescent : baseEnd_2832059 < baseStart_2832059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832106 : List Nat := [3, 1, 3, 1, 1, 1, 5, 2, 5]
def baseStart_2832106 : Nat := 118140960795 + 2832106 * 2 ^ 59
def prefixEnd_2832106 : Nat := 4983230072969 + 3 ^ 40 * 2832106 * 2
def baseEnd_2832106 : Nat := 323162587218311467988975

theorem tailTrace_2832106 : CollatzResearch.WordTrace tailWord_2832106 prefixEnd_2832106 323162587218311467988975 := by
  unfold tailWord_2832106
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823847969442780510441043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68863594585180748027842781 25823847969442780510441043)
  ·
    refine ⟨38735771954164170765661565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25823847969442780510441043 38735771954164170765661565)
    ·
      refine ⟨14525914482811564037123087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38735771954164170765661565 14525914482811564037123087)
      ·
        refine ⟨21788871724217346055684631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14525914482811564037123087 21788871724217346055684631)
        ·
          refine ⟨32683307586326019083526947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21788871724217346055684631 32683307586326019083526947)
          ·
            refine ⟨49024961379489028625290421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32683307586326019083526947 49024961379489028625290421)
            ·
              refine ⟨4596090129327096433620977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49024961379489028625290421 4596090129327096433620977)
              ·
                refine ⟨3447067596995322325215733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4596090129327096433620977 3447067596995322325215733)
                ·
                  refine ⟨323162587218311467988975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3447067596995322325215733 323162587218311467988975)
                  ·
                    rfl

theorem cell22_2832106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_2832106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832106 prefixEnd_2832106 := by exact prefixLift 2832106
  have htrace : WordTrace (prefixWord ++ tailWord_2832106) baseStart_2832106 baseEnd_2832106 := by
    simpa [prefixWord, tailWord_2832106, baseEnd_2832106] using wordTrace_append hprefix tailTrace_2832106
  have hstable : (prefixWord ++ tailWord_2832106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832106).length < 2 ^ (prefixWord ++ tailWord_2832106).sum := by decide
  have hdescent : baseEnd_2832106 < baseStart_2832106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832119 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 5, 4]
def baseStart_2832119 : Nat := 118140960795 + 2832119 * 2 ^ 59
def prefixEnd_2832119 : Nat := 4983230072969 + 3 ^ 40 * 2832119 * 2
def baseEnd_2832119 : Nat := 969492211820606703391885

theorem tailTrace_2832119 : CollatzResearch.WordTrace tailWord_2832119 prefixEnd_2832119 969492211820606703391885 := by
  unfold tailWord_2832119
  simp only [CollatzResearch.WordTrace]
  refine ⟨103295866026724025261987411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68863910684482683507991607 103295866026724025261987411)
  ·
    refine ⟨154943799040086037892981117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103295866026724025261987411 154943799040086037892981117)
    ·
      refine ⟨58103924640032264209867919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154943799040086037892981117 58103924640032264209867919)
      ·
        refine ⟨87155886960048396314801879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58103924640032264209867919 87155886960048396314801879)
        ·
          refine ⟨130733830440072594472202819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87155886960048396314801879 130733830440072594472202819)
          ·
            refine ⟨196100745660108891708304229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130733830440072594472202819 196100745660108891708304229)
            ·
              refine ⟨36768889811270417195307043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196100745660108891708304229 36768889811270417195307043)
              ·
                refine ⟨55153334716905625792960565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36768889811270417195307043 55153334716905625792960565)
                ·
                  refine ⟨5170625129709902418090053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55153334716905625792960565 5170625129709902418090053)
                  ·
                    refine ⟨969492211820606703391885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170625129709902418090053 969492211820606703391885)
                    ·
                      rfl

theorem cell22_2832119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_2832119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832119 prefixEnd_2832119 := by exact prefixLift 2832119
  have htrace : WordTrace (prefixWord ++ tailWord_2832119) baseStart_2832119 baseEnd_2832119 := by
    simpa [prefixWord, tailWord_2832119, baseEnd_2832119] using wordTrace_append hprefix tailTrace_2832119
  have hstable : (prefixWord ++ tailWord_2832119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832119).length < 2 ^ (prefixWord ++ tailWord_2832119).sum := by decide
  have hdescent : baseEnd_2832119 < baseStart_2832119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832168 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 6]
def baseStart_2832168 : Nat := 118140960795 + 2832168 * 2 ^ 59
def prefixEnd_2832168 : Nat := 4983230072969 + 3 ^ 40 * 2832168 * 2
def baseEnd_2832168 : Nat := 323169661840662302972245

theorem tailTrace_2832168 : CollatzResearch.WordTrace tailWord_2832168 prefixEnd_2832168 323169661840662302972245 := by
  unfold tailWord_2832168
  simp only [CollatzResearch.WordTrace]
  refine ⟨51648826601773253315260579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68865102135697671087014105 51648826601773253315260579)
  ·
    refine ⟨77473239902659879972890869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51648826601773253315260579 77473239902659879972890869)
    ·
      refine ⟨7263116240874363747458519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77473239902659879972890869 7263116240874363747458519)
      ·
        refine ⟨10894674361311545621187779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263116240874363747458519 10894674361311545621187779)
        ·
          refine ⟨16342011541967318431781669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10894674361311545621187779 16342011541967318431781669)
          ·
            refine ⟨3064127164118872205959063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16342011541967318431781669 3064127164118872205959063)
            ·
              refine ⟨4596190746178308308938595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3064127164118872205959063 4596190746178308308938595)
              ·
                refine ⟨6894286119267462463407893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596190746178308308938595 6894286119267462463407893)
                ·
                  refine ⟨323169661840662302972245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6894286119267462463407893 323169661840662302972245)
                  ·
                    rfl

theorem cell22_2832168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_2832168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832168 prefixEnd_2832168 := by exact prefixLift 2832168
  have htrace : WordTrace (prefixWord ++ tailWord_2832168) baseStart_2832168 baseEnd_2832168 := by
    simpa [prefixWord, tailWord_2832168, baseEnd_2832168] using wordTrace_append hprefix tailTrace_2832168
  have hstable : (prefixWord ++ tailWord_2832168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832168).length < 2 ^ (prefixWord ++ tailWord_2832168).sum := by decide
  have hdescent : baseEnd_2832168 < baseStart_2832168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832241 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 5]
def baseStart_2832241 : Nat := 118140960795 + 2832241 * 2 ^ 59
def prefixEnd_2832241 : Nat := 4983230072969 + 3 ^ 40 * 2832241 * 2
def baseEnd_2832241 : Nat := 323177991637946350613837

theorem tailTrace_2832241 : CollatzResearch.WordTrace tailWord_2832241 prefixEnd_2832241 323177991637946350613837 := by
  unfold tailWord_2832241
  simp only [CollatzResearch.WordTrace]
  refine ⟨103300315732282040097928577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68866877154854693398619051 103300315732282040097928577)
  ·
    refine ⟨77475236799211530073446433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103300315732282040097928577 77475236799211530073446433)
    ·
      refine ⟨58106427599408647555084825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77475236799211530073446433 58106427599408647555084825)
      ·
        refine ⟨43579820699556485666313619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58106427599408647555084825 43579820699556485666313619)
        ·
          refine ⟨65369731049334728499470429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43579820699556485666313619 65369731049334728499470429)
          ·
            refine ⟨24513649143500523187301411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65369731049334728499470429 24513649143500523187301411)
            ·
              refine ⟨36770473715250784780952117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24513649143500523187301411 36770473715250784780952117)
              ·
                refine ⟨3447231910804761073214261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36770473715250784780952117 3447231910804761073214261)
                ·
                  refine ⟨323177991637946350613837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3447231910804761073214261 323177991637946350613837)
                  ·
                    rfl

theorem cell22_2832241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_2832241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832241 prefixEnd_2832241 := by exact prefixLift 2832241
  have htrace : WordTrace (prefixWord ++ tailWord_2832241) baseStart_2832241 baseEnd_2832241 := by
    simpa [prefixWord, tailWord_2832241, baseEnd_2832241] using wordTrace_append hprefix tailTrace_2832241
  have hstable : (prefixWord ++ tailWord_2832241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832241).length < 2 ^ (prefixWord ++ tailWord_2832241).sum := by decide
  have hdescent : baseEnd_2832241 < baseStart_2832241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832305 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_2832305 : Nat := 118140960795 + 2832305 * 2 ^ 59
def prefixEnd_2832305 : Nat := 4983230072969 + 3 ^ 40 * 2832305 * 2
def baseEnd_2832305 : Nat := 969555883421764218241315

theorem tailTrace_2832305 : CollatzResearch.WordTrace tailWord_2832305 prefixEnd_2832305 969555883421764218241315 := by
  unfold tailWord_2832305
  simp only [CollatzResearch.WordTrace]
  refine ⟨103302650004050179028258369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68868433336033452685505579 103302650004050179028258369)
  ·
    refine ⟨77476987503037634271193777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103302650004050179028258369 77476987503037634271193777)
    ·
      refine ⟨58107740627278225703395333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77476987503037634271193777 58107740627278225703395333)
      ·
        refine ⟨10895201367614667319386625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58107740627278225703395333 10895201367614667319386625)
        ·
          refine ⟨8171401025711000489539969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10895201367614667319386625 8171401025711000489539969)
          ·
            refine ⟨6128550769283250367154977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8171401025711000489539969 6128550769283250367154977)
            ·
              refine ⟨4596413076962437775366233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6128550769283250367154977 4596413076962437775366233)
              ·
                refine ⟨3447309807721828331524675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4596413076962437775366233 3447309807721828331524675)
                ·
                  refine ⟨5170964711582742497287013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447309807721828331524675 5170964711582742497287013)
                  ·
                    refine ⟨969555883421764218241315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5170964711582742497287013 969555883421764218241315)
                    ·
                      rfl

theorem cell22_2832305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_2832305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832305 prefixEnd_2832305 := by exact prefixLift 2832305
  have htrace : WordTrace (prefixWord ++ tailWord_2832305) baseStart_2832305 baseEnd_2832305 := by
    simpa [prefixWord, tailWord_2832305, baseEnd_2832305] using wordTrace_append hprefix tailTrace_2832305
  have hstable : (prefixWord ++ tailWord_2832305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832305).length < 2 ^ (prefixWord ++ tailWord_2832305).sum := by decide
  have hdescent : baseEnd_2832305 < baseStart_2832305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832363 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 3, 3]
def baseStart_2832363 : Nat := 118140960795 + 2832363 * 2 ^ 59
def prefixEnd_2832363 : Nat := 4983230072969 + 3 ^ 40 * 2832363 * 2
def baseEnd_2832363 : Nat := 969575738007071400291137

theorem tailTrace_2832363 : CollatzResearch.WordTrace tailWord_2832363 prefixEnd_2832363 969575738007071400291137 := by
  unfold tailWord_2832363
  simp only [CollatzResearch.WordTrace]
  refine ⟨103304765437840054933869743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68869843625226703289246495 103304765437840054933869743)
  ·
    refine ⟨154957148156760082400804615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103304765437840054933869743 154957148156760082400804615)
    ·
      refine ⟨232435722235140123601206923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154957148156760082400804615 232435722235140123601206923)
      ·
        refine ⟨348653583352710185401810385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232435722235140123601206923 348653583352710185401810385)
        ·
          refine ⟨261490187514532639051357789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348653583352710185401810385 261490187514532639051357789)
          ·
            refine ⟨98058820317949739644259171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261490187514532639051357789 98058820317949739644259171)
            ·
              refine ⟨147088230476924609466388757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98058820317949739644259171 147088230476924609466388757)
              ·
                refine ⟨6894760803605841068736973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147088230476924609466388757 6894760803605841068736973)
                ·
                  refine ⟨2585535301352190400776365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6894760803605841068736973 2585535301352190400776365)
                  ·
                    refine ⟨969575738007071400291137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2585535301352190400776365 969575738007071400291137)
                    ·
                      rfl

theorem cell22_2832363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 3].length) (baseStart_2832363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832363 prefixEnd_2832363 := by exact prefixLift 2832363
  have htrace : WordTrace (prefixWord ++ tailWord_2832363) baseStart_2832363 baseEnd_2832363 := by
    simpa [prefixWord, tailWord_2832363, baseEnd_2832363] using wordTrace_append hprefix tailTrace_2832363
  have hstable : (prefixWord ++ tailWord_2832363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832363).length < 2 ^ (prefixWord ++ tailWord_2832363).sum := by decide
  have hdescent : baseEnd_2832363 < baseStart_2832363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832376 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_2832376 : Nat := 118140960795 + 2832376 * 2 ^ 59
def prefixEnd_2832376 : Nat := 4983230072969 + 3 ^ 40 * 2832376 * 2
def baseEnd_2832376 : Nat := 323193396057581233238699

theorem tailTrace_2832376 : CollatzResearch.WordTrace tailWord_2832376 prefixEnd_2832376 323193396057581233238699 := by
  unfold tailWord_2832376
  simp only [CollatzResearch.WordTrace]
  refine ⟨51652619793396479077046491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68870159724528638769395321 51652619793396479077046491)
  ·
    refine ⟨77478929690094718615569737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51652619793396479077046491 77478929690094718615569737)
    ·
      refine ⟨58109197267571038961677303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77478929690094718615569737 58109197267571038961677303)
      ·
        refine ⟨87163795901356558442515955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58109197267571038961677303 87163795901356558442515955)
        ·
          refine ⟨130745693852034837663773933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87163795901356558442515955 130745693852034837663773933)
          ·
            refine ⟨49029635194513064123915225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130745693852034837663773933 49029635194513064123915225)
            ·
              refine ⟨36772226395884798092936419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49029635194513064123915225 36772226395884798092936419)
              ·
                refine ⟨55158339593827197139404629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36772226395884798092936419 55158339593827197139404629)
                ·
                  refine ⟨323193396057581233238699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55158339593827197139404629 323193396057581233238699)
                  ·
                    rfl

theorem cell22_2832376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_2832376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832376 prefixEnd_2832376 := by exact prefixLift 2832376
  have htrace : WordTrace (prefixWord ++ tailWord_2832376) baseStart_2832376 baseEnd_2832376 := by
    simpa [prefixWord, tailWord_2832376, baseEnd_2832376] using wordTrace_append hprefix tailTrace_2832376
  have hstable : (prefixWord ++ tailWord_2832376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832376).length < 2 ^ (prefixWord ++ tailWord_2832376).sum := by decide
  have hdescent : baseEnd_2832376 < baseStart_2832376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832408 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_2832408 : Nat := 118140960795 + 2832408 * 2 ^ 59
def prefixEnd_2832408 : Nat := 4983230072969 + 3 ^ 40 * 2832408 * 2
def baseEnd_2832408 : Nat := 969591142426706282915999

theorem tailTrace_2832408 : CollatzResearch.WordTrace tailWord_2832408 prefixEnd_2832408 969591142426706282915999 := by
  unfold tailWord_2832408
  simp only [CollatzResearch.WordTrace]
  refine ⟨51653203361338513809628939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68870937815118018412838585 51653203361338513809628939)
  ·
    refine ⟨77479805042007770714443409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51653203361338513809628939 77479805042007770714443409)
    ·
      refine ⟨58109853781505828035832557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77479805042007770714443409 58109853781505828035832557)
      ·
        refine ⟨21791195168064685513437209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58109853781505828035832557 21791195168064685513437209)
        ·
          refine ⟨16343396376048514135077907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21791195168064685513437209 16343396376048514135077907)
          ·
            refine ⟨24515094564072771202616861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16343396376048514135077907 24515094564072771202616861)
            ·
              refine ⟨9193160461527289200981323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24515094564072771202616861 9193160461527289200981323)
              ·
                refine ⟨13789740692290933801471985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193160461527289200981323 13789740692290933801471985)
                ·
                  refine ⟨10342305519218200351103989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13789740692290933801471985 10342305519218200351103989)
                  ·
                    refine ⟨969591142426706282915999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10342305519218200351103989 969591142426706282915999)
                    ·
                      rfl

theorem cell22_2832408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_2832408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832408 prefixEnd_2832408 := by exact prefixLift 2832408
  have htrace : WordTrace (prefixWord ++ tailWord_2832408) baseStart_2832408 baseEnd_2832408 := by
    simpa [prefixWord, tailWord_2832408, baseEnd_2832408] using wordTrace_append hprefix tailTrace_2832408
  have hstable : (prefixWord ++ tailWord_2832408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832408).length < 2 ^ (prefixWord ++ tailWord_2832408).sum := by decide
  have hdescent : baseEnd_2832408 < baseStart_2832408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832455 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 4]
def baseStart_2832455 : Nat := 118140960795 + 2832455 * 2 ^ 59
def prefixEnd_2832455 : Nat := 4983230072969 + 3 ^ 40 * 2832455 * 2
def baseEnd_2832455 : Nat := 323202410495737942330285

theorem tailTrace_2832455 : CollatzResearch.WordTrace tailWord_2832455 prefixEnd_2832455 323202410495737942330285 := by
  unfold tailWord_2832455
  simp only [CollatzResearch.WordTrace]
  refine ⟨103308120953506754646218819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68872080635671169764145879 103308120953506754646218819)
  ·
    refine ⟨154962181430260131969328229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103308120953506754646218819 154962181430260131969328229)
    ·
      refine ⟨29055409018173774744249043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154962181430260131969328229 29055409018173774744249043)
      ·
        refine ⟨43583113527260662116373565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29055409018173774744249043 43583113527260662116373565)
        ·
          refine ⟨16343667572722748293640087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43583113527260662116373565 16343667572722748293640087)
          ·
            refine ⟨24515501359084122440460131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16343667572722748293640087 24515501359084122440460131)
            ·
              refine ⟨36773252038626183660690197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24515501359084122440460131 36773252038626183660690197)
              ·
                refine ⟨1723746189310602359094853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36773252038626183660690197 1723746189310602359094853)
                ·
                  refine ⟨323202410495737942330285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1723746189310602359094853 323202410495737942330285)
                  ·
                    rfl

theorem cell22_2832455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 4].length) (baseStart_2832455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832455 prefixEnd_2832455 := by exact prefixLift 2832455
  have htrace : WordTrace (prefixWord ++ tailWord_2832455) baseStart_2832455 baseEnd_2832455 := by
    simpa [prefixWord, tailWord_2832455, baseEnd_2832455] using wordTrace_append hprefix tailTrace_2832455
  have hstable : (prefixWord ++ tailWord_2832455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832455).length < 2 ^ (prefixWord ++ tailWord_2832455).sum := by decide
  have hdescent : baseEnd_2832455 < baseStart_2832455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832502 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2832502 : Nat := 118140960795 + 2832502 * 2 ^ 59
def prefixEnd_2832502 : Nat := 4983230072969 + 3 ^ 40 * 2832502 * 2
def baseEnd_2832502 : Nat := 969623320547721371065711

theorem tailTrace_2832502 : CollatzResearch.WordTrace tailWord_2832502 prefixEnd_2832502 969623320547721371065711 := by
  unfold tailWord_2832502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456864699021030104573735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68873223456224321115453173 6456864699021030104573735)
  ·
    refine ⟨9685297048531545156860603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6456864699021030104573735 9685297048531545156860603)
    ·
      refine ⟨14527945572797317735290905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9685297048531545156860603 14527945572797317735290905)
      ·
        refine ⟨10895959179597988301468179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14527945572797317735290905 10895959179597988301468179)
        ·
          refine ⟨16343938769396982452202269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10895959179597988301468179 16343938769396982452202269)
          ·
            refine ⟨6128977038523868419575851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16343938769396982452202269 6128977038523868419575851)
            ·
              refine ⟨9193465557785802629363777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128977038523868419575851 9193465557785802629363777)
              ·
                refine ⟨6895099168339351972022833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9193465557785802629363777 6895099168339351972022833)
                ·
                  refine ⟨5171324376254513979017125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6895099168339351972022833 5171324376254513979017125)
                  ·
                    refine ⟨969623320547721371065711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5171324376254513979017125 969623320547721371065711)
                    ·
                      rfl

theorem cell22_2832502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2832502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832502 prefixEnd_2832502 := by exact prefixLift 2832502
  have htrace : WordTrace (prefixWord ++ tailWord_2832502) baseStart_2832502 baseEnd_2832502 := by
    simpa [prefixWord, tailWord_2832502, baseEnd_2832502] using wordTrace_append hprefix tailTrace_2832502
  have hstable : (prefixWord ++ tailWord_2832502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832502).length < 2 ^ (prefixWord ++ tailWord_2832502).sum := by decide
  have hdescent : baseEnd_2832502 < baseStart_2832502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832590 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_2832590 : Nat := 118140960795 + 2832590 * 2 ^ 59
def prefixEnd_2832590 : Nat := 4983230072969 + 3 ^ 40 * 2832590 * 2
def baseEnd_2832590 : Nat := 323217814915372824955147

theorem tailTrace_2832590 : CollatzResearch.WordTrace tailWord_2832590 prefixEnd_2832590 323217814915372824955147 := by
  unfold tailWord_2832590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12914130601002209087797903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68875363205345115134922149 12914130601002209087797903)
  ·
    refine ⟨19371195901503313631696855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12914130601002209087797903 19371195901503313631696855)
    ·
      refine ⟨29056793852254970447545283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19371195901503313631696855 29056793852254970447545283)
      ·
        refine ⟨43585190778382455671317925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29056793852254970447545283 43585190778382455671317925)
        ·
          refine ⟨8172223270946710438372111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43585190778382455671317925 8172223270946710438372111)
          ·
            refine ⟨12258334906420065657558167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8172223270946710438372111 12258334906420065657558167)
            ·
              refine ⟨18387502359630098486337251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12258334906420065657558167 18387502359630098486337251)
              ·
                refine ⟨27581253539445147729505877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18387502359630098486337251 27581253539445147729505877)
                ·
                  refine ⟨323217814915372824955147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27581253539445147729505877 323217814915372824955147)
                  ·
                    rfl

theorem cell22_2832590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_2832590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832590 prefixEnd_2832590 := by exact prefixLift 2832590
  have htrace : WordTrace (prefixWord ++ tailWord_2832590) baseStart_2832590 baseEnd_2832590 := by
    simpa [prefixWord, tailWord_2832590, baseEnd_2832590] using wordTrace_append hprefix tailTrace_2832590
  have hstable : (prefixWord ++ tailWord_2832590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832590).length < 2 ^ (prefixWord ++ tailWord_2832590).sum := by decide
  have hdescent : baseEnd_2832590 < baseStart_2832590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832620 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_2832620 : Nat := 118140960795 + 2832620 * 2 ^ 59
def prefixEnd_2832620 : Nat := 4983230072969 + 3 ^ 40 * 2832620 * 2
def baseEnd_2832620 : Nat := 969663714359208396615349

theorem tailTrace_2832620 : CollatzResearch.WordTrace tailWord_2832620 prefixEnd_2832620 969663714359208396615349 := by
  unfold tailWord_2832620
  simp only [CollatzResearch.WordTrace]
  refine ⟨51657069498954493912987657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68876092665272658550650209 51657069498954493912987657)
  ·
    refine ⟨38742802124215870434740743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51657069498954493912987657 38742802124215870434740743)
    ·
      refine ⟨58114203186323805652111115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38742802124215870434740743 58114203186323805652111115)
      ·
        refine ⟨87171304779485708478166673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58114203186323805652111115 87171304779485708478166673)
        ·
          refine ⟨65378478584614281358625005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87171304779485708478166673 65378478584614281358625005)
          ·
            refine ⟨24516929469230355509484377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65378478584614281358625005 24516929469230355509484377)
            ·
              refine ⟨18387697101922766632113283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24516929469230355509484377 18387697101922766632113283)
              ·
                refine ⟨27581545652884149948169925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18387697101922766632113283 27581545652884149948169925)
                ·
                  refine ⟨5171539809915778115281861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27581545652884149948169925 5171539809915778115281861)
                  ·
                    refine ⟨969663714359208396615349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5171539809915778115281861 969663714359208396615349)
                    ·
                      rfl

theorem cell22_2832620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_2832620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832620 prefixEnd_2832620 := by exact prefixLift 2832620
  have htrace : WordTrace (prefixWord ++ tailWord_2832620) baseStart_2832620 baseEnd_2832620 := by
    simpa [prefixWord, tailWord_2832620, baseEnd_2832620] using wordTrace_append hprefix tailTrace_2832620
  have hstable : (prefixWord ++ tailWord_2832620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832620).length < 2 ^ (prefixWord ++ tailWord_2832620).sum := by decide
  have hdescent : baseEnd_2832620 < baseStart_2832620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832639 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 2, 3]
def baseStart_2832639 : Nat := 118140960795 + 2832639 * 2 ^ 59
def prefixEnd_2832639 : Nat := 4983230072969 + 3 ^ 40 * 2832639 * 2
def baseEnd_2832639 : Nat := 969670218447498680390291

theorem tailTrace_2832639 : CollatzResearch.WordTrace tailWord_2832639 prefixEnd_2832639 969670218447498680390291 := by
  unfold tailWord_2832639
  simp only [CollatzResearch.WordTrace]
  refine ⟨103314831984840154070916971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68876554656560102713944647 103314831984840154070916971)
  ·
    refine ⟨154972247977260231106375457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103314831984840154070916971 154972247977260231106375457)
    ·
      refine ⟨116229185982945173329781593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154972247977260231106375457 116229185982945173329781593)
      ·
        refine ⟨87171889487208879997336195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116229185982945173329781593 87171889487208879997336195)
        ·
          refine ⟨130757834230813319996004293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87171889487208879997336195 130757834230813319996004293)
          ·
            refine ⟨24517093918277497499250805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130757834230813319996004293 24517093918277497499250805)
            ·
              refine ⟨2298477554838515390554763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24517093918277497499250805 2298477554838515390554763)
              ·
                refine ⟨3447716332257773085832145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298477554838515390554763 3447716332257773085832145)
                ·
                  refine ⟨2585787249193329814374109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447716332257773085832145 2585787249193329814374109)
                  ·
                    refine ⟨969670218447498680390291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2585787249193329814374109 969670218447498680390291)
                    ·
                      rfl

theorem cell22_2832639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_2832639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832639 prefixEnd_2832639 := by exact prefixLift 2832639
  have htrace : WordTrace (prefixWord ++ tailWord_2832639) baseStart_2832639 baseEnd_2832639 := by
    simpa [prefixWord, tailWord_2832639, baseEnd_2832639] using wordTrace_append hprefix tailTrace_2832639
  have hstable : (prefixWord ++ tailWord_2832639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832639).length < 2 ^ (prefixWord ++ tailWord_2832639).sum := by decide
  have hdescent : baseEnd_2832639 < baseStart_2832639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832669 : List Nat := [1, 4, 2, 3, 3, 1, 8]
def baseStart_2832669 : Nat := 118140960795 + 2832669 * 2 ^ 59
def prefixEnd_2832669 : Nat := 4983230072969 + 3 ^ 40 * 2832669 * 2
def baseEnd_2832669 : Nat := 35914092150392170449637

theorem tailTrace_2832669 : CollatzResearch.WordTrace tailWord_2832669 prefixEnd_2832669 35914092150392170449637 := by
  unfold tailWord_2832669
  simp only [CollatzResearch.WordTrace]
  refine ⟨103315926174731469194509061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68877284116487646129672707 103315926174731469194509061)
  ·
    refine ⟨19371736157762150473970449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103315926174731469194509061 19371736157762150473970449)
    ·
      refine ⟨14528802118321612855477837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19371736157762150473970449 14528802118321612855477837)
      ·
        refine ⟨5448300794370604820804189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14528802118321612855477837 5448300794370604820804189)
        ·
          refine ⟨2043112797888976807801571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5448300794370604820804189 2043112797888976807801571)
          ·
            refine ⟨3064669196833465211702357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043112797888976807801571 3064669196833465211702357)
            ·
              refine ⟨35914092150392170449637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3064669196833465211702357 35914092150392170449637)
              ·
                rfl

theorem cell22_2832669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 8].length) (baseStart_2832669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832669 prefixEnd_2832669 := by exact prefixLift 2832669
  have htrace : WordTrace (prefixWord ++ tailWord_2832669) baseStart_2832669 baseEnd_2832669 := by
    simpa [prefixWord, tailWord_2832669, baseEnd_2832669] using wordTrace_append hprefix tailTrace_2832669
  have hstable : (prefixWord ++ tailWord_2832669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832669).length < 2 ^ (prefixWord ++ tailWord_2832669).sum := by decide
  have hdescent : baseEnd_2832669 < baseStart_2832669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832684 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_2832684 : Nat := 118140960795 + 2832684 * 2 ^ 59
def prefixEnd_2832684 : Nat := 4983230072969 + 3 ^ 40 * 2832684 * 2
def baseEnd_2832684 : Nat := 969685622867133563015153

theorem tailTrace_2832684 : CollatzResearch.WordTrace tailWord_2832684 prefixEnd_2832684 969685622867133563015153 := by
  unfold tailWord_2832684
  simp only [CollatzResearch.WordTrace]
  refine ⟨51658236634838563378152553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68877648846451417837536737 51658236634838563378152553)
  ·
    refine ⟨38743677476128922533614415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51658236634838563378152553 38743677476128922533614415)
    ·
      refine ⟨58115516214193383800421623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38743677476128922533614415 58115516214193383800421623)
      ·
        refine ⟨87173274321290075700632435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58115516214193383800421623 87173274321290075700632435)
        ·
          refine ⟨130759911481935113550948653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87173274321290075700632435 130759911481935113550948653)
          ·
            refine ⟨49034966805725667581605745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130759911481935113550948653 49034966805725667581605745)
            ·
              refine ⟨36776225104294250686204309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49034966805725667581605745 36776225104294250686204309)
              ·
                refine ⟨1723885551763793000915827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36776225104294250686204309 1723885551763793000915827)
                ·
                  refine ⟨2585828327645689501373741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1723885551763793000915827 2585828327645689501373741)
                  ·
                    refine ⟨969685622867133563015153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2585828327645689501373741 969685622867133563015153)
                    ·
                      rfl

theorem cell22_2832684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_2832684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832684 prefixEnd_2832684 := by exact prefixLift 2832684
  have htrace : WordTrace (prefixWord ++ tailWord_2832684) baseStart_2832684 baseEnd_2832684 := by
    simpa [prefixWord, tailWord_2832684, baseEnd_2832684] using wordTrace_append hprefix tailTrace_2832684
  have hstable : (prefixWord ++ tailWord_2832684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832684).length < 2 ^ (prefixWord ++ tailWord_2832684).sum := by decide
  have hdescent : baseEnd_2832684 < baseStart_2832684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832695 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_2832695 : Nat := 118140960795 + 2832695 * 2 ^ 59
def prefixEnd_2832695 : Nat := 4983230072969 + 3 ^ 40 * 2832695 * 2
def baseEnd_2832695 : Nat := 969689388391933200990119

theorem tailTrace_2832695 : CollatzResearch.WordTrace tailWord_2832695 prefixEnd_2832695 969689388391933200990119 := by
  unfold tailWord_2832695
  simp only [CollatzResearch.WordTrace]
  refine ⟨103316874472637275634955539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68877916315091517089970359 103316874472637275634955539)
  ·
    refine ⟨154975311708955913452433309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103316874472637275634955539 154975311708955913452433309)
    ·
      refine ⟨58115741890858467544662491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154975311708955913452433309 58115741890858467544662491)
      ·
        refine ⟨87173612836287701316993737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58115741890858467544662491 87173612836287701316993737)
        ·
          refine ⟨65380209627215775987745303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87173612836287701316993737 65380209627215775987745303)
          ·
            refine ⟨98070314440823663981617955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65380209627215775987745303 98070314440823663981617955)
            ·
              refine ⟨147105471661235495972426933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98070314440823663981617955 147105471661235495972426933)
              ·
                refine ⟨13791137968240827747415025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147105471661235495972426933 13791137968240827747415025)
                ·
                  refine ⟨10343353476180620810561269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13791137968240827747415025 10343353476180620810561269)
                  ·
                    refine ⟨969689388391933200990119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10343353476180620810561269 969689388391933200990119)
                    ·
                      rfl

theorem cell22_2832695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_2832695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832695 prefixEnd_2832695 := by exact prefixLift 2832695
  have htrace : WordTrace (prefixWord ++ tailWord_2832695) baseStart_2832695 baseEnd_2832695 := by
    simpa [prefixWord, tailWord_2832695, baseEnd_2832695] using wordTrace_append hprefix tailTrace_2832695
  have hstable : (prefixWord ++ tailWord_2832695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832695).length < 2 ^ (prefixWord ++ tailWord_2832695).sum := by decide
  have hdescent : baseEnd_2832695 < baseStart_2832695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832755 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_2832755 : Nat := 118140960795 + 2832755 * 2 ^ 59
def prefixEnd_2832755 : Nat := 4983230072969 + 3 ^ 40 * 2832755 * 2
def baseEnd_2832755 : Nat := 969709927618113044489935

theorem tailTrace_2832755 : CollatzResearch.WordTrace tailWord_2832755 prefixEnd_2832755 969709927618113044489935 := by
  unfold tailWord_2832755
  simp only [CollatzResearch.WordTrace]
  refine ⟨103319062852419905882139719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68879375234946603921426479 103319062852419905882139719)
  ·
    refine ⟨154978594278629858823209579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103319062852419905882139719 154978594278629858823209579)
    ·
      refine ⟨232467891417944788234814369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154978594278629858823209579 232467891417944788234814369)
      ·
        refine ⟨174350918563458591176110777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232467891417944788234814369 174350918563458591176110777)
        ·
          refine ⟨130763188922593943382083083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174350918563458591176110777 130763188922593943382083083)
          ·
            refine ⟨196144783383890915073124625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130763188922593943382083083 196144783383890915073124625)
            ·
              refine ⟨147108587537918186304843469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196144783383890915073124625 147108587537918186304843469)
              ·
                refine ⟨55165720326719319864316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147108587537918186304843469 55165720326719319864316301)
                ·
                  refine ⟨20687145122519744949118613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55165720326719319864316301 20687145122519744949118613)
                  ·
                    refine ⟨969709927618113044489935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20687145122519744949118613 969709927618113044489935)
                    ·
                      rfl

theorem cell22_2832755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_2832755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832755 prefixEnd_2832755 := by exact prefixLift 2832755
  have htrace : WordTrace (prefixWord ++ tailWord_2832755) baseStart_2832755 baseEnd_2832755 := by
    simpa [prefixWord, tailWord_2832755, baseEnd_2832755] using wordTrace_append hprefix tailTrace_2832755
  have hstable : (prefixWord ++ tailWord_2832755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832755).length < 2 ^ (prefixWord ++ tailWord_2832755).sum := by decide
  have hdescent : baseEnd_2832755 < baseStart_2832755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832772 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2832772 : Nat := 118140960795 + 2832772 * 2 ^ 59
def prefixEnd_2832772 : Nat := 4983230072969 + 3 ^ 40 * 2832772 * 2
def baseEnd_2832772 : Nat := 969715747065530666814883

theorem tailTrace_2832772 : CollatzResearch.WordTrace tailWord_2832772 prefixEnd_2832772 969715747065530666814883 := by
  unfold tailWord_2832772
  simp only [CollatzResearch.WordTrace]
  refine ⟨51659841446679158892754285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68879788595572211857005713 51659841446679158892754285)
  ·
    refine ⟨19372440542504684584782857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51659841446679158892754285 19372440542504684584782857)
    ·
      refine ⟨14529330406878513438587143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19372440542504684584782857 14529330406878513438587143)
      ·
        refine ⟨21793995610317770157880715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14529330406878513438587143 21793995610317770157880715)
        ·
          refine ⟨32690993415476655236821073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21793995610317770157880715 32690993415476655236821073)
          ·
            refine ⟨24518245061607491427615805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32690993415476655236821073 24518245061607491427615805)
            ·
              refine ⟨9194341898102809285355927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24518245061607491427615805 9194341898102809285355927)
              ·
                refine ⟨13791512847154213928033891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9194341898102809285355927 13791512847154213928033891)
                ·
                  refine ⟨20687269270731320892050837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13791512847154213928033891 20687269270731320892050837)
                  ·
                    refine ⟨969715747065530666814883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20687269270731320892050837 969715747065530666814883)
                    ·
                      rfl

theorem cell22_2832772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2832772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832772 prefixEnd_2832772 := by exact prefixLift 2832772
  have htrace : WordTrace (prefixWord ++ tailWord_2832772) baseStart_2832772 baseEnd_2832772 := by
    simpa [prefixWord, tailWord_2832772, baseEnd_2832772] using wordTrace_append hprefix tailTrace_2832772
  have hstable : (prefixWord ++ tailWord_2832772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832772).length < 2 ^ (prefixWord ++ tailWord_2832772).sum := by decide
  have hdescent : baseEnd_2832772 < baseStart_2832772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832821 : List Nat := [1, 3, 3, 2, 3, 2, 2, 6]
def baseStart_2832821 : Nat := 118140960795 + 2832821 * 2 ^ 59
def prefixEnd_2832821 : Nat := 4983230072969 + 3 ^ 40 * 2832821 * 2
def baseEnd_2832821 : Nat := 107748057862990096926637

theorem tailTrace_2832821 : CollatzResearch.WordTrace tailWord_2832821 prefixEnd_2832821 107748057862990096926637 := by
  unfold tailWord_2832821
  simp only [CollatzResearch.WordTrace]
  refine ⟨103321470070180799154042317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68880980046787199436028211 103321470070180799154042317)
  ·
    refine ⟨38745551276317799682765869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103321470070180799154042317 38745551276317799682765869)
    ·
      refine ⟨14529581728619174881037201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38745551276317799682765869 14529581728619174881037201)
      ·
        refine ⟨10897186296464381160777901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14529581728619174881037201 10897186296464381160777901)
        ·
          refine ⟨4086444861174142935291713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10897186296464381160777901 4086444861174142935291713)
          ·
            refine ⟨3064833645880607201468785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4086444861174142935291713 3064833645880607201468785)
            ·
              refine ⟨2298625234410455401101589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064833645880607201468785 2298625234410455401101589)
              ·
                refine ⟨107748057862990096926637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2298625234410455401101589 107748057862990096926637)
                ·
                  rfl

theorem cell22_2832821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 6].length) (baseStart_2832821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832821 prefixEnd_2832821 := by exact prefixLift 2832821
  have htrace : WordTrace (prefixWord ++ tailWord_2832821) baseStart_2832821 baseEnd_2832821 := by
    simpa [prefixWord, tailWord_2832821, baseEnd_2832821] using wordTrace_append hprefix tailTrace_2832821
  have hstable : (prefixWord ++ tailWord_2832821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832821).length < 2 ^ (prefixWord ++ tailWord_2832821).sum := by decide
  have hdescent : baseEnd_2832821 < baseStart_2832821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832984 : List Nat := [2, 1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_2832984 : Nat := 118140960795 + 2832984 * 2 ^ 59
def prefixEnd_2832984 : Nat := 4983230072969 + 3 ^ 40 * 2832984 * 2
def baseEnd_2832984 : Nat := 323262772999344260171411

theorem tailTrace_2832984 : CollatzResearch.WordTrace tailWord_2832984 prefixEnd_2832984 323262772999344260171411 := by
  unfold tailWord_2832984
  simp only [CollatzResearch.WordTrace]
  refine ⟨51663707584295138996113003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68884943445726851994817337 51663707584295138996113003)
  ·
    refine ⟨77495561376442708494169505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51663707584295138996113003 77495561376442708494169505)
    ·
      refine ⟨58121671032332031370627129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77495561376442708494169505 58121671032332031370627129)
      ·
        refine ⟨43591253274249023527970347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58121671032332031370627129 43591253274249023527970347)
        ·
          refine ⟨65386879911373535291955521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43591253274249023527970347 65386879911373535291955521)
          ·
            refine ⟨49040159933530151468966641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65386879911373535291955521 49040159933530151468966641)
            ·
              refine ⟨36780119950147613601724981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49040159933530151468966641 36780119950147613601724981)
              ·
                refine ⟨3448136245326338775161717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36780119950147613601724981 3448136245326338775161717)
                ·
                  refine ⟨323262772999344260171411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3448136245326338775161717 323262772999344260171411)
                  ·
                    rfl

theorem cell22_2832984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_2832984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832984 prefixEnd_2832984 := by exact prefixLift 2832984
  have htrace : WordTrace (prefixWord ++ tailWord_2832984) baseStart_2832984 baseEnd_2832984 := by
    simpa [prefixWord, tailWord_2832984, baseEnd_2832984] using wordTrace_append hprefix tailTrace_2832984
  have hstable : (prefixWord ++ tailWord_2832984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832984).length < 2 ^ (prefixWord ++ tailWord_2832984).sum := by decide
  have hdescent : baseEnd_2832984 < baseStart_2832984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2832990 : List Nat := [4, 4, 1, 2, 1, 1, 1, 8]
def baseStart_2832990 : Nat := 118140960795 + 2832990 * 2 ^ 59
def prefixEnd_2832990 : Nat := 4983230072969 + 3 ^ 40 * 2832990 * 2
def baseEnd_2832990 : Nat := 107754485880072307207135

theorem tailTrace_2832990 : CollatzResearch.WordTrace tailWord_2832990 prefixEnd_2832990 107754485880072307207135 := by
  unfold tailWord_2832990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915954250821067627118053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68885089337712360677962949 12915954250821067627118053)
  ·
    refine ⟨2421741422028950180084635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12915954250821067627118053 2421741422028950180084635)
    ·
      refine ⟨3632612133043425270126953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421741422028950180084635 3632612133043425270126953)
      ·
        refine ⟨2724459099782568952595215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3632612133043425270126953 2724459099782568952595215)
        ·
          refine ⟨4086688649673853428892823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724459099782568952595215 4086688649673853428892823)
          ·
            refine ⟨6130032974510780143339235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086688649673853428892823 6130032974510780143339235)
            ·
              refine ⟨9195049461766170215008853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130032974510780143339235 9195049461766170215008853)
              ·
                refine ⟨107754485880072307207135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9195049461766170215008853 107754485880072307207135)
                ·
                  rfl

theorem cell22_2832990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_2832990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2832990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2832990 prefixEnd_2832990 := by exact prefixLift 2832990
  have htrace : WordTrace (prefixWord ++ tailWord_2832990) baseStart_2832990 baseEnd_2832990 := by
    simpa [prefixWord, tailWord_2832990, baseEnd_2832990] using wordTrace_append hprefix tailTrace_2832990
  have hstable : (prefixWord ++ tailWord_2832990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2832990).length < 2 ^ (prefixWord ++ tailWord_2832990).sum := by decide
  have hdescent : baseEnd_2832990 < baseStart_2832990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2832990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833005 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_2833005 : Nat := 118140960795 + 2833005 * 2 ^ 59
def prefixEnd_2833005 : Nat := 4983230072969 + 3 ^ 40 * 2833005 * 2
def baseEnd_2833005 : Nat := 969795507727195725739169

theorem tailTrace_2833005 : CollatzResearch.WordTrace tailWord_2833005 prefixEnd_2833005 969795507727195725739169 := by
  unfold tailWord_2833005
  simp only [CollatzResearch.WordTrace]
  refine ⟨103328181101514198578740469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68885454067676132385826979 103328181101514198578740469)
  ·
    refine ⟨9687016978266956116756919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103328181101514198578740469 9687016978266956116756919)
    ·
      refine ⟨14530525467400434175135379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9687016978266956116756919 14530525467400434175135379)
      ·
        refine ⟨21795788201100651262703069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14530525467400434175135379 21795788201100651262703069)
        ·
          refine ⟨8173420575412744223513651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21795788201100651262703069 8173420575412744223513651)
          ·
            refine ⟨12260130863119116335270477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173420575412744223513651 12260130863119116335270477)
            ·
              refine ⟨4597549073669668625726429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12260130863119116335270477 4597549073669668625726429)
              ·
                refine ⟨1724080902626125734647411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4597549073669668625726429 1724080902626125734647411)
                ·
                  refine ⟨2586121353939188601971117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724080902626125734647411 2586121353939188601971117)
                  ·
                    refine ⟨969795507727195725739169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2586121353939188601971117 969795507727195725739169)
                    ·
                      rfl

theorem cell22_2833005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_2833005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833005 prefixEnd_2833005 := by exact prefixLift 2833005
  have htrace : WordTrace (prefixWord ++ tailWord_2833005) baseStart_2833005 baseEnd_2833005 := by
    simpa [prefixWord, tailWord_2833005, baseEnd_2833005] using wordTrace_append hprefix tailTrace_2833005
  have hstable : (prefixWord ++ tailWord_2833005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833005).length < 2 ^ (prefixWord ++ tailWord_2833005).sum := by decide
  have hdescent : baseEnd_2833005 < baseStart_2833005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833183 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 1, 4]
def baseStart_2833183 : Nat := 118140960795 + 2833183 * 2 ^ 59
def prefixEnd_2833183 : Nat := 4983230072969 + 3 ^ 40 * 2833183 * 2
def baseEnd_2833183 : Nat := 969856440764862594788623

theorem tailTrace_2833183 : CollatzResearch.WordTrace tailWord_2833183 prefixEnd_2833183 969856440764862594788623 := by
  unfold tailWord_2833183
  simp only [CollatzResearch.WordTrace]
  refine ⟨103334673294869334978720203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68889782196579556652480135 103334673294869334978720203)
  ·
    refine ⟨155002009942304002468080305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103334673294869334978720203 155002009942304002468080305)
    ·
      refine ⟨116251507456728001851060229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155002009942304002468080305 116251507456728001851060229)
      ·
        refine ⟨21797157648136500347073793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116251507456728001851060229 21797157648136500347073793)
        ·
          refine ⟨16347868236102375260305345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21797157648136500347073793 16347868236102375260305345)
          ·
            refine ⟨12260901177076781445229009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16347868236102375260305345 12260901177076781445229009)
            ·
              refine ⟨9195675882807586083921757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12260901177076781445229009 9195675882807586083921757)
              ·
                refine ⟨3448378456052844781470659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9195675882807586083921757 3448378456052844781470659)
                ·
                  refine ⟨5172567684079267172205989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448378456052844781470659 5172567684079267172205989)
                  ·
                    refine ⟨969856440764862594788623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5172567684079267172205989 969856440764862594788623)
                    ·
                      rfl

theorem cell22_2833183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_2833183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833183 prefixEnd_2833183 := by exact prefixLift 2833183
  have htrace : WordTrace (prefixWord ++ tailWord_2833183) baseStart_2833183 baseEnd_2833183 := by
    simpa [prefixWord, tailWord_2833183, baseEnd_2833183] using wordTrace_append hprefix tailTrace_2833183
  have hstable : (prefixWord ++ tailWord_2833183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833183).length < 2 ^ (prefixWord ++ tailWord_2833183).sum := by decide
  have hdescent : baseEnd_2833183 < baseStart_2833183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833204 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2833204 : Nat := 118140960795 + 2833204 * 2 ^ 59
def prefixEnd_2833204 : Nat := 4983230072969 + 3 ^ 40 * 2833204 * 2
def baseEnd_2833204 : Nat := 323287876498008513337853

theorem tailTrace_2833204 : CollatzResearch.WordTrace tailWord_2833204 prefixEnd_2833204 323287876498008513337853 := by
  unfold tailWord_2833204
  simp only [CollatzResearch.WordTrace]
  refine ⟨51667719613896627782617333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68890292818528837043489777 51667719613896627782617333)
  ·
    refine ⟨4843848713802808854620375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51667719613896627782617333 4843848713802808854620375)
    ·
      refine ⟨7265773070704213281930563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843848713802808854620375 7265773070704213281930563)
      ·
        refine ⟨10898659606056319922895845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265773070704213281930563 10898659606056319922895845)
        ·
          refine ⟨2043498676135559985542971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10898659606056319922895845 2043498676135559985542971)
          ·
            refine ⟨3065248014203339978314457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043498676135559985542971 3065248014203339978314457)
            ·
              refine ⟨2298936010652504983735843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3065248014203339978314457 2298936010652504983735843)
              ·
                refine ⟨3448404015978757475603765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298936010652504983735843 3448404015978757475603765)
                ·
                  refine ⟨323287876498008513337853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3448404015978757475603765 323287876498008513337853)
                  ·
                    rfl

theorem cell22_2833204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2833204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833204 prefixEnd_2833204 := by exact prefixLift 2833204
  have htrace : WordTrace (prefixWord ++ tailWord_2833204) baseStart_2833204 baseEnd_2833204 := by
    simpa [prefixWord, tailWord_2833204, baseEnd_2833204] using wordTrace_append hprefix tailTrace_2833204
  have hstable : (prefixWord ++ tailWord_2833204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833204).length < 2 ^ (prefixWord ++ tailWord_2833204).sum := by decide
  have hdescent : baseEnd_2833204 < baseStart_2833204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833228 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_2833228 : Nat := 118140960795 + 2833228 * 2 ^ 59
def prefixEnd_2833228 : Nat := 4983230072969 + 3 ^ 40 * 2833228 * 2
def baseEnd_2833228 : Nat := 969871845184497477413485

theorem tailTrace_2833228 : CollatzResearch.WordTrace tailWord_2833228 prefixEnd_2833228 969871845184497477413485 := by
  unfold tailWord_2833228
  simp only [CollatzResearch.WordTrace]
  refine ⟨51668157289853153832054169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68890876386470871776072225 51668157289853153832054169)
  ·
    refine ⟨38751117967389865374040627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51668157289853153832054169 38751117967389865374040627)
    ·
      refine ⟨58126676951084798061060941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38751117967389865374040627 58126676951084798061060941)
      ·
        refine ⟨21797503856656799272897853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58126676951084798061060941 21797503856656799272897853)
        ·
          refine ⟨8174063946246299727336695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21797503856656799272897853 8174063946246299727336695)
          ·
            refine ⟨12261095919369449591005043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8174063946246299727336695 12261095919369449591005043)
            ·
              refine ⟨18391643879054174386507565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12261095919369449591005043 18391643879054174386507565)
              ·
                refine ⟨6896866454645315394940337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18391643879054174386507565 6896866454645315394940337)
                ·
                  refine ⟨5172649840983986546205253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6896866454645315394940337 5172649840983986546205253)
                  ·
                    refine ⟨969871845184497477413485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5172649840983986546205253 969871845184497477413485)
                    ·
                      rfl

theorem cell22_2833228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_2833228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833228 prefixEnd_2833228 := by exact prefixLift 2833228
  have htrace : WordTrace (prefixWord ++ tailWord_2833228) baseStart_2833228 baseEnd_2833228 := by
    simpa [prefixWord, tailWord_2833228, baseEnd_2833228] using wordTrace_append hprefix tailTrace_2833228
  have hstable : (prefixWord ++ tailWord_2833228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833228).length < 2 ^ (prefixWord ++ tailWord_2833228).sum := by decide
  have hdescent : baseEnd_2833228 < baseStart_2833228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833333 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 6]
def baseStart_2833333 : Nat := 118140960795 + 2833333 * 2 ^ 59
def prefixEnd_2833333 : Nat := 4983230072969 + 3 ^ 40 * 2833333 * 2
def baseEnd_2833333 : Nat := 323302596276770734512721

theorem tailTrace_2833333 : CollatzResearch.WordTrace tailWord_2833333 prefixEnd_2833333 323302596276770734512721 := by
  unfold tailWord_2833333
  simp only [CollatzResearch.WordTrace]
  refine ⟨103340144244325910596680653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68893429496217273731120435 103340144244325910596680653)
  ·
    refine ⟨38752554091622216473755245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103340144244325910596680653 38752554091622216473755245)
    ·
      refine ⟨14532207784358331177658217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38752554091622216473755245 14532207784358331177658217)
      ·
        refine ⟨10899155838268748383243663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14532207784358331177658217 10899155838268748383243663)
        ·
          refine ⟨16348733757403122574865495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10899155838268748383243663 16348733757403122574865495)
          ·
            refine ⟨24523100636104683862298243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16348733757403122574865495 24523100636104683862298243)
            ·
              refine ⟨36784650954157025793447365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24523100636104683862298243 36784650954157025793447365)
              ·
                refine ⟨6897122053904442336271381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36784650954157025793447365 6897122053904442336271381)
                ·
                  refine ⟨323302596276770734512721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6897122053904442336271381 323302596276770734512721)
                  ·
                    rfl

theorem cell22_2833333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_2833333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833333 prefixEnd_2833333 := by exact prefixLift 2833333
  have htrace : WordTrace (prefixWord ++ tailWord_2833333) baseStart_2833333 baseEnd_2833333 := by
    simpa [prefixWord, tailWord_2833333, baseEnd_2833333] using wordTrace_append hprefix tailTrace_2833333
  have hstable : (prefixWord ++ tailWord_2833333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833333).length < 2 ^ (prefixWord ++ tailWord_2833333).sum := by decide
  have hdescent : baseEnd_2833333 < baseStart_2833333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833517 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_2833517 : Nat := 118140960795 + 2833517 * 2 ^ 59
def prefixEnd_2833517 : Nat := 4983230072969 + 3 ^ 40 * 2833517 * 2
def baseEnd_2833517 : Nat := 969970775790597056937599

theorem tailTrace_2833517 : CollatzResearch.WordTrace tailWord_2833517 prefixEnd_2833517 969970775790597056937599 := by
  unfold tailWord_2833517
  simp only [CollatzResearch.WordTrace]
  refine ⟨103346855275659310021378805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68897903517106206680919203 103346855275659310021378805)
  ·
    refine ⟨9688767682093060314504263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103346855275659310021378805 9688767682093060314504263)
    ·
      refine ⟨14533151523139590471756395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9688767682093060314504263 14533151523139590471756395)
      ·
        refine ⟨21799727284709385707634593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14533151523139590471756395 21799727284709385707634593)
        ·
          refine ⟨16349795463532039280725945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21799727284709385707634593 16349795463532039280725945)
          ·
            refine ⟨12262346597649029460544459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16349795463532039280725945 12262346597649029460544459)
            ·
              refine ⟨18393519896473544190816689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12262346597649029460544459 18393519896473544190816689)
              ·
                refine ⟨13795139922355158143112517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18393519896473544190816689 13795139922355158143112517)
                ·
                  refine ⟨2586588735441592151833597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13795139922355158143112517 2586588735441592151833597)
                  ·
                    refine ⟨969970775790597056937599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2586588735441592151833597 969970775790597056937599)
                    ·
                      rfl

theorem cell22_2833517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_2833517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833517 prefixEnd_2833517 := by exact prefixLift 2833517
  have htrace : WordTrace (prefixWord ++ tailWord_2833517) baseStart_2833517 baseEnd_2833517 := by
    simpa [prefixWord, tailWord_2833517, baseEnd_2833517] using wordTrace_append hprefix tailTrace_2833517
  have hstable : (prefixWord ++ tailWord_2833517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833517).length < 2 ^ (prefixWord ++ tailWord_2833517).sum := by decide
  have hdescent : baseEnd_2833517 < baseStart_2833517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833596 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_2833596 : Nat := 118140960795 + 2833596 * 2 ^ 59
def prefixEnd_2833596 : Nat := 4983230072969 + 3 ^ 40 * 2833596 * 2
def baseEnd_2833596 : Nat := 969997819105067184212357

theorem tailTrace_2833596 : CollatzResearch.WordTrace tailWord_2833596 prefixEnd_2833596 969997819105067184212357 := by
  unfold tailWord_2833596
  simp only [CollatzResearch.WordTrace]
  refine ⟨51674868321186553256752321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68899824428248737675669761 51674868321186553256752321)
  ·
    refine ⟨38756151240889914942564241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51674868321186553256752321 38756151240889914942564241)
    ·
      refine ⟨29067113430667436206923181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38756151240889914942564241 29067113430667436206923181)
      ·
        refine ⟨10900167536500288577596193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29067113430667436206923181 10900167536500288577596193)
        ·
          refine ⟨8175125652375216433197145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10900167536500288577596193 8175125652375216433197145)
          ·
            refine ⟨6131344239281412324897859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8175125652375216433197145 6131344239281412324897859)
            ·
              refine ⟨9197016358922118487346789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131344239281412324897859 9197016358922118487346789)
              ·
                refine ⟨1724440567297897216377523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9197016358922118487346789 1724440567297897216377523)
                ·
                  refine ⟨2586660850946845824566285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724440567297897216377523 2586660850946845824566285)
                  ·
                    refine ⟨969997819105067184212357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2586660850946845824566285 969997819105067184212357)
                    ·
                      rfl

theorem cell22_2833596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_2833596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833596 prefixEnd_2833596 := by exact prefixLift 2833596
  have htrace : WordTrace (prefixWord ++ tailWord_2833596) baseStart_2833596 baseEnd_2833596 := by
    simpa [prefixWord, tailWord_2833596, baseEnd_2833596] using wordTrace_append hprefix tailTrace_2833596
  have hstable : (prefixWord ++ tailWord_2833596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833596).length < 2 ^ (prefixWord ++ tailWord_2833596).sum := by decide
  have hdescent : baseEnd_2833596 < baseStart_2833596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833613 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2833613 : Nat := 118140960795 + 2833613 * 2 ^ 59
def prefixEnd_2833613 : Nat := 4983230072969 + 3 ^ 40 * 2833613 * 2
def baseEnd_2833613 : Nat := 970003638552484806537305

theorem tailTrace_2833613 : CollatzResearch.WordTrace tailWord_2833613 prefixEnd_2833613 970003638552484806537305 := by
  unfold tailWord_2833613
  simp only [CollatzResearch.WordTrace]
  refine ⟨103350356683311518416873493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68900237788874345611248995 103350356683311518416873493)
  ·
    refine ⟨4844547969530227425790945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103350356683311518416873493 4844547969530227425790945)
    ·
      refine ⟨3633410977147670569343209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4844547969530227425790945 3633410977147670569343209)
      ·
        refine ⟨2725058232860752927007407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3633410977147670569343209 2725058232860752927007407)
        ·
          refine ⟨4087587349291129390511111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725058232860752927007407 4087587349291129390511111)
          ·
            refine ⟨6131381023936694085766667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4087587349291129390511111 6131381023936694085766667)
            ·
              refine ⟨9197071535905041128650001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131381023936694085766667 9197071535905041128650001)
              ·
                refine ⟨6897803651928780846487501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9197071535905041128650001 6897803651928780846487501)
                ·
                  refine ⟨2586676369473292817432813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6897803651928780846487501 2586676369473292817432813)
                  ·
                    refine ⟨970003638552484806537305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2586676369473292817432813 970003638552484806537305)
                    ·
                      rfl

theorem cell22_2833613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2833613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833613 prefixEnd_2833613 := by exact prefixLift 2833613
  have htrace : WordTrace (prefixWord ++ tailWord_2833613) baseStart_2833613 baseEnd_2833613 := by
    simpa [prefixWord, tailWord_2833613, baseEnd_2833613] using wordTrace_append hprefix tailTrace_2833613
  have hstable : (prefixWord ++ tailWord_2833613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833613).length < 2 ^ (prefixWord ++ tailWord_2833613).sum := by decide
  have hdescent : baseEnd_2833613 < baseStart_2833613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833804 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_2833804 : Nat := 118140960795 + 2833804 * 2 ^ 59
def prefixEnd_2833804 : Nat := 4983230072969 + 3 ^ 40 * 2833804 * 2
def baseEnd_2833804 : Nat := 970069021755823975011719

theorem tailTrace_2833804 : CollatzResearch.WordTrace tailWord_2833804 prefixEnd_2833804 970069021755823975011719 := by
  unfold tailWord_2833804
  simp only [CollatzResearch.WordTrace]
  refine ⟨51678661512809779018538233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68904882017079705358050977 51678661512809779018538233)
  ·
    refine ⟨38758996134607334263903675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51678661512809779018538233 38758996134607334263903675)
    ·
      refine ⟨58138494201911001395855513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38758996134607334263903675 58138494201911001395855513)
      ·
        refine ⟨43603870651433251046891635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58138494201911001395855513 43603870651433251046891635)
        ·
          refine ⟨65405805977149876570337453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43603870651433251046891635 65405805977149876570337453)
          ·
            refine ⟨24527177241431203713876545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65405805977149876570337453 24527177241431203713876545)
            ·
              refine ⟨18395382931073402785407409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24527177241431203713876545 18395382931073402785407409)
              ·
                refine ⟨13796537198305052089055557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18395382931073402785407409 13796537198305052089055557)
                ·
                  refine ⟨2586850724682197266697917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13796537198305052089055557 2586850724682197266697917)
                  ·
                    refine ⟨970069021755823975011719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2586850724682197266697917 970069021755823975011719)
                    ·
                      rfl

theorem cell22_2833804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_2833804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833804 prefixEnd_2833804 := by exact prefixLift 2833804
  have htrace : WordTrace (prefixWord ++ tailWord_2833804) baseStart_2833804 baseEnd_2833804 := by
    simpa [prefixWord, tailWord_2833804, baseEnd_2833804] using wordTrace_append hprefix tailTrace_2833804
  have hstable : (prefixWord ++ tailWord_2833804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833804).length < 2 ^ (prefixWord ++ tailWord_2833804).sum := by decide
  have hdescent : baseEnd_2833804 < baseStart_2833804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833817 : List Nat := [1, 2, 1, 2, 1, 6, 9]
def baseStart_2833817 : Nat := 118140960795 + 2833817 * 2 ^ 59
def prefixEnd_2833817 : Nat := 4983230072969 + 3 ^ 40 * 2833817 * 2
def baseEnd_2833817 : Nat := 35928647108203565719877

theorem tailTrace_2833817 : CollatzResearch.WordTrace tailWord_2833817 prefixEnd_2833817 35928647108203565719877 := by
  unfold tailWord_2833817
  simp only [CollatzResearch.WordTrace]
  refine ⟨103357797174572461257299705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68905198116381640838199803 103357797174572461257299705)
  ·
    refine ⟨77518347880929345942974779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103357797174572461257299705 77518347880929345942974779)
    ·
      refine ⟨116277521821394018914462169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77518347880929345942974779 116277521821394018914462169)
      ·
        refine ⟨87208141366045514185846627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116277521821394018914462169 87208141366045514185846627)
        ·
          refine ⟨130812212049068271278769941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87208141366045514185846627 130812212049068271278769941)
          ·
            refine ⟨6131822439800075216192341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130812212049068271278769941 6131822439800075216192341)
            ·
              refine ⟨35928647108203565719877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6131822439800075216192341 35928647108203565719877)
              ·
                rfl

theorem cell22_2833817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 9].length) (baseStart_2833817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833817 prefixEnd_2833817 := by exact prefixLift 2833817
  have htrace : WordTrace (prefixWord ++ tailWord_2833817) baseStart_2833817 baseEnd_2833817 := by
    simpa [prefixWord, tailWord_2833817, baseEnd_2833817] using wordTrace_append hprefix tailTrace_2833817
  have hstable : (prefixWord ++ tailWord_2833817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833817).length < 2 ^ (prefixWord ++ tailWord_2833817).sum := by decide
  have hdescent : baseEnd_2833817 < baseStart_2833817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833821 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2833821 : Nat := 118140960795 + 2833821 * 2 ^ 59
def prefixEnd_2833821 : Nat := 4983230072969 + 3 ^ 40 * 2833821 * 2
def baseEnd_2833821 : Nat := 970074841203241597336667

theorem tailTrace_2833821 : CollatzResearch.WordTrace tailWord_2833821 prefixEnd_2833821 970074841203241597336667 := by
  unfold tailWord_2833821
  simp only [CollatzResearch.WordTrace]
  refine ⟨103357943066557969940445317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68905295377705313293630211 103357943066557969940445317)
  ·
    refine ⟨19379614324979619363833497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103357943066557969940445317 19379614324979619363833497)
    ·
      refine ⟨14534710743734714522875123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19379614324979619363833497 14534710743734714522875123)
      ·
        refine ⟨21802066115602071784312685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14534710743734714522875123 21802066115602071784312685)
        ·
          refine ⟨8175774793350776919117257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21802066115602071784312685 8175774793350776919117257)
          ·
            refine ⟨6131831095013082689337943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8175774793350776919117257 6131831095013082689337943)
            ·
              refine ⟨9197746642519624034006915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131831095013082689337943 9197746642519624034006915)
              ·
                refine ⟨13796619963779436051010373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197746642519624034006915 13796619963779436051010373)
                ·
                  refine ⟨2586866243208644259564445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13796619963779436051010373 2586866243208644259564445)
                  ·
                    refine ⟨970074841203241597336667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2586866243208644259564445 970074841203241597336667)
                    ·
                      rfl

theorem cell22_2833821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2833821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833821 prefixEnd_2833821 := by exact prefixLift 2833821
  have htrace : WordTrace (prefixWord ++ tailWord_2833821) baseStart_2833821 baseEnd_2833821 := by
    simpa [prefixWord, tailWord_2833821, baseEnd_2833821] using wordTrace_append hprefix tailTrace_2833821
  have hstable : (prefixWord ++ tailWord_2833821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833821).length < 2 ^ (prefixWord ++ tailWord_2833821).sum := by decide
  have hdescent : baseEnd_2833821 < baseStart_2833821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833934 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 1, 3]
def baseStart_2833934 : Nat := 118140960795 + 2833934 * 2 ^ 59
def prefixEnd_2833934 : Nat := 4983230072969 + 3 ^ 40 * 2833934 * 2
def baseEnd_2833934 : Nat := 970113523412546969261321

theorem tailTrace_2833934 : CollatzResearch.WordTrace tailWord_2833934 prefixEnd_2833934 970113523412546969261321 := by
  unfold tailWord_2833934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12920258064393573779913607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68908043010099060159539237 12920258064393573779913607)
  ·
    refine ⟨19380387096590360669870411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12920258064393573779913607 19380387096590360669870411)
    ·
      refine ⟨29070580644885541004805617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19380387096590360669870411 29070580644885541004805617)
      ·
        refine ⟨21802935483664155753604213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29070580644885541004805617 21802935483664155753604213)
        ·
          refine ⟨2044025201593514601900395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21802935483664155753604213 2044025201593514601900395)
          ·
            refine ⟨3066037802390271902850593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044025201593514601900395 3066037802390271902850593)
            ·
              refine ⟨2299528351792703927137945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066037802390271902850593 2299528351792703927137945)
              ·
                refine ⟨1724646263844527945353459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299528351792703927137945 1724646263844527945353459)
                ·
                  refine ⟨2586969395766791918030189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724646263844527945353459 2586969395766791918030189)
                  ·
                    refine ⟨970113523412546969261321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2586969395766791918030189 970113523412546969261321)
                    ·
                      rfl

theorem cell22_2833934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_2833934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833934 prefixEnd_2833934 := by exact prefixLift 2833934
  have htrace : WordTrace (prefixWord ++ tailWord_2833934) baseStart_2833934 baseEnd_2833934 := by
    simpa [prefixWord, tailWord_2833934, baseEnd_2833934] using wordTrace_append hprefix tailTrace_2833934
  have hstable : (prefixWord ++ tailWord_2833934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833934).length < 2 ^ (prefixWord ++ tailWord_2833934).sum := by decide
  have hdescent : baseEnd_2833934 < baseStart_2833934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2833971 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 2, 4]
def baseStart_2833971 : Nat := 118140960795 + 2833971 * 2 ^ 59
def prefixEnd_2833971 : Nat := 4983230072969 + 3 ^ 40 * 2833971 * 2
def baseEnd_2833971 : Nat := 970126189268691206086207

theorem tailTrace_2833971 : CollatzResearch.WordTrace tailWord_2833971 prefixEnd_2833971 970126189268691206086207 := by
  unfold tailWord_2833971
  simp only [CollatzResearch.WordTrace]
  refine ⟨103363414016014545558405767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68908942677343030372270511 103363414016014545558405767)
  ·
    refine ⟨155045121024021818337608651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103363414016014545558405767 155045121024021818337608651)
    ·
      refine ⟨232567681536032727506412977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155045121024021818337608651 232567681536032727506412977)
      ·
        refine ⟨174425761152024545629809733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232567681536032727506412977 174425761152024545629809733)
        ·
          refine ⟨32704830216004602305589325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174425761152024545629809733 32704830216004602305589325)
          ·
            refine ⟨12264311331001725864595997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32704830216004602305589325 12264311331001725864595997)
            ·
              refine ⟨4599116749125647199223499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12264311331001725864595997 4599116749125647199223499)
              ·
                refine ⟨6898675123688470798835249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599116749125647199223499 6898675123688470798835249)
                ·
                  refine ⟨5174006342766353099126437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6898675123688470798835249 5174006342766353099126437)
                  ·
                    refine ⟨970126189268691206086207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174006342766353099126437 970126189268691206086207)
                    ·
                      rfl

theorem cell22_2833971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].length) (baseStart_2833971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2833971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2833971 prefixEnd_2833971 := by exact prefixLift 2833971
  have htrace : WordTrace (prefixWord ++ tailWord_2833971) baseStart_2833971 baseEnd_2833971 := by
    simpa [prefixWord, tailWord_2833971, baseEnd_2833971] using wordTrace_append hprefix tailTrace_2833971
  have hstable : (prefixWord ++ tailWord_2833971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2833971).length < 2 ^ (prefixWord ++ tailWord_2833971).sum := by decide
  have hdescent : baseEnd_2833971 < baseStart_2833971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2833971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834052 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_2834052 : Nat := 118140960795 + 2834052 * 2 ^ 59
def prefixEnd_2834052 : Nat := 4983230072969 + 3 ^ 40 * 2834052 * 2
def baseEnd_2834052 : Nat := 970153917224033994810959

theorem tailTrace_2834052 : CollatzResearch.WordTrace tailWord_2834052 prefixEnd_2834052 970153917224033994810959 := by
  unfold tailWord_2834052
  simp only [CollatzResearch.WordTrace]
  refine ⟨51683184164360548196052205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68910912219147397594736273 51683184164360548196052205)
  ·
    refine ⟨19381194061635205573519577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51683184164360548196052205 19381194061635205573519577)
    ·
      refine ⟨14535895546226404180139683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19381194061635205573519577 14535895546226404180139683)
      ·
        refine ⟨21803843319339606270209525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14535895546226404180139683 21803843319339606270209525)
        ·
          refine ⟨2044110311188088087832143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21803843319339606270209525 2044110311188088087832143)
          ·
            refine ⟨3066165466782132131748215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044110311188088087832143 3066165466782132131748215)
            ·
              refine ⟨4599248200173198197622323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3066165466782132131748215 4599248200173198197622323)
              ·
                refine ⟨6898872300259797296433485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599248200173198197622323 6898872300259797296433485)
                ·
                  refine ⟨2587077112597423986162557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6898872300259797296433485 2587077112597423986162557)
                  ·
                    refine ⟨970153917224033994810959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587077112597423986162557 970153917224033994810959)
                    ·
                      rfl

theorem cell22_2834052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_2834052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834052 prefixEnd_2834052 := by exact prefixLift 2834052
  have htrace : WordTrace (prefixWord ++ tailWord_2834052) baseStart_2834052 baseEnd_2834052 := by
    simpa [prefixWord, tailWord_2834052, baseEnd_2834052] using wordTrace_append hprefix tailTrace_2834052
  have hstable : (prefixWord ++ tailWord_2834052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834052).length < 2 ^ (prefixWord ++ tailWord_2834052).sum := by decide
  have hdescent : baseEnd_2834052 < baseStart_2834052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834110 : List Nat := [4, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2834110 : Nat := 118140960795 + 2834110 * 2 ^ 59
def prefixEnd_2834110 : Nat := 4983230072969 + 3 ^ 40 * 2834110 * 2
def baseEnd_2834110 : Nat := 323391257269780392286927

theorem tailTrace_2834110 : CollatzResearch.WordTrace tailWord_2834110 prefixEnd_2834110 323391257269780392286927 := by
  unfold tailWord_2834110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921060470313871537214473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68912322508340648198477189 12921060470313871537214473)
  ·
    refine ⟨9690795352735403652910855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12921060470313871537214473 9690795352735403652910855)
    ·
      refine ⟨14536193029103105479366283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690795352735403652910855 14536193029103105479366283)
      ·
        refine ⟨21804289543654658219049425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14536193029103105479366283 21804289543654658219049425)
        ·
          refine ⟨16353217157740993664287069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21804289543654658219049425 16353217157740993664287069)
          ·
            refine ⟨6132456434152872624107651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16353217157740993664287069 6132456434152872624107651)
            ·
              refine ⟨9198684651229308936161477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132456434152872624107651 9198684651229308936161477)
              ·
                refine ⟨1724753372105495425530277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9198684651229308936161477 1724753372105495425530277)
                ·
                  refine ⟨323391257269780392286927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1724753372105495425530277 323391257269780392286927)
                  ·
                    rfl

theorem cell22_2834110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2834110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834110 prefixEnd_2834110 := by exact prefixLift 2834110
  have htrace : WordTrace (prefixWord ++ tailWord_2834110) baseStart_2834110 baseEnd_2834110 := by
    simpa [prefixWord, tailWord_2834110, baseEnd_2834110] using wordTrace_append hprefix tailTrace_2834110
  have hstable : (prefixWord ++ tailWord_2834110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834110).length < 2 ^ (prefixWord ++ tailWord_2834110).sum := by decide
  have hdescent : baseEnd_2834110 < baseStart_2834110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834125 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2834125 : Nat := 118140960795 + 2834125 * 2 ^ 59
def prefixEnd_2834125 : Nat := 4983230072969 + 3 ^ 40 * 2834125 * 2
def baseEnd_2834125 : Nat := 970178906615886137735735

theorem tailTrace_2834125 : CollatzResearch.WordTrace tailWord_2834125 prefixEnd_2834125 970178906615886137735735 := by
  unfold tailWord_2834125
  simp only [CollatzResearch.WordTrace]
  refine ⟨103369030857456629859511829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68912687238304419906341219 103369030857456629859511829)
  ·
    refine ⟨4845423321443279524664617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103369030857456629859511829 4845423321443279524664617)
    ·
      refine ⟨3634067491082459643498463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4845423321443279524664617 3634067491082459643498463)
      ·
        refine ⟨5451101236623689465247695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634067491082459643498463 5451101236623689465247695)
        ·
          refine ⟨8176651854935534197871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451101236623689465247695 8176651854935534197871543)
          ·
            refine ⟨12264977782403301296807315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176651854935534197871543 12264977782403301296807315)
            ·
              refine ⟨18397466673604951945210973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12264977782403301296807315 18397466673604951945210973)
              ·
                refine ⟨6899050002601856979454115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18397466673604951945210973 6899050002601856979454115)
                ·
                  refine ⟨10348575003902785469181173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899050002601856979454115 10348575003902785469181173)
                  ·
                    refine ⟨970178906615886137735735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10348575003902785469181173 970178906615886137735735)
                    ·
                      rfl

theorem cell22_2834125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2834125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834125 prefixEnd_2834125 := by exact prefixLift 2834125
  have htrace : WordTrace (prefixWord ++ tailWord_2834125) baseStart_2834125 baseEnd_2834125 := by
    simpa [prefixWord, tailWord_2834125, baseEnd_2834125] using wordTrace_append hprefix tailTrace_2834125
  have hstable : (prefixWord ++ tailWord_2834125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834125).length < 2 ^ (prefixWord ++ tailWord_2834125).sum := by decide
  have hdescent : baseEnd_2834125 < baseStart_2834125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834138 : List Nat := [3, 1, 1, 2, 2, 4, 3, 6]
def baseStart_2834138 : Nat := 118140960795 + 2834138 * 2 ^ 59
def prefixEnd_2834138 : Nat := 4983230072969 + 3 ^ 40 * 2834138 * 2
def baseEnd_2834138 : Nat := 107798150753506493017855

theorem tailTrace_2834138 : CollatzResearch.WordTrace tailWord_2834138 prefixEnd_2834138 107798150753506493017855 := by
  unfold tailWord_2834138
  simp only [CollatzResearch.WordTrace]
  refine ⟨25842376251602383269933767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68913003337606355386490045 25842376251602383269933767)
  ·
    refine ⟨38763564377403574904900651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25842376251602383269933767 38763564377403574904900651)
    ·
      refine ⟨58145346566105362357350977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38763564377403574904900651 58145346566105362357350977)
      ·
        refine ⟨43609009924579021768013233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58145346566105362357350977 43609009924579021768013233)
        ·
          refine ⟨32706757443434266326009925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43609009924579021768013233 32706757443434266326009925)
          ·
            refine ⟨6132517020643924936126861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32706757443434266326009925 6132517020643924936126861)
            ·
              refine ⟨2299693882741471851047573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6132517020643924936126861 2299693882741471851047573)
              ·
                refine ⟨107798150753506493017855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2299693882741471851047573 107798150753506493017855)
                ·
                  rfl

theorem cell22_2834138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_2834138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834138 prefixEnd_2834138 := by exact prefixLift 2834138
  have htrace : WordTrace (prefixWord ++ tailWord_2834138) baseStart_2834138 baseEnd_2834138 := by
    simpa [prefixWord, tailWord_2834138, baseEnd_2834138] using wordTrace_append hprefix tailTrace_2834138
  have hstable : (prefixWord ++ tailWord_2834138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834138).length < 2 ^ (prefixWord ++ tailWord_2834138).sum := by decide
  have hdescent : baseEnd_2834138 < baseStart_2834138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834140 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2834140 : Nat := 118140960795 + 2834140 * 2 ^ 59
def prefixEnd_2834140 : Nat := 4983230072969 + 3 ^ 40 * 2834140 * 2
def baseEnd_2834140 : Nat := 970184041422431098610689

theorem tailTrace_2834140 : CollatzResearch.WordTrace tailWord_2834140 prefixEnd_2834140 970184041422431098610689 := by
  unfold tailWord_2834140
  simp only [CollatzResearch.WordTrace]
  refine ⟨51684788976201143710653937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68913051968268191614205249 51684788976201143710653937)
  ·
    refine ⟨38763591732150857782990453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51684788976201143710653937 38763591732150857782990453)
    ·
      refine ⟨3634086724889142917155355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38763591732150857782990453 3634086724889142917155355)
      ·
        refine ⟨5451130087333714375733033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634086724889142917155355 5451130087333714375733033)
        ·
          refine ⟨4088347565500285781799775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5451130087333714375733033 4088347565500285781799775)
          ·
            refine ⟨6132521348250428672699663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088347565500285781799775 6132521348250428672699663)
            ·
              refine ⟨9198782022375643009049495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132521348250428672699663 9198782022375643009049495)
              ·
                refine ⟨13798173033563464513574243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9198782022375643009049495 13798173033563464513574243)
                ·
                  refine ⟨20697259550345196770361365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13798173033563464513574243 20697259550345196770361365)
                  ·
                    refine ⟨970184041422431098610689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20697259550345196770361365 970184041422431098610689)
                    ·
                      rfl

theorem cell22_2834140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2834140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834140 prefixEnd_2834140 := by exact prefixLift 2834140
  have htrace : WordTrace (prefixWord ++ tailWord_2834140) baseStart_2834140 baseEnd_2834140 := by
    simpa [prefixWord, tailWord_2834140, baseEnd_2834140] using wordTrace_append hprefix tailTrace_2834140
  have hstable : (prefixWord ++ tailWord_2834140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834140).length < 2 ^ (prefixWord ++ tailWord_2834140).sum := by decide
  have hdescent : baseEnd_2834140 < baseStart_2834140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834189 : List Nat := [1, 7, 2, 1, 1, 1, 1, 8]
def baseStart_2834189 : Nat := 118140960795 + 2834189 * 2 ^ 59
def prefixEnd_2834189 : Nat := 4983230072969 + 3 ^ 40 * 2834189 * 2
def baseEnd_2834189 : Nat := 107800090569312367126171

theorem tailTrace_2834189 : CollatzResearch.WordTrace tailWord_2834189 prefixEnd_2834189 107800090569312367126171 := by
  unfold tailWord_2834189
  simp only [CollatzResearch.WordTrace]
  refine ⟨103371365129224768789841621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68914243419483179193227747 103371365129224768789841621)
  ·
    refine ⟨2422766370216205518511913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 103371365129224768789841621 2422766370216205518511913)
    ·
      refine ⟨1817074777662154138883935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2422766370216205518511913 1817074777662154138883935)
      ·
        refine ⟨2725612166493231208325903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817074777662154138883935 2725612166493231208325903)
        ·
          refine ⟨4088418249739846812488855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725612166493231208325903 4088418249739846812488855)
          ·
            refine ⟨6132627374609770218733283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088418249739846812488855 6132627374609770218733283)
            ·
              refine ⟨9198941061914655328099925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132627374609770218733283 9198941061914655328099925)
              ·
                refine ⟨107800090569312367126171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9198941061914655328099925 107800090569312367126171)
                ·
                  rfl

theorem cell22_2834189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 8].length) (baseStart_2834189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834189 prefixEnd_2834189 := by exact prefixLift 2834189
  have htrace : WordTrace (prefixWord ++ tailWord_2834189) baseStart_2834189 baseEnd_2834189 := by
    simpa [prefixWord, tailWord_2834189, baseEnd_2834189] using wordTrace_append hprefix tailTrace_2834189
  have hstable : (prefixWord ++ tailWord_2834189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834189).length < 2 ^ (prefixWord ++ tailWord_2834189).sum := by decide
  have hdescent : baseEnd_2834189 < baseStart_2834189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834211 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 8]
def baseStart_2834211 : Nat := 118140960795 + 2834211 * 2 ^ 59
def prefixEnd_2834211 : Nat := 4983230072969 + 3 ^ 40 * 2834211 * 2
def baseEnd_2834211 : Nat := 323402782057803526695157

theorem tailTrace_2834211 : CollatzResearch.WordTrace tailWord_2834211 prefixEnd_2834211 323402782057803526695157 := by
  unfold tailWord_2834211
  simp only [CollatzResearch.WordTrace]
  refine ⟨103372167535145066547142487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68914778356763377698094991 103372167535145066547142487)
  ·
    refine ⟨155058251302717599820713731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103372167535145066547142487 155058251302717599820713731)
    ·
      refine ⟨232587376954076399731070597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155058251302717599820713731 232587376954076399731070597)
      ·
        refine ⟨43610133178889324949575737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232587376954076399731070597 43610133178889324949575737)
        ·
          refine ⟨32707599884166993712181803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43610133178889324949575737 32707599884166993712181803)
          ·
            refine ⟨49061399826250490568272705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32707599884166993712181803 49061399826250490568272705)
            ·
              refine ⟨36796049869687867926204529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49061399826250490568272705 36796049869687867926204529)
              ·
                refine ⟨27597037402265900944653397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36796049869687867926204529 27597037402265900944653397)
                ·
                  refine ⟨323402782057803526695157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27597037402265900944653397 323402782057803526695157)
                  ·
                    rfl

theorem cell22_2834211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_2834211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834211 prefixEnd_2834211 := by exact prefixLift 2834211
  have htrace : WordTrace (prefixWord ++ tailWord_2834211) baseStart_2834211 baseEnd_2834211 := by
    simpa [prefixWord, tailWord_2834211, baseEnd_2834211] using wordTrace_append hprefix tailTrace_2834211
  have hstable : (prefixWord ++ tailWord_2834211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834211).length < 2 ^ (prefixWord ++ tailWord_2834211).sum := by decide
  have hdescent : baseEnd_2834211 < baseStart_2834211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834260 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2834260 : Nat := 118140960795 + 2834260 * 2 ^ 59
def prefixEnd_2834260 : Nat := 4983230072969 + 3 ^ 40 * 2834260 * 2
def baseEnd_2834260 : Nat := 970225119874790785610321

theorem tailTrace_2834260 : CollatzResearch.WordTrace tailWord_2834260 prefixEnd_2834260 970225119874790785610321 := by
  unfold tailWord_2834260
  simp only [CollatzResearch.WordTrace]
  refine ⟨51686977355983773957838117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68915969807978365277117489 51686977355983773957838117)
  ·
    refine ⟨9691308254246957617094647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51686977355983773957838117 9691308254246957617094647)
    ·
      refine ⟨14536962381370436425641971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9691308254246957617094647 14536962381370436425641971)
      ·
        refine ⟨21805443572055654638462957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14536962381370436425641971 21805443572055654638462957)
        ·
          refine ⟨8177041339520870489423609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21805443572055654638462957 8177041339520870489423609)
          ·
            refine ⟨6132781004640652867067707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8177041339520870489423609 6132781004640652867067707)
            ·
              refine ⟨9199171506960979300601561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132781004640652867067707 9199171506960979300601561)
              ·
                refine ⟨6899378630220734475451171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9199171506960979300601561 6899378630220734475451171)
                ·
                  refine ⟨10349067945331101713176757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899378630220734475451171 10349067945331101713176757)
                  ·
                    refine ⟨970225119874790785610321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10349067945331101713176757 970225119874790785610321)
                    ·
                      rfl

theorem cell22_2834260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2834260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834260 prefixEnd_2834260 := by exact prefixLift 2834260
  have htrace : WordTrace (prefixWord ++ tailWord_2834260) baseStart_2834260 baseEnd_2834260 := by
    simpa [prefixWord, tailWord_2834260, baseEnd_2834260] using wordTrace_append hprefix tailTrace_2834260
  have hstable : (prefixWord ++ tailWord_2834260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834260).length < 2 ^ (prefixWord ++ tailWord_2834260).sum := by decide
  have hdescent : baseEnd_2834260 < baseStart_2834260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834335 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 7]
def baseStart_2834335 : Nat := 118140960795 + 2834335 * 2 ^ 59
def prefixEnd_2834335 : Nat := 4983230072969 + 3 ^ 40 * 2834335 * 2
def baseEnd_2834335 : Nat := 323416931302505196661697

theorem tailTrace_2834335 : CollatzResearch.WordTrace tailWord_2834335 prefixEnd_2834335 323416931302505196661697 := by
  unfold tailWord_2834335
  simp only [CollatzResearch.WordTrace]
  refine ⟨103376690186695835724656459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68917793457797223816437639 103376690186695835724656459)
  ·
    refine ⟨155065035280043753586984689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103376690186695835724656459 155065035280043753586984689)
    ·
      refine ⟨116298776460032815190238517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155065035280043753586984689 116298776460032815190238517)
      ·
        refine ⟨10903010293128076424084861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116298776460032815190238517 10903010293128076424084861)
        ·
          refine ⟨4088628859923028659031823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10903010293128076424084861 4088628859923028659031823)
          ·
            refine ⟨6132943289884542988547735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088628859923028659031823 6132943289884542988547735)
            ·
              refine ⟨9199414934826814482821603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132943289884542988547735 9199414934826814482821603)
              ·
                refine ⟨13799122402240221724232405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199414934826814482821603 13799122402240221724232405)
                ·
                  refine ⟨323416931302505196661697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13799122402240221724232405 323416931302505196661697)
                  ·
                    rfl

theorem cell22_2834335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 7].length) (baseStart_2834335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834335 prefixEnd_2834335 := by exact prefixLift 2834335
  have htrace : WordTrace (prefixWord ++ tailWord_2834335) baseStart_2834335 baseEnd_2834335 := by
    simpa [prefixWord, tailWord_2834335, baseEnd_2834335] using wordTrace_append hprefix tailTrace_2834335
  have hstable : (prefixWord ++ tailWord_2834335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834335).length < 2 ^ (prefixWord ++ tailWord_2834335).sum := by decide
  have hdescent : baseEnd_2834335 < baseStart_2834335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834410 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2834410 : Nat := 118140960795 + 2834410 * 2 ^ 59
def prefixEnd_2834410 : Nat := 4983230072969 + 3 ^ 40 * 2834410 * 2
def baseEnd_2834410 : Nat := 970276467940240394359861

theorem tailTrace_2834410 : CollatzResearch.WordTrace tailWord_2834410 prefixEnd_2834410 970276467940240394359861 := by
  unfold tailWord_2834410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25844856415356030883409171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68919617107616082355757789 25844856415356030883409171)
  ·
    refine ⟨38767284623034046325113757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25844856415356030883409171 38767284623034046325113757)
    ·
      refine ⟨14537731733637767371917659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38767284623034046325113757 14537731733637767371917659)
      ·
        refine ⟨21806597600456651057876489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14537731733637767371917659 21806597600456651057876489)
        ·
          refine ⟨16354948200342488293407367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21806597600456651057876489 16354948200342488293407367)
          ·
            refine ⟨24532422300513732440111051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16354948200342488293407367 24532422300513732440111051)
            ·
              refine ⟨36798633450770598660166577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24532422300513732440111051 36798633450770598660166577)
              ·
                refine ⟨27598975088077948995124933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36798633450770598660166577 27598975088077948995124933)
                ·
                  refine ⟨5174807829014615436585925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27598975088077948995124933 5174807829014615436585925)
                  ·
                    refine ⟨970276467940240394359861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174807829014615436585925 970276467940240394359861)
                    ·
                      rfl

theorem cell22_2834410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2834410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834410 prefixEnd_2834410 := by exact prefixLift 2834410
  have htrace : WordTrace (prefixWord ++ tailWord_2834410) baseStart_2834410 baseEnd_2834410 := by
    simpa [prefixWord, tailWord_2834410, baseEnd_2834410] using wordTrace_append hprefix tailTrace_2834410
  have hstable : (prefixWord ++ tailWord_2834410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834410).length < 2 ^ (prefixWord ++ tailWord_2834410).sum := by decide
  have hdescent : baseEnd_2834410 < baseStart_2834410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834474 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2834474 : Nat := 118140960795 + 2834474 * 2 ^ 59
def prefixEnd_2834474 : Nat := 4983230072969 + 3 ^ 40 * 2834474 * 2
def baseEnd_2834474 : Nat := 970298376448165560759665

theorem tailTrace_2834474 : CollatzResearch.WordTrace tailWord_2834474 prefixEnd_2834474 970298376448165560759665 := by
  unfold tailWord_2834474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25845439983298065615991619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68921173288794841642644317 25845439983298065615991619)
  ·
    refine ⟨38768159974947098423987429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25845439983298065615991619 38768159974947098423987429)
    ·
      refine ⟨7269029995302580954497643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38768159974947098423987429 7269029995302580954497643)
      ·
        refine ⟨10903544992953871431746465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269029995302580954497643 10903544992953871431746465)
        ·
          refine ⟨8177658744715403573809849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10903544992953871431746465 8177658744715403573809849)
          ·
            refine ⟨6133244058536552680357387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8177658744715403573809849 6133244058536552680357387)
            ·
              refine ⟨9199866087804829020536081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133244058536552680357387 9199866087804829020536081)
              ·
                refine ⟨6899899565853621765402061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9199866087804829020536081 6899899565853621765402061)
                ·
                  refine ⟨2587462337195108162025773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6899899565853621765402061 2587462337195108162025773)
                  ·
                    refine ⟨970298376448165560759665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587462337195108162025773 970298376448165560759665)
                    ·
                      rfl

theorem cell22_2834474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2834474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834474 prefixEnd_2834474 := by exact prefixLift 2834474
  have htrace : WordTrace (prefixWord ++ tailWord_2834474) baseStart_2834474 baseEnd_2834474 := by
    simpa [prefixWord, tailWord_2834474, baseEnd_2834474] using wordTrace_append hprefix tailTrace_2834474
  have hstable : (prefixWord ++ tailWord_2834474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834474).length < 2 ^ (prefixWord ++ tailWord_2834474).sum := by decide
  have hdescent : baseEnd_2834474 < baseStart_2834474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834545 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2834545 : Nat := 118140960795 + 2834545 * 2 ^ 59
def prefixEnd_2834545 : Nat := 4983230072969 + 3 ^ 40 * 2834545 * 2
def baseEnd_2834545 : Nat := 970322681199145042234447

theorem tailTrace_2834545 : CollatzResearch.WordTrace tailWord_2834545 prefixEnd_2834545 970322681199145042234447 := by
  unfold tailWord_2834545
  simp only [CollatzResearch.WordTrace]
  refine ⟨103384349515935041589801089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68922899677290027726534059 103384349515935041589801089)
  ·
    refine ⟨77538262136951281192350817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103384349515935041589801089 77538262136951281192350817)
    ·
      refine ⟨58153696602713460894263113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77538262136951281192350817 58153696602713460894263113)
      ·
        refine ⟨43615272452035095670697335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58153696602713460894263113 43615272452035095670697335)
        ·
          refine ⟨65422908678052643506046003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43615272452035095670697335 65422908678052643506046003)
          ·
            refine ⟨98134363017078965259069005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65422908678052643506046003 98134363017078965259069005)
            ·
              refine ⟨36800386131404611972150877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98134363017078965259069005 36800386131404611972150877)
              ·
                refine ⟨13800144799276729489556579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36800386131404611972150877 13800144799276729489556579)
                ·
                  refine ⟨20700217198915094234334869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13800144799276729489556579 20700217198915094234334869)
                  ·
                    refine ⟨970322681199145042234447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20700217198915094234334869 970322681199145042234447)
                    ·
                      rfl

theorem cell22_2834545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2834545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834545 prefixEnd_2834545 := by exact prefixLift 2834545
  have htrace : WordTrace (prefixWord ++ tailWord_2834545) baseStart_2834545 baseEnd_2834545 := by
    simpa [prefixWord, tailWord_2834545, baseEnd_2834545] using wordTrace_append hprefix tailTrace_2834545
  have hstable : (prefixWord ++ tailWord_2834545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834545).length < 2 ^ (prefixWord ++ tailWord_2834545).sum := by decide
  have hdescent : baseEnd_2834545 < baseStart_2834545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834564 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_2834564 : Nat := 118140960795 + 2834564 * 2 ^ 59
def prefixEnd_2834564 : Nat := 4983230072969 + 3 ^ 40 * 2834564 * 2
def baseEnd_2834564 : Nat := 970329185287435326009389

theorem tailTrace_2834564 : CollatzResearch.WordTrace tailWord_2834564 prefixEnd_2834564 970329185287435326009389 := by
  unfold tailWord_2834564
  simp only [CollatzResearch.WordTrace]
  refine ⟨51692521251433103917371373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68923361668577471889828497 51692521251433103917371373)
  ·
    refine ⟨19384695469287413969014265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51692521251433103917371373 19384695469287413969014265)
    ·
      refine ⟨14538521601965560476760699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19384695469287413969014265 14538521601965560476760699)
      ·
        refine ⟨21807782402948340715141049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14538521601965560476760699 21807782402948340715141049)
        ·
          refine ⟨16355836802211255536355787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21807782402948340715141049 16355836802211255536355787)
          ·
            refine ⟨24533755203316883304533681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16355836802211255536355787 24533755203316883304533681)
            ·
              refine ⟨18400316402487662478400261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24533755203316883304533681 18400316402487662478400261)
              ·
                refine ⟨3450059325466436714700049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18400316402487662478400261 3450059325466436714700049)
                ·
                  refine ⟨2587544494099827536025037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450059325466436714700049 2587544494099827536025037)
                  ·
                    refine ⟨970329185287435326009389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587544494099827536025037 970329185287435326009389)
                    ·
                      rfl

theorem cell22_2834564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_2834564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834564 prefixEnd_2834564 := by exact prefixLift 2834564
  have htrace : WordTrace (prefixWord ++ tailWord_2834564) baseStart_2834564 baseEnd_2834564 := by
    simpa [prefixWord, tailWord_2834564, baseEnd_2834564] using wordTrace_append hprefix tailTrace_2834564
  have hstable : (prefixWord ++ tailWord_2834564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834564).length < 2 ^ (prefixWord ++ tailWord_2834564).sum := by decide
  have hdescent : baseEnd_2834564 < baseStart_2834564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834684 : List Nat := [2, 2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_2834684 : Nat := 118140960795 + 2834684 * 2 ^ 59
def prefixEnd_2834684 : Nat := 4983230072969 + 3 ^ 40 * 2834684 * 2
def baseEnd_2834684 : Nat := 323456754579931671003007

theorem tailTrace_2834684 : CollatzResearch.WordTrace tailWord_2834684 prefixEnd_2834684 323456754579931671003007 := by
  unfold tailWord_2834684
  simp only [CollatzResearch.WordTrace]
  refine ⟨51694709631215734164555553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68926279508287645552740737 51694709631215734164555553)
  ·
    refine ⟨38771032223411800623416665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51694709631215734164555553 38771032223411800623416665)
    ·
      refine ⟨29078274167558850467562499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38771032223411800623416665 29078274167558850467562499)
      ·
        refine ⟨43617411251338275701343749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29078274167558850467562499 43617411251338275701343749)
        ·
          refine ⟨8178264609625926694001953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43617411251338275701343749 8178264609625926694001953)
          ·
            refine ⟨6133698457219445020501465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8178264609625926694001953 6133698457219445020501465)
            ·
              refine ⟨4600273842914583765376099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6133698457219445020501465 4600273842914583765376099)
              ·
                refine ⟨6900410764371875648064149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600273842914583765376099 6900410764371875648064149)
                ·
                  refine ⟨323456754579931671003007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6900410764371875648064149 323456754579931671003007)
                  ·
                    rfl

theorem cell22_2834684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_2834684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834684 prefixEnd_2834684 := by exact prefixLift 2834684
  have htrace : WordTrace (prefixWord ++ tailWord_2834684) baseStart_2834684 baseEnd_2834684 := by
    simpa [prefixWord, tailWord_2834684, baseEnd_2834684] using wordTrace_append hprefix tailTrace_2834684
  have hstable : (prefixWord ++ tailWord_2834684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834684).length < 2 ^ (prefixWord ++ tailWord_2834684).sum := by decide
  have hdescent : baseEnd_2834684 < baseStart_2834684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834697 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_2834697 : Nat := 118140960795 + 2834697 * 2 ^ 59
def prefixEnd_2834697 : Nat := 4983230072969 + 3 ^ 40 * 2834697 * 2
def baseEnd_2834697 : Nat := 970374713905467312433981

theorem tailTrace_2834697 : CollatzResearch.WordTrace tailWord_2834697 prefixEnd_2834697 970374713905467312433981 := by
  unfold tailWord_2834697
  simp only [CollatzResearch.WordTrace]
  refine ⟨103389893411384371549334345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68926595607589581032889563 103389893411384371549334345)
  ·
    refine ⟨77542420058538278662000759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103389893411384371549334345 77542420058538278662000759)
    ·
      refine ⟨116313630087807417993001139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77542420058538278662000759 116313630087807417993001139)
      ·
        refine ⟨174470445131711126989501709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116313630087807417993001139 174470445131711126989501709)
        ·
          refine ⟨65426416924391672621063141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174470445131711126989501709 65426416924391672621063141)
          ·
            refine ⟨12267453173323438616449339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65426416924391672621063141 12267453173323438616449339)
            ·
              refine ⟨18401179759985157924674009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12267453173323438616449339 18401179759985157924674009)
              ·
                refine ⟨13800884819988868443505507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18401179759985157924674009 13800884819988868443505507)
                ·
                  refine ⟨20701327229983302665258261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13800884819988868443505507 20701327229983302665258261)
                  ·
                    refine ⟨970374713905467312433981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20701327229983302665258261 970374713905467312433981)
                    ·
                      rfl

theorem cell22_2834697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_2834697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834697 prefixEnd_2834697 := by exact prefixLift 2834697
  have htrace : WordTrace (prefixWord ++ tailWord_2834697) baseStart_2834697 baseEnd_2834697 := by
    simpa [prefixWord, tailWord_2834697, baseEnd_2834697] using wordTrace_append hprefix tailTrace_2834697
  have hstable : (prefixWord ++ tailWord_2834697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834697).length < 2 ^ (prefixWord ++ tailWord_2834697).sum := by decide
  have hdescent : baseEnd_2834697 < baseStart_2834697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834712 : List Nat := [2, 1, 2, 3, 1, 2, 3, 8]
def baseStart_2834712 : Nat := 118140960795 + 2834712 * 2 ^ 59
def prefixEnd_2834712 : Nat := 4983230072969 + 3 ^ 40 * 2834712 * 2
def baseEnd_2834712 : Nat := 107819983190223585923215

theorem tailTrace_2834712 : CollatzResearch.WordTrace tailWord_2834712 prefixEnd_2834712 107819983190223585923215 := by
  unfold tailWord_2834712
  simp only [CollatzResearch.WordTrace]
  refine ⟨51695220253165014555565195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68926960337553352740753593 51695220253165014555565195)
  ·
    refine ⟨77542830379747521833347793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51695220253165014555565195 77542830379747521833347793)
    ·
      refine ⟨58157122784810641375010845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77542830379747521833347793 58157122784810641375010845)
      ·
        refine ⟨21808921044303990515629067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58157122784810641375010845 21808921044303990515629067)
        ·
          refine ⟨32713381566455985773443601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21808921044303990515629067 32713381566455985773443601)
          ·
            refine ⟨24535036174841989330082701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32713381566455985773443601 24535036174841989330082701)
            ·
              refine ⟨9200638565565745998781013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24535036174841989330082701 9200638565565745998781013)
              ·
                refine ⟨107819983190223585923215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9200638565565745998781013 107819983190223585923215)
                ·
                  rfl

theorem cell22_2834712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_2834712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834712 prefixEnd_2834712 := by exact prefixLift 2834712
  have htrace : WordTrace (prefixWord ++ tailWord_2834712) baseStart_2834712 baseEnd_2834712 := by
    simpa [prefixWord, tailWord_2834712, baseEnd_2834712] using wordTrace_append hprefix tailTrace_2834712
  have hstable : (prefixWord ++ tailWord_2834712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834712).length < 2 ^ (prefixWord ++ tailWord_2834712).sum := by decide
  have hdescent : baseEnd_2834712 < baseStart_2834712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834750 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2834750 : Nat := 118140960795 + 2834750 * 2 ^ 59
def prefixEnd_2834750 : Nat := 4983230072969 + 3 ^ 40 * 2834750 * 2
def baseEnd_2834750 : Nat := 970392856888592840858819

theorem tailTrace_2834750 : CollatzResearch.WordTrace tailWord_2834750 prefixEnd_2834750 970392856888592840858819 := by
  unfold tailWord_2834750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12923978310024045200126713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68927884320128241067342469 12923978310024045200126713)
  ·
    refine ⟨9692983732518033900095035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12923978310024045200126713 9692983732518033900095035)
    ·
      refine ⟨14539475598777050850142553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9692983732518033900095035 14539475598777050850142553)
      ·
        refine ⟨10904606699082788137606915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14539475598777050850142553 10904606699082788137606915)
        ·
          refine ⟨16356910048624182206410373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10904606699082788137606915 16356910048624182206410373)
          ·
            refine ⟨3066920634117034163701945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16356910048624182206410373 3066920634117034163701945)
            ·
              refine ⟨2300190475587775622776459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066920634117034163701945 2300190475587775622776459)
              ·
                refine ⟨3450285713381663434164689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300190475587775622776459 3450285713381663434164689)
                ·
                  refine ⟨2587714285036247575623517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450285713381663434164689 2587714285036247575623517)
                  ·
                    refine ⟨970392856888592840858819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587714285036247575623517 970392856888592840858819)
                    ·
                      rfl

theorem cell22_2834750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2834750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834750 prefixEnd_2834750 := by exact prefixLift 2834750
  have htrace : WordTrace (prefixWord ++ tailWord_2834750) baseStart_2834750 baseEnd_2834750 := by
    simpa [prefixWord, tailWord_2834750, baseEnd_2834750] using wordTrace_append hprefix tailTrace_2834750
  have hstable : (prefixWord ++ tailWord_2834750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834750).length < 2 ^ (prefixWord ++ tailWord_2834750).sum := by decide
  have hdescent : baseEnd_2834750 < baseStart_2834750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834791 : List Nat := [1, 1, 5, 1, 3, 2, 2, 2, 5]
def baseStart_2834791 : Nat := 118140960795 + 2834791 * 2 ^ 59
def prefixEnd_2834791 : Nat := 4983230072969 + 3 ^ 40 * 2834791 * 2
def baseEnd_2834791 : Nat := 323468964008827466861231

theorem tailTrace_2834791 : CollatzResearch.WordTrace tailWord_2834791 prefixEnd_2834791 323468964008827466861231 := by
  unfold tailWord_2834791
  simp only [CollatzResearch.WordTrace]
  refine ⟨103393321873043825603256227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68928881248695883735504151 103393321873043825603256227)
  ·
    refine ⟨155089982809565738404884341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103393321873043825603256227 155089982809565738404884341)
    ·
      refine ⟨14539685888396787975457907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155089982809565738404884341 14539685888396787975457907)
      ·
        refine ⟨21809528832595181963186861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14539685888396787975457907 21809528832595181963186861)
        ·
          refine ⟨8178573312223193236195073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21809528832595181963186861 8178573312223193236195073)
          ·
            refine ⟨6133929984167394927146305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8178573312223193236195073 6133929984167394927146305)
            ·
              refine ⟨4600447488125546195359729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6133929984167394927146305 4600447488125546195359729)
              ·
                refine ⟨3450335616094159646519797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4600447488125546195359729 3450335616094159646519797)
                ·
                  refine ⟨323468964008827466861231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3450335616094159646519797 323468964008827466861231)
                  ·
                    rfl

theorem cell22_2834791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 2, 5].length) (baseStart_2834791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834791 prefixEnd_2834791 := by exact prefixLift 2834791
  have htrace : WordTrace (prefixWord ++ tailWord_2834791) baseStart_2834791 baseEnd_2834791 := by
    simpa [prefixWord, tailWord_2834791, baseEnd_2834791] using wordTrace_append hprefix tailTrace_2834791
  have hstable : (prefixWord ++ tailWord_2834791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834791).length < 2 ^ (prefixWord ++ tailWord_2834791).sum := by decide
  have hdescent : baseEnd_2834791 < baseStart_2834791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834851 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 4, 3]
def baseStart_2834851 : Nat := 118140960795 + 2834851 * 2 ^ 59
def prefixEnd_2834851 : Nat := 4983230072969 + 3 ^ 40 * 2834851 * 2
def baseEnd_2834851 : Nat := 970427431252662244083509

theorem tailTrace_2834851 : CollatzResearch.WordTrace tailWord_2834851 prefixEnd_2834851 970427431252662244083509 := by
  unfold tailWord_2834851
  simp only [CollatzResearch.WordTrace]
  refine ⟨103395510252826455850440407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68930340168550970566960271 103395510252826455850440407)
  ·
    refine ⟨155093265379239683775660611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103395510252826455850440407 155093265379239683775660611)
    ·
      refine ⟨232639898068859525663490917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155093265379239683775660611 232639898068859525663490917)
      ·
        refine ⟨43619980887911161061904547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232639898068859525663490917 43619980887911161061904547)
        ·
          refine ⟨65429971331866741592856821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43619980887911161061904547 65429971331866741592856821)
          ·
            refine ⟨6134059812362507024330327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65429971331866741592856821 6134059812362507024330327)
            ·
              refine ⟨9201089718543760536495491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134059812362507024330327 9201089718543760536495491)
              ·
                refine ⟨13801634577815640804743237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201089718543760536495491 13801634577815640804743237)
                ·
                  refine ⟨2587806483340432650889357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13801634577815640804743237 2587806483340432650889357)
                  ·
                    refine ⟨970427431252662244083509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587806483340432650889357 970427431252662244083509)
                    ·
                      rfl

theorem cell22_2834851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 3].length) (baseStart_2834851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834851 prefixEnd_2834851 := by exact prefixLift 2834851
  have htrace : WordTrace (prefixWord ++ tailWord_2834851) baseStart_2834851 baseEnd_2834851 := by
    simpa [prefixWord, tailWord_2834851, baseEnd_2834851] using wordTrace_append hprefix tailTrace_2834851
  have hstable : (prefixWord ++ tailWord_2834851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834851).length < 2 ^ (prefixWord ++ tailWord_2834851).sum := by decide
  have hdescent : baseEnd_2834851 < baseStart_2834851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834894 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2834894 : Nat := 118140960795 + 2834894 * 2 ^ 59
def prefixEnd_2834894 : Nat := 4983230072969 + 3 ^ 40 * 2834894 * 2
def baseEnd_2834894 : Nat := 970442151031424465258377

theorem tailTrace_2834894 : CollatzResearch.WordTrace tailWord_2834894 prefixEnd_2834894 970442151031424465258377 := by
  unfold tailWord_2834894
  simp only [CollatzResearch.WordTrace]
  refine ⟨12924634823958834274281967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68931385727780449462837157 12924634823958834274281967)
  ·
    refine ⟨19386952235938251411422951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12924634823958834274281967 19386952235938251411422951)
    ·
      refine ⟨29080428353907377117134427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19386952235938251411422951 29080428353907377117134427)
      ·
        refine ⟨43620642530861065675701641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29080428353907377117134427 43620642530861065675701641)
        ·
          refine ⟨32715481898145799256776231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43620642530861065675701641 32715481898145799256776231)
          ·
            refine ⟨49073222847218698885164347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32715481898145799256776231 49073222847218698885164347)
            ·
              refine ⟨73609834270828048327746521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49073222847218698885164347 73609834270828048327746521)
              ·
                refine ⟨55207375703121036245809891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73609834270828048327746521 55207375703121036245809891)
                ·
                  refine ⟨82811063554681554368714837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55207375703121036245809891 82811063554681554368714837)
                  ·
                    refine ⟨970442151031424465258377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82811063554681554368714837 970442151031424465258377)
                    ·
                      rfl

theorem cell22_2834894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2834894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834894 prefixEnd_2834894 := by exact prefixLift 2834894
  have htrace : WordTrace (prefixWord ++ tailWord_2834894) baseStart_2834894 baseEnd_2834894 := by
    simpa [prefixWord, tailWord_2834894, baseEnd_2834894] using wordTrace_append hprefix tailTrace_2834894
  have hstable : (prefixWord ++ tailWord_2834894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834894).length < 2 ^ (prefixWord ++ tailWord_2834894).sum := by decide
  have hdescent : baseEnd_2834894 < baseStart_2834894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834898 : List Nat := [3, 2, 2, 4, 1, 2, 8]
def baseStart_2834898 : Nat := 118140960795 + 2834898 * 2 ^ 59
def prefixEnd_2834898 : Nat := 4983230072969 + 3 ^ 40 * 2834898 * 2
def baseEnd_2834898 : Nat := 35942352604191473635495

theorem tailTrace_2834898 : CollatzResearch.WordTrace tailWord_2834898 prefixEnd_2834898 35942352604191473635495 := by
  unfold tailWord_2834898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25849306120914045719350337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68931482989104121918267565 25849306120914045719350337)
  ·
    refine ⟨19386979590685534289512753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25849306120914045719350337 19386979590685534289512753)
    ·
      refine ⟨14540234693014150717134565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19386979590685534289512753 14540234693014150717134565)
      ·
        refine ⟨2726294004940153259462731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14540234693014150717134565 2726294004940153259462731)
        ·
          refine ⟨4089441007410229889194097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726294004940153259462731 4089441007410229889194097)
          ·
            refine ⟨3067080755557672416895573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4089441007410229889194097 3067080755557672416895573)
            ·
              refine ⟨35942352604191473635495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3067080755557672416895573 35942352604191473635495)
              ·
                rfl

theorem cell22_2834898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 8].length) (baseStart_2834898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834898 prefixEnd_2834898 := by exact prefixLift 2834898
  have htrace : WordTrace (prefixWord ++ tailWord_2834898) baseStart_2834898 baseEnd_2834898 := by
    simpa [prefixWord, tailWord_2834898, baseEnd_2834898] using wordTrace_append hprefix tailTrace_2834898
  have hstable : (prefixWord ++ tailWord_2834898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834898).length < 2 ^ (prefixWord ++ tailWord_2834898).sum := by decide
  have hdescent : baseEnd_2834898 < baseStart_2834898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834924 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_2834924 : Nat := 118140960795 + 2834924 * 2 ^ 59
def prefixEnd_2834924 : Nat := 4983230072969 + 3 ^ 40 * 2834924 * 2
def baseEnd_2834924 : Nat := 970452420644514387008285

theorem tailTrace_2834924 : CollatzResearch.WordTrace tailWord_2834924 prefixEnd_2834924 970452420644514387008285 := by
  unfold tailWord_2834924
  simp only [CollatzResearch.WordTrace]
  refine ⟨51699086390780994658923913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68932115187707992878565217 51699086390780994658923913)
  ·
    refine ⟨38774314793085745994192935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51699086390780994658923913 38774314793085745994192935)
    ·
      refine ⟨58161472189628618991289403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38774314793085745994192935 58161472189628618991289403)
      ·
        refine ⟨87242208284442928486934105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58161472189628618991289403 87242208284442928486934105)
        ·
          refine ⟨65431656213332196365200579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87242208284442928486934105 65431656213332196365200579)
          ·
            refine ⟨98147484319998294547800869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65431656213332196365200579 98147484319998294547800869)
            ·
              refine ⟨18402653309999680227712663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98147484319998294547800869 18402653309999680227712663)
              ·
                refine ⟨27603979964999520341568995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18402653309999680227712663 27603979964999520341568995)
                ·
                  refine ⟨41405969947499280512353493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27603979964999520341568995 41405969947499280512353493)
                  ·
                    refine ⟨970452420644514387008285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41405969947499280512353493 970452420644514387008285)
                    ·
                      rfl

theorem cell22_2834924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_2834924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834924 prefixEnd_2834924 := by exact prefixLift 2834924
  have htrace : WordTrace (prefixWord ++ tailWord_2834924) baseStart_2834924 baseEnd_2834924 := by
    simpa [prefixWord, tailWord_2834924, baseEnd_2834924] using wordTrace_append hprefix tailTrace_2834924
  have hstable : (prefixWord ++ tailWord_2834924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834924).length < 2 ^ (prefixWord ++ tailWord_2834924).sum := by decide
  have hdescent : baseEnd_2834924 < baseStart_2834924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2834964 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2834964 : Nat := 118140960795 + 2834964 * 2 ^ 59
def prefixEnd_2834964 : Nat := 4983230072969 + 3 ^ 40 * 2834964 * 2
def baseEnd_2834964 : Nat := 970466113461967616008163

theorem tailTrace_2834964 : CollatzResearch.WordTrace tailWord_2834964 prefixEnd_2834964 970466113461967616008163 := by
  unfold tailWord_2834964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51699815850708538074651973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68933087800944717432869297 51699815850708538074651973)
  ·
    refine ⟨9693715472007850888997245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51699815850708538074651973 9693715472007850888997245)
    ·
      refine ⟨3635143302002944083373967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9693715472007850888997245 3635143302002944083373967)
      ·
        refine ⟨5452714953004416125060951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635143302002944083373967 5452714953004416125060951)
        ·
          refine ⟨8179072429506624187591427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452714953004416125060951 8179072429506624187591427)
          ·
            refine ⟨12268608644259936281387141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8179072429506624187591427 12268608644259936281387141)
            ·
              refine ⟨2300364120798738052760089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12268608644259936281387141 2300364120798738052760089)
              ·
                refine ⟨1725273090599053539570067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300364120798738052760089 1725273090599053539570067)
                ·
                  refine ⟨2587909635898580309355101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725273090599053539570067 2587909635898580309355101)
                  ·
                    refine ⟨970466113461967616008163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587909635898580309355101 970466113461967616008163)
                    ·
                      rfl

theorem cell22_2834964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2834964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2834964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2834964 prefixEnd_2834964 := by exact prefixLift 2834964
  have htrace : WordTrace (prefixWord ++ tailWord_2834964) baseStart_2834964 baseEnd_2834964 := by
    simpa [prefixWord, tailWord_2834964, baseEnd_2834964] using wordTrace_append hprefix tailTrace_2834964
  have hstable : (prefixWord ++ tailWord_2834964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2834964).length < 2 ^ (prefixWord ++ tailWord_2834964).sum := by decide
  have hdescent : baseEnd_2834964 < baseStart_2834964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2834964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835001 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_2835001 : Nat := 118140960795 + 2835001 * 2 ^ 59
def prefixEnd_2835001 : Nat := 4983230072969 + 3 ^ 40 * 2835001 * 2
def baseEnd_2835001 : Nat := 970478779318111852833049

theorem tailTrace_2835001 : CollatzResearch.WordTrace tailWord_2835001 prefixEnd_2835001 970478779318111852833049 := by
  unfold tailWord_2835001
  simp only [CollatzResearch.WordTrace]
  refine ⟨103400981202283031468400857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68933987468188687645600571 103400981202283031468400857)
  ·
    refine ⟨77550735901712273601300643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103400981202283031468400857 77550735901712273601300643)
    ·
      refine ⟨116326103852568410401950965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77550735901712273601300643 116326103852568410401950965)
      ·
        refine ⟨10905572236178288475182903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116326103852568410401950965 10905572236178288475182903)
        ·
          refine ⟨16358358354267432712774355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10905572236178288475182903 16358358354267432712774355)
          ·
            refine ⟨24537537531401149069161533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16358358354267432712774355 24537537531401149069161533)
            ·
              refine ⟨9201576574275430900935575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24537537531401149069161533 9201576574275430900935575)
              ·
                refine ⟨13802364861413146351403363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201576574275430900935575 13802364861413146351403363)
                ·
                  refine ⟨20703547292119719527105045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13802364861413146351403363 20703547292119719527105045)
                  ·
                    refine ⟨970478779318111852833049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20703547292119719527105045 970478779318111852833049)
                    ·
                      rfl

theorem cell22_2835001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_2835001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835001 prefixEnd_2835001 := by exact prefixLift 2835001
  have htrace : WordTrace (prefixWord ++ tailWord_2835001) baseStart_2835001 baseEnd_2835001 := by
    simpa [prefixWord, tailWord_2835001, baseEnd_2835001] using wordTrace_append hprefix tailTrace_2835001
  have hstable : (prefixWord ++ tailWord_2835001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835001).length < 2 ^ (prefixWord ++ tailWord_2835001).sum := by decide
  have hdescent : baseEnd_2835001 < baseStart_2835001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835005 : List Nat := [1, 4, 1, 3, 2, 2, 2, 3, 4]
def baseStart_2835005 : Nat := 118140960795 + 2835005 * 2 ^ 59
def prefixEnd_2835005 : Nat := 4983230072969 + 3 ^ 40 * 2835005 * 2
def baseEnd_2835005 : Nat := 323493382866619058577679

theorem tailTrace_2835005 : CollatzResearch.WordTrace tailWord_2835005 prefixEnd_2835005 323493382866619058577679 := by
  unfold tailWord_2835005
  simp only [CollatzResearch.WordTrace]
  refine ⟨103401127094268540151546469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68934084729512360101030979 103401127094268540151546469)
  ·
    refine ⟨19387711330175351278414963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103401127094268540151546469 19387711330175351278414963)
    ·
      refine ⟨29081566995263026917622445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19387711330175351278414963 29081566995263026917622445)
      ·
        refine ⟨10905587623223635094108417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29081566995263026917622445 10905587623223635094108417)
        ·
          refine ⟨8179190717417726320581313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10905587623223635094108417 8179190717417726320581313)
          ·
            refine ⟨6134393038063294740435985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8179190717417726320581313 6134393038063294740435985)
            ·
              refine ⟨4600794778547471055326989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6134393038063294740435985 4600794778547471055326989)
              ·
                refine ⟨1725298041955301645747621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4600794778547471055326989 1725298041955301645747621)
                ·
                  refine ⟨323493382866619058577679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725298041955301645747621 323493382866619058577679)
                  ·
                    rfl

theorem cell22_2835005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_2835005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835005 prefixEnd_2835005 := by exact prefixLift 2835005
  have htrace : WordTrace (prefixWord ++ tailWord_2835005) baseStart_2835005 baseEnd_2835005 := by
    simpa [prefixWord, tailWord_2835005, baseEnd_2835005] using wordTrace_append hprefix tailTrace_2835005
  have hstable : (prefixWord ++ tailWord_2835005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835005).length < 2 ^ (prefixWord ++ tailWord_2835005).sum := by decide
  have hdescent : baseEnd_2835005 < baseStart_2835005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835082 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 3, 3]
def baseStart_2835082 : Nat := 118140960795 + 2835082 * 2 ^ 59
def prefixEnd_2835082 : Nat := 4983230072969 + 3 ^ 40 * 2835082 * 2
def baseEnd_2835082 : Nat := 970506507273454641557801

theorem tailTrace_2835082 : CollatzResearch.WordTrace tailWord_2835082 prefixEnd_2835082 970506507273454641557801 := by
  unfold tailWord_2835082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25850983878747395575524875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68935957009993054868066333 25850983878747395575524875)
  ·
    refine ⟨38776475818121093363287313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25850983878747395575524875 38776475818121093363287313)
    ·
      refine ⟨29082356863590820022465485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38776475818121093363287313 29082356863590820022465485)
      ·
        refine ⟨10905883823846557508424557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29082356863590820022465485 10905883823846557508424557)
        ·
          refine ⟨4089706433942459065659209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10905883823846557508424557 4089706433942459065659209)
          ·
            refine ⟨3067279825456844299244407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4089706433942459065659209 3067279825456844299244407)
            ·
              refine ⟨4600919738185266448866611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067279825456844299244407 4600919738185266448866611)
              ·
                refine ⟨6901379607277899673299917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600919738185266448866611 6901379607277899673299917)
                ·
                  refine ⟨2588017352729212377487469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6901379607277899673299917 2588017352729212377487469)
                  ·
                    refine ⟨970506507273454641557801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588017352729212377487469 970506507273454641557801)
                    ·
                      rfl

theorem cell22_2835082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_2835082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835082 prefixEnd_2835082 := by exact prefixLift 2835082
  have htrace : WordTrace (prefixWord ++ tailWord_2835082) baseStart_2835082 baseEnd_2835082 := by
    simpa [prefixWord, tailWord_2835082, baseEnd_2835082] using wordTrace_append hprefix tailTrace_2835082
  have hstable : (prefixWord ++ tailWord_2835082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835082).length < 2 ^ (prefixWord ++ tailWord_2835082).sum := by decide
  have hdescent : baseEnd_2835082 < baseStart_2835082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835091 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 5, 4]
def baseStart_2835091 : Nat := 118140960795 + 2835091 * 2 ^ 59
def prefixEnd_2835091 : Nat := 4983230072969 + 3 ^ 40 * 2835091 * 2
def baseEnd_2835091 : Nat := 970509588157381618082773

theorem tailTrace_2835091 : CollatzResearch.WordTrace tailWord_2835091 prefixEnd_2835091 970509588157381618082773 := by
  unfold tailWord_2835091
  simp only [CollatzResearch.WordTrace]
  refine ⟨103404263771956976839177127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68936175847971317892784751 103404263771956976839177127)
  ·
    refine ⟨155106395657935465258765691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103404263771956976839177127 155106395657935465258765691)
    ·
      refine ⟨232659593486903197888148537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155106395657935465258765691 232659593486903197888148537)
      ·
        refine ⟨174494695115177398416111403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232659593486903197888148537 174494695115177398416111403)
        ·
          refine ⟨261742042672766097624167105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174494695115177398416111403 261742042672766097624167105)
          ·
            refine ⟨196306532004574573218125329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261742042672766097624167105 196306532004574573218125329)
            ·
              refine ⟨147229899003430929913593997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196306532004574573218125329 147229899003430929913593997)
              ·
                refine ⟨55211212126286598717597749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147229899003430929913593997 55211212126286598717597749)
                ·
                  refine ⟨5176051136839368629774789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55211212126286598717597749 5176051136839368629774789)
                  ·
                    refine ⟨970509588157381618082773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176051136839368629774789 970509588157381618082773)
                    ·
                      rfl

theorem cell22_2835091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 4].length) (baseStart_2835091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835091 prefixEnd_2835091 := by exact prefixLift 2835091
  have htrace : WordTrace (prefixWord ++ tailWord_2835091) baseStart_2835091 baseEnd_2835091 := by
    simpa [prefixWord, tailWord_2835091, baseEnd_2835091] using wordTrace_append hprefix tailTrace_2835091
  have hstable : (prefixWord ++ tailWord_2835091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835091).length < 2 ^ (prefixWord ++ tailWord_2835091).sum := by decide
  have hdescent : baseEnd_2835091 < baseStart_2835091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835108 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2835108 : Nat := 118140960795 + 2835108 * 2 ^ 59
def prefixEnd_2835108 : Nat := 4983230072969 + 3 ^ 40 * 2835108 * 2
def baseEnd_2835108 : Nat := 970515407604799240407721

theorem tailTrace_2835108 : CollatzResearch.WordTrace tailWord_2835108 prefixEnd_2835108 970515407604799240407721 := by
  unfold tailWord_2835108
  simp only [CollatzResearch.WordTrace]
  refine ⟨51702441906447694371272989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68936589208596925828363985 51702441906447694371272989)
  ·
    refine ⟨19388415714917885389227371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51702441906447694371272989 19388415714917885389227371)
    ·
      refine ⟨29082623572376828083841057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19388415714917885389227371 29082623572376828083841057)
      ·
        refine ⟨21811967679282621062880793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29082623572376828083841057 21811967679282621062880793)
        ·
          refine ⟨16358975759461965797160595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21811967679282621062880793 16358975759461965797160595)
          ·
            refine ⟨24538463639192948695740893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16358975759461965797160595 24538463639192948695740893)
            ·
              refine ⟨9201923864697355760902835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24538463639192948695740893 9201923864697355760902835)
              ·
                refine ⟨13802885797046033641354253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201923864697355760902835 13802885797046033641354253)
                ·
                  refine ⟨5176082173892262615507845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13802885797046033641354253 5176082173892262615507845)
                  ·
                    refine ⟨970515407604799240407721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176082173892262615507845 970515407604799240407721)
                    ·
                      rfl

theorem cell22_2835108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2835108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835108 prefixEnd_2835108 := by exact prefixLift 2835108
  have htrace : WordTrace (prefixWord ++ tailWord_2835108) baseStart_2835108 baseEnd_2835108 := by
    simpa [prefixWord, tailWord_2835108, baseEnd_2835108] using wordTrace_append hprefix tailTrace_2835108
  have hstable : (prefixWord ++ tailWord_2835108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835108).length < 2 ^ (prefixWord ++ tailWord_2835108).sum := by decide
  have hdescent : baseEnd_2835108 < baseStart_2835108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835234 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2835234 : Nat := 118140960795 + 2835234 * 2 ^ 59
def prefixEnd_2835234 : Nat := 4983230072969 + 3 ^ 40 * 2835234 * 2
def baseEnd_2835234 : Nat := 970558539979776911757335

theorem tailTrace_2835234 : CollatzResearch.WordTrace tailWord_2835234 prefixEnd_2835234 970558539979776911757335 := by
  unfold tailWord_2835234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25852369852609728065408189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68939652940292608174421837 25852369852609728065408189)
  ·
    refine ⟨9694638694728648024528071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25852369852609728065408189 9694638694728648024528071)
    ·
      refine ⟨14541958042092972036792107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9694638694728648024528071 14541958042092972036792107)
      ·
        refine ⟨21812937063139458055188161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14541958042092972036792107 21812937063139458055188161)
        ·
          refine ⟨16359702797354593541391121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21812937063139458055188161 16359702797354593541391121)
          ·
            refine ⟨12269777098015945156043341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16359702797354593541391121 12269777098015945156043341)
            ·
              refine ⟨4601166411755979433516253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12269777098015945156043341 4601166411755979433516253)
              ·
                refine ⟨1725437404408492287568595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4601166411755979433516253 1725437404408492287568595)
                ·
                  refine ⟨2588156106612738431352893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725437404408492287568595 2588156106612738431352893)
                  ·
                    refine ⟨970558539979776911757335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588156106612738431352893 970558539979776911757335)
                    ·
                      rfl

theorem cell22_2835234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2835234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835234 prefixEnd_2835234 := by exact prefixLift 2835234
  have htrace : WordTrace (prefixWord ++ tailWord_2835234) baseStart_2835234 baseEnd_2835234 := by
    simpa [prefixWord, tailWord_2835234, baseEnd_2835234] using wordTrace_append hprefix tailTrace_2835234
  have hstable : (prefixWord ++ tailWord_2835234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835234).length < 2 ^ (prefixWord ++ tailWord_2835234).sum := by decide
  have hdescent : baseEnd_2835234 < baseStart_2835234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835288 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_2835288 : Nat := 118140960795 + 2835288 * 2 ^ 59
def prefixEnd_2835288 : Nat := 4983230072969 + 3 ^ 40 * 2835288 * 2
def baseEnd_2835288 : Nat := 970577025283338770907169

theorem tailTrace_2835288 : CollatzResearch.WordTrace tailWord_2835288 prefixEnd_2835288 970577025283338770907169 := by
  unfold tailWord_2835288
  simp only [CollatzResearch.WordTrace]
  refine ⟨51705724476121639742049259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68940965968162186322732345 51705724476121639742049259)
  ·
    refine ⟨77558586714182459613073889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51705724476121639742049259 77558586714182459613073889)
    ·
      refine ⟨58168940035636844709805417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77558586714182459613073889 58168940035636844709805417)
      ·
        refine ⟨43626705026727633532354063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58168940035636844709805417 43626705026727633532354063)
        ·
          refine ⟨65440057540091450298531095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43626705026727633532354063 65440057540091450298531095)
          ·
            refine ⟨98160086310137175447796643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65440057540091450298531095 98160086310137175447796643)
            ·
              refine ⟨147240129465205763171694965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98160086310137175447796643 147240129465205763171694965)
              ·
                refine ⟨13803762137363040297346403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147240129465205763171694965 13803762137363040297346403)
                ·
                  refine ⟨20705643206044560446019605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13803762137363040297346403 20705643206044560446019605)
                  ·
                    refine ⟨970577025283338770907169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20705643206044560446019605 970577025283338770907169)
                    ·
                      rfl

theorem cell22_2835288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_2835288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835288 prefixEnd_2835288 := by exact prefixLift 2835288
  have htrace : WordTrace (prefixWord ++ tailWord_2835288) baseStart_2835288 baseEnd_2835288 := by
    simpa [prefixWord, tailWord_2835288, baseEnd_2835288] using wordTrace_append hprefix tailTrace_2835288
  have hstable : (prefixWord ++ tailWord_2835288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835288).length < 2 ^ (prefixWord ++ tailWord_2835288).sum := by decide
  have hdescent : baseEnd_2835288 < baseStart_2835288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835290 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_2835290 : Nat := 118140960795 + 2835290 * 2 ^ 59
def prefixEnd_2835290 : Nat := 4983230072969 + 3 ^ 40 * 2835290 * 2
def baseEnd_2835290 : Nat := 970577709924211432357163

theorem tailTrace_2835290 : CollatzResearch.WordTrace tailWord_2835290 prefixEnd_2835290 970577709924211432357163 := by
  unfold tailWord_2835290
  simp only [CollatzResearch.WordTrace]
  refine ⟨25852880474559008456417831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68941014598824022550447549 25852880474559008456417831)
  ·
    refine ⟨38779320711838512684626747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25852880474559008456417831 38779320711838512684626747)
    ·
      refine ⟨58168981067757769026940121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38779320711838512684626747 58168981067757769026940121)
      ·
        refine ⟨43626735800818326770205091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58168981067757769026940121 43626735800818326770205091)
        ·
          refine ⟨65440103701227490155307637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43626735800818326770205091 65440103701227490155307637)
          ·
            refine ⟨6135009721990077202060091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65440103701227490155307637 6135009721990077202060091)
            ·
              refine ⟨9202514582985115803090137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6135009721990077202060091 9202514582985115803090137)
              ·
                refine ⟨6901885937238836852317603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9202514582985115803090137 6901885937238836852317603)
                ·
                  refine ⟨10352828905858255278476405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901885937238836852317603 10352828905858255278476405)
                  ·
                    refine ⟨970577709924211432357163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10352828905858255278476405 970577709924211432357163)
                    ·
                      rfl

theorem cell22_2835290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_2835290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835290 prefixEnd_2835290 := by exact prefixLift 2835290
  have htrace : WordTrace (prefixWord ++ tailWord_2835290) baseStart_2835290 baseEnd_2835290 := by
    simpa [prefixWord, tailWord_2835290, baseEnd_2835290] using wordTrace_append hprefix tailTrace_2835290
  have hstable : (prefixWord ++ tailWord_2835290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835290).length < 2 ^ (prefixWord ++ tailWord_2835290).sum := by decide
  have hdescent : baseEnd_2835290 < baseStart_2835290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835303 : List Nat := [1, 1, 5, 1, 2, 12]
def baseStart_2835303 : Nat := 118140960795 + 2835303 * 2 ^ 59
def prefixEnd_2835303 : Nat := 4983230072969 + 3 ^ 40 * 2835303 * 2
def baseEnd_2835303 : Nat := 11982495803578811503483

theorem tailTrace_2835303 : CollatzResearch.WordTrace tailWord_2835303 prefixEnd_2835303 11982495803578811503483 := by
  unfold tailWord_2835303
  simp only [CollatzResearch.WordTrace]
  refine ⟨103411996047188937045894563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68941330698125958030596375 103411996047188937045894563)
  ·
    refine ⟨155117994070783405568841845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103411996047188937045894563 155117994070783405568841845)
    ·
      refine ⟨14542311944135944272078923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155117994070783405568841845 14542311944135944272078923)
      ·
        refine ⟨21813467916203916408118385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14542311944135944272078923 21813467916203916408118385)
        ·
          refine ⟨16360100937152937306088789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21813467916203916408118385 16360100937152937306088789)
          ·
            refine ⟨11982495803578811503483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16360100937152937306088789 11982495803578811503483)
            ·
              rfl

theorem cell22_2835303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 12].length) (baseStart_2835303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835303 prefixEnd_2835303 := by exact prefixLift 2835303
  have htrace : WordTrace (prefixWord ++ tailWord_2835303) baseStart_2835303 baseEnd_2835303 := by
    simpa [prefixWord, tailWord_2835303, baseEnd_2835303] using wordTrace_append hprefix tailTrace_2835303
  have hstable : (prefixWord ++ tailWord_2835303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835303).length < 2 ^ (prefixWord ++ tailWord_2835303).sum := by decide
  have hdescent : baseEnd_2835303 < baseStart_2835303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835440 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_2835440 : Nat := 118140960795 + 2835440 * 2 ^ 59
def prefixEnd_2835440 : Nat := 4983230072969 + 3 ^ 40 * 2835440 * 2
def baseEnd_2835440 : Nat := 970629057989661041106703

theorem tailTrace_2835440 : CollatzResearch.WordTrace tailWord_2835440 prefixEnd_2835440 970629057989661041106703 := by
  unfold tailWord_2835440
  simp only [CollatzResearch.WordTrace]
  refine ⟨51708496423846304721815887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68944661898461739629087849 51708496423846304721815887)
  ·
    refine ⟨77562744635769457082723831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51708496423846304721815887 77562744635769457082723831)
    ·
      refine ⟨116344116953654185624085747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77562744635769457082723831 116344116953654185624085747)
      ·
        refine ⟨174516175430481278436128621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116344116953654185624085747 174516175430481278436128621)
        ·
          refine ⟨65443565786430479413548233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174516175430481278436128621 65443565786430479413548233)
          ·
            refine ⟨49082674339822859560161175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65443565786430479413548233 49082674339822859560161175)
            ·
              refine ⟨73624011509734289340241763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49082674339822859560161175 73624011509734289340241763)
              ·
                refine ⟨110436017264601434010362645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73624011509734289340241763 110436017264601434010362645)
                ·
                  refine ⟨5176688309278192219235749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110436017264601434010362645 5176688309278192219235749)
                  ·
                    refine ⟨970629057989661041106703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176688309278192219235749 970629057989661041106703)
                    ·
                      rfl

theorem cell22_2835440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_2835440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835440 prefixEnd_2835440 := by exact prefixLift 2835440
  have htrace : WordTrace (prefixWord ++ tailWord_2835440) baseStart_2835440 baseEnd_2835440 := by
    simpa [prefixWord, tailWord_2835440, baseEnd_2835440] using wordTrace_append hprefix tailTrace_2835440
  have hstable : (prefixWord ++ tailWord_2835440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835440).length < 2 ^ (prefixWord ++ tailWord_2835440).sum := by decide
  have hdescent : baseEnd_2835440 < baseStart_2835440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835446 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2835446 : Nat := 118140960795 + 2835446 * 2 ^ 59
def prefixEnd_2835446 : Nat := 4983230072969 + 3 ^ 40 * 2835446 * 2
def baseEnd_2835446 : Nat := 970631111912279025456685

theorem tailTrace_2835446 : CollatzResearch.WordTrace tailWord_2835446 prefixEnd_2835446 970631111912279025456685 := by
  unfold tailWord_2835446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463575730354429529271887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68944807790447248312233461 6463575730354429529271887)
  ·
    refine ⟨9695363595531644293907831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6463575730354429529271887 9695363595531644293907831)
    ·
      refine ⟨14543045393297466440861747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9695363595531644293907831 14543045393297466440861747)
      ·
        refine ⟨21814568089946199661292621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14543045393297466440861747 21814568089946199661292621)
        ·
          refine ⟨8180463033729824872984733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21814568089946199661292621 8180463033729824872984733)
          ·
            refine ⟨3067673637648684327369275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8180463033729824872984733 3067673637648684327369275)
            ·
              refine ⟨4601510456473026491053913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067673637648684327369275 4601510456473026491053913)
              ·
                refine ⟨3451132842354769868290435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4601510456473026491053913 3451132842354769868290435)
                ·
                  refine ⟨5176699263532154802435653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451132842354769868290435 5176699263532154802435653)
                  ·
                    refine ⟨970631111912279025456685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176699263532154802435653 970631111912279025456685)
                    ·
                      rfl

theorem cell22_2835446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2835446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835446 prefixEnd_2835446 := by exact prefixLift 2835446
  have htrace : WordTrace (prefixWord ++ tailWord_2835446) baseStart_2835446 baseEnd_2835446 := by
    simpa [prefixWord, tailWord_2835446, baseEnd_2835446] using wordTrace_append hprefix tailTrace_2835446
  have hstable : (prefixWord ++ tailWord_2835446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835446).length < 2 ^ (prefixWord ++ tailWord_2835446).sum := by decide
  have hdescent : baseEnd_2835446 < baseStart_2835446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835457 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2835457 : Nat := 118140960795 + 2835457 * 2 ^ 59
def prefixEnd_2835457 : Nat := 4983230072969 + 3 ^ 40 * 2835457 * 2
def baseEnd_2835457 : Nat := 970634877437078663431651

theorem tailTrace_2835457 : CollatzResearch.WordTrace tailWord_2835457 prefixEnd_2835457 970634877437078663431651 := by
  unfold tailWord_2835457
  simp only [CollatzResearch.WordTrace]
  refine ⟨103417612888631021347000625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68945075259087347564667083 103417612888631021347000625)
  ·
    refine ⟨77563209666473266010250469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103417612888631021347000625 77563209666473266010250469)
    ·
      refine ⟨14543101812463737376921963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77563209666473266010250469 14543101812463737376921963)
      ·
        refine ⟨21814652718695606065382945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14543101812463737376921963 21814652718695606065382945)
        ·
          refine ⟨16360989539021704549037209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21814652718695606065382945 16360989539021704549037209)
          ·
            refine ⟨12270742154266278411777907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16360989539021704549037209 12270742154266278411777907)
            ·
              refine ⟨18406113231399417617666861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12270742154266278411777907 18406113231399417617666861)
              ·
                refine ⟨6902292461774781606625073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18406113231399417617666861 6902292461774781606625073)
                ·
                  refine ⟨5176719346331086204968805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6902292461774781606625073 5176719346331086204968805)
                  ·
                    refine ⟨970634877437078663431651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176719346331086204968805 970634877437078663431651)
                    ·
                      rfl

theorem cell22_2835457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2835457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835457 prefixEnd_2835457 := by exact prefixLift 2835457
  have htrace : WordTrace (prefixWord ++ tailWord_2835457) baseStart_2835457 baseEnd_2835457 := by
    simpa [prefixWord, tailWord_2835457, baseEnd_2835457] using wordTrace_append hprefix tailTrace_2835457
  have hstable : (prefixWord ++ tailWord_2835457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835457).length < 2 ^ (prefixWord ++ tailWord_2835457).sum := by decide
  have hdescent : baseEnd_2835457 < baseStart_2835457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835502 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2835502 : Nat := 118140960795 + 2835502 * 2 ^ 59
def prefixEnd_2835502 : Nat := 4983230072969 + 3 ^ 40 * 2835502 * 2
def baseEnd_2835502 : Nat := 970650281856713546056513

theorem tailTrace_2835502 : CollatzResearch.WordTrace tailWord_2835502 prefixEnd_2835502 970650281856713546056513 := by
  unfold tailWord_2835502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12927406771683499254048595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68946169448978662688259173 12927406771683499254048595)
  ·
    refine ⟨19391110157525248881072893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12927406771683499254048595 19391110157525248881072893)
    ·
      refine ⟨7271666309071968330402335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19391110157525248881072893 7271666309071968330402335)
      ·
        refine ⟨10907499463607952495603503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7271666309071968330402335 10907499463607952495603503)
        ·
          refine ⟨16361249195411928743405255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10907499463607952495603503 16361249195411928743405255)
          ·
            refine ⟨24541873793117893115107883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16361249195411928743405255 24541873793117893115107883)
            ·
              refine ⟨36812810689676839672661825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24541873793117893115107883 36812810689676839672661825)
              ·
                refine ⟨27609608017257629754496369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36812810689676839672661825 27609608017257629754496369)
                ·
                  refine ⟨20707206012943222315872277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27609608017257629754496369 20707206012943222315872277)
                  ·
                    refine ⟨970650281856713546056513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20707206012943222315872277 970650281856713546056513)
                    ·
                      rfl

theorem cell22_2835502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2835502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835502 prefixEnd_2835502 := by exact prefixLift 2835502
  have htrace : WordTrace (prefixWord ++ tailWord_2835502) baseStart_2835502 baseEnd_2835502 := by
    simpa [prefixWord, tailWord_2835502, baseEnd_2835502] using wordTrace_append hprefix tailTrace_2835502
  have hstable : (prefixWord ++ tailWord_2835502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835502).length < 2 ^ (prefixWord ++ tailWord_2835502).sum := by decide
  have hdescent : baseEnd_2835502 < baseStart_2835502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835515 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 6, 5]
def baseStart_2835515 : Nat := 118140960795 + 2835515 * 2 ^ 59
def prefixEnd_2835515 : Nat := 4983230072969 + 3 ^ 40 * 2835515 * 2
def baseEnd_2835515 : Nat := 970654732022385845481473

theorem tailTrace_2835515 : CollatzResearch.WordTrace tailWord_2835515 prefixEnd_2835515 970654732022385845481473 := by
  unfold tailWord_2835515
  simp only [CollatzResearch.WordTrace]
  refine ⟨103419728322420897252611999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68946485548280598168407999 103419728322420897252611999)
  ·
    refine ⟨155129592483631345878917999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103419728322420897252611999 155129592483631345878917999)
    ·
      refine ⟨232694388725447018818376999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155129592483631345878917999 232694388725447018818376999)
      ·
        refine ⟨349041583088170528227565499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232694388725447018818376999 349041583088170528227565499)
        ·
          refine ⟨523562374632255792341348249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349041583088170528227565499 523562374632255792341348249)
          ·
            refine ⟨392671780974191844256011187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523562374632255792341348249 392671780974191844256011187)
            ·
              refine ⟨589007671461287766384016781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392671780974191844256011187 589007671461287766384016781)
              ·
                refine ⟨220877876797982912394006293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589007671461287766384016781 220877876797982912394006293)
                ·
                  refine ⟨10353650474905449018469045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220877876797982912394006293 10353650474905449018469045)
                  ·
                    refine ⟨970654732022385845481473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10353650474905449018469045 970654732022385845481473)
                    ·
                      rfl

theorem cell22_2835515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_2835515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835515 prefixEnd_2835515 := by exact prefixLift 2835515
  have htrace : WordTrace (prefixWord ++ tailWord_2835515) baseStart_2835515 baseEnd_2835515 := by
    simpa [prefixWord, tailWord_2835515, baseEnd_2835515] using wordTrace_append hprefix tailTrace_2835515
  have hstable : (prefixWord ++ tailWord_2835515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835515).length < 2 ^ (prefixWord ++ tailWord_2835515).sum := by decide
  have hdescent : baseEnd_2835515 < baseStart_2835515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835564 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_2835564 : Nat := 118140960795 + 2835564 * 2 ^ 59
def prefixEnd_2835564 : Nat := 4983230072969 + 3 ^ 40 * 2835564 * 2
def baseEnd_2835564 : Nat := 970671505723766051006323

theorem tailTrace_2835564 : CollatzResearch.WordTrace tailWord_2835564 prefixEnd_2835564 970671505723766051006323 := by
  unfold tailWord_2835564
  simp only [CollatzResearch.WordTrace]
  refine ⟨51710757749621689310572873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68947676999495585747430497 51710757749621689310572873)
  ·
    refine ⟨38783068312216266982929655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51710757749621689310572873 38783068312216266982929655)
    ·
      refine ⟨58174602468324400474394483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38783068312216266982929655 58174602468324400474394483)
      ·
        refine ⟨87261903702486600711591725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58174602468324400474394483 87261903702486600711591725)
        ·
          refine ⟨32723213888432475266846897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87261903702486600711591725 32723213888432475266846897)
          ·
            refine ⟨24542410416324356450135173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32723213888432475266846897 24542410416324356450135173)
            ·
              refine ⟨4601701953060816834400345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24542410416324356450135173 4601701953060816834400345)
              ·
                refine ⟨3451276464795612625800259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4601701953060816834400345 3451276464795612625800259)
                ·
                  refine ⟨5176914697193418938700389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451276464795612625800259 5176914697193418938700389)
                  ·
                    refine ⟨970671505723766051006323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176914697193418938700389 970671505723766051006323)
                    ·
                      rfl

theorem cell22_2835564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_2835564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835564 prefixEnd_2835564 := by exact prefixLift 2835564
  have htrace : WordTrace (prefixWord ++ tailWord_2835564) baseStart_2835564 baseEnd_2835564 := by
    simpa [prefixWord, tailWord_2835564, baseEnd_2835564] using wordTrace_append hprefix tailTrace_2835564
  have hstable : (prefixWord ++ tailWord_2835564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835564).length < 2 ^ (prefixWord ++ tailWord_2835564).sum := by decide
  have hdescent : baseEnd_2835564 < baseStart_2835564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835594 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 4, 3]
def baseStart_2835594 : Nat := 118140960795 + 2835594 * 2 ^ 59
def prefixEnd_2835594 : Nat := 4983230072969 + 3 ^ 40 * 2835594 * 2
def baseEnd_2835594 : Nat := 970681775336855972756231

theorem tailTrace_2835594 : CollatzResearch.WordTrace tailWord_2835594 prefixEnd_2835594 970681775336855972756231 := by
  unfold tailWord_2835594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25855652422283673436184459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68948406459423129163158557 25855652422283673436184459)
  ·
    refine ⟨38783478633425510154276689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25855652422283673436184459 38783478633425510154276689)
    ·
      refine ⟨29087608975069132615707517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38783478633425510154276689 29087608975069132615707517)
      ·
        refine ⟨10907853365650924730890319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29087608975069132615707517 10907853365650924730890319)
        ·
          refine ⟨16361780048476387096335479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10907853365650924730890319 16361780048476387096335479)
          ·
            refine ⟨24542670072714580644503219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16361780048476387096335479 24542670072714580644503219)
            ·
              refine ⟨36814005109071870966754829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24542670072714580644503219 36814005109071870966754829)
              ·
                refine ⟨13805251915901951612533061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36814005109071870966754829 13805251915901951612533061)
                ·
                  refine ⟨2588484734231615927349949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13805251915901951612533061 2588484734231615927349949)
                  ·
                    refine ⟨970681775336855972756231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588484734231615927349949 970681775336855972756231)
                    ·
                      rfl

theorem cell22_2835594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_2835594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835594 prefixEnd_2835594 := by exact prefixLift 2835594
  have htrace : WordTrace (prefixWord ++ tailWord_2835594) baseStart_2835594 baseEnd_2835594 := by
    simpa [prefixWord, tailWord_2835594, baseEnd_2835594] using wordTrace_append hprefix tailTrace_2835594
  have hstable : (prefixWord ++ tailWord_2835594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835594).length < 2 ^ (prefixWord ++ tailWord_2835594).sum := by decide
  have hdescent : baseEnd_2835594 < baseStart_2835594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835607 : List Nat := [1, 1, 3, 3, 3, 1, 1, 9]
def baseStart_2835607 : Nat := 118140960795 + 2835607 * 2 ^ 59
def prefixEnd_2835607 : Nat := 4983230072969 + 3 ^ 40 * 2835607 * 2
def baseEnd_2835607 : Nat := 107854025055836474686799

theorem tailTrace_2835607 : CollatzResearch.WordTrace tailWord_2835607 prefixEnd_2835607 107854025055836474686799 := by
  unfold tailWord_2835607
  simp only [CollatzResearch.WordTrace]
  refine ⟨103423083838087596964961075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68948722558725064643307383 103423083838087596964961075)
  ·
    refine ⟨155134625757131395447441613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103423083838087596964961075 155134625757131395447441613)
    ·
      refine ⟨58175484658924273292790605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155134625757131395447441613 58175484658924273292790605)
      ·
        refine ⟨21815806747096602484796477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58175484658924273292790605 21815806747096602484796477)
        ·
          refine ⟨8180927530161225931798679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21815806747096602484796477 8180927530161225931798679)
          ·
            refine ⟨12271391295241838897698019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180927530161225931798679 12271391295241838897698019)
            ·
              refine ⟨18407086942862758346547029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12271391295241838897698019 18407086942862758346547029)
              ·
                refine ⟨107854025055836474686799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18407086942862758346547029 107854025055836474686799)
                ·
                  rfl

theorem cell22_2835607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 9].length) (baseStart_2835607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835607 prefixEnd_2835607 := by exact prefixLift 2835607
  have htrace : WordTrace (prefixWord ++ tailWord_2835607) baseStart_2835607 baseEnd_2835607 := by
    simpa [prefixWord, tailWord_2835607, baseEnd_2835607] using wordTrace_append hprefix tailTrace_2835607
  have hstable : (prefixWord ++ tailWord_2835607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835607).length < 2 ^ (prefixWord ++ tailWord_2835607).sum := by decide
  have hdescent : baseEnd_2835607 < baseStart_2835607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835626 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2835626 : Nat := 118140960795 + 2835626 * 2 ^ 59
def prefixEnd_2835626 : Nat := 4983230072969 + 3 ^ 40 * 2835626 * 2
def baseEnd_2835626 : Nat := 970692729590818555956133

theorem tailTrace_2835626 : CollatzResearch.WordTrace tailWord_2835626 prefixEnd_2835626 970692729590818555956133 := by
  unfold tailWord_2835626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25855944206254690802475683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68949184550012508806601821 25855944206254690802475683)
  ·
    refine ⟨38783916309382036203713525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25855944206254690802475683 38783916309382036203713525)
    ·
      refine ⟨3635992154004565894098143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38783916309382036203713525 3635992154004565894098143)
      ·
        refine ⟨5453988231006848841147215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635992154004565894098143 5453988231006848841147215)
        ·
          refine ⟨8180982346510273261720823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453988231006848841147215 8180982346510273261720823)
          ·
            refine ⟨12271473519765409892581235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180982346510273261720823 12271473519765409892581235)
            ·
              refine ⟨18407210279648114838871853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12271473519765409892581235 18407210279648114838871853)
              ·
                refine ⟨6902703854868043064576945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18407210279648114838871853 6902703854868043064576945)
                ·
                  refine ⟨5177027891151032298432709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6902703854868043064576945 5177027891151032298432709)
                  ·
                    refine ⟨970692729590818555956133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5177027891151032298432709 970692729590818555956133)
                    ·
                      rfl

theorem cell22_2835626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2835626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835626 prefixEnd_2835626 := by exact prefixLift 2835626
  have htrace : WordTrace (prefixWord ++ tailWord_2835626) baseStart_2835626 baseEnd_2835626 := by
    simpa [prefixWord, tailWord_2835626, baseEnd_2835626] using wordTrace_append hprefix tailTrace_2835626
  have hstable : (prefixWord ++ tailWord_2835626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835626).length < 2 ^ (prefixWord ++ tailWord_2835626).sum := by decide
  have hdescent : baseEnd_2835626 < baseStart_2835626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835667 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 2, 5]
def baseStart_2835667 : Nat := 118140960795 + 2835667 * 2 ^ 59
def prefixEnd_2835667 : Nat := 4983230072969 + 3 ^ 40 * 2835667 * 2
def baseEnd_2835667 : Nat := 970706764728708115681007

theorem tailTrace_2835667 : CollatzResearch.WordTrace tailWord_2835667 prefixEnd_2835667 970706764728708115681007 := by
  unfold tailWord_2835667
  simp only [CollatzResearch.WordTrace]
  refine ⟨103425272217870227212145255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68950181478580151474763503 103425272217870227212145255)
  ·
    refine ⟨155137908326805340818217883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103425272217870227212145255 155137908326805340818217883)
    ·
      refine ⟨232706862490208011227326825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155137908326805340818217883 232706862490208011227326825)
      ·
        refine ⟨174530146867656008420495119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232706862490208011227326825 174530146867656008420495119)
        ·
          refine ⟨261795220301484012630742679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174530146867656008420495119 261795220301484012630742679)
          ·
            refine ⟨392692830452226018946114019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261795220301484012630742679 392692830452226018946114019)
            ·
              refine ⟨589039245678339028419171029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392692830452226018946114019 589039245678339028419171029)
              ·
                refine ⟨13805607320586070978574321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 589039245678339028419171029 13805607320586070978574321)
                ·
                  refine ⟨10354205490439553233930741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13805607320586070978574321 10354205490439553233930741)
                  ·
                    refine ⟨970706764728708115681007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10354205490439553233930741 970706764728708115681007)
                    ·
                      rfl

theorem cell22_2835667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_2835667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835667 prefixEnd_2835667 := by exact prefixLift 2835667
  have htrace : WordTrace (prefixWord ++ tailWord_2835667) baseStart_2835667 baseEnd_2835667 := by
    simpa [prefixWord, tailWord_2835667, baseEnd_2835667] using wordTrace_append hprefix tailTrace_2835667
  have hstable : (prefixWord ++ tailWord_2835667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835667).length < 2 ^ (prefixWord ++ tailWord_2835667).sum := by decide
  have hdescent : baseEnd_2835667 < baseStart_2835667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835697 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 10]
def baseStart_2835697 : Nat := 118140960795 + 2835697 * 2 ^ 59
def prefixEnd_2835697 : Nat := 4983230072969 + 3 ^ 40 * 2835697 * 2
def baseEnd_2835697 : Nat := 323572344780599345810305

theorem tailTrace_2835697 : CollatzResearch.WordTrace tailWord_2835697 prefixEnd_2835697 323572344780599345810305 := by
  unfold tailWord_2835697
  simp only [CollatzResearch.WordTrace]
  refine ⟨103426366407761542335737345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68950910938507694890491563 103426366407761542335737345)
  ·
    refine ⟨77569774805821156751803009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103426366407761542335737345 77569774805821156751803009)
    ·
      refine ⟨58177331104365867563852257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77569774805821156751803009 58177331104365867563852257)
      ·
        refine ⟨43632998328274400672889193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58177331104365867563852257 43632998328274400672889193)
        ·
          refine ⟨32724748746205800504666895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43632998328274400672889193 32724748746205800504666895)
          ·
            refine ⟨49087123119308700757000343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32724748746205800504666895 49087123119308700757000343)
            ·
              refine ⟨73630684678963051135500515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49087123119308700757000343 73630684678963051135500515)
              ·
                refine ⟨110446027018444576703250773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73630684678963051135500515 110446027018444576703250773)
                ·
                  refine ⟨323572344780599345810305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110446027018444576703250773 323572344780599345810305)
                  ·
                    rfl

theorem cell22_2835697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_2835697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835697 prefixEnd_2835697 := by exact prefixLift 2835697
  have htrace : WordTrace (prefixWord ++ tailWord_2835697) baseStart_2835697 baseEnd_2835697 := by
    simpa [prefixWord, tailWord_2835697, baseEnd_2835697] using wordTrace_append hprefix tailTrace_2835697
  have hstable : (prefixWord ++ tailWord_2835697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835697).length < 2 ^ (prefixWord ++ tailWord_2835697).sum := by decide
  have hdescent : baseEnd_2835697 < baseStart_2835697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835761 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_2835761 : Nat := 118140960795 + 2835761 * 2 ^ 59
def prefixEnd_2835761 : Nat := 4983230072969 + 3 ^ 40 * 2835761 * 2
def baseEnd_2835761 : Nat := 970738942849723203830719

theorem tailTrace_2835761 : CollatzResearch.WordTrace tailWord_2835761 prefixEnd_2835761 970738942849723203830719 := by
  unfold tailWord_2835761
  simp only [CollatzResearch.WordTrace]
  refine ⟨103428700679529681266067137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68952467119686454177378091 103428700679529681266067137)
  ·
    refine ⟨77571525509647260949550353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103428700679529681266067137 77571525509647260949550353)
    ·
      refine ⟨58178644132235445712162765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77571525509647260949550353 58178644132235445712162765)
      ·
        refine ⟨21816991549588292142061037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58178644132235445712162765 21816991549588292142061037)
        ·
          refine ⟨8181371831095609553272889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21816991549588292142061037 8181371831095609553272889)
          ·
            refine ⟨6136028873321707164954667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8181371831095609553272889 6136028873321707164954667)
            ·
              refine ⟨9204043309982560747432001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136028873321707164954667 9204043309982560747432001)
              ·
                refine ⟨6903032482486920560574001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9204043309982560747432001 6903032482486920560574001)
                ·
                  refine ⟨5177274361865190420430501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6903032482486920560574001 5177274361865190420430501)
                  ·
                    refine ⟨970738942849723203830719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5177274361865190420430501 970738942849723203830719)
                    ·
                      rfl

theorem cell22_2835761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_2835761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835761 prefixEnd_2835761 := by exact prefixLift 2835761
  have htrace : WordTrace (prefixWord ++ tailWord_2835761) baseStart_2835761 baseEnd_2835761 := by
    simpa [prefixWord, tailWord_2835761, baseEnd_2835761] using wordTrace_append hprefix tailTrace_2835761
  have hstable : (prefixWord ++ tailWord_2835761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835761).length < 2 ^ (prefixWord ++ tailWord_2835761).sum := by decide
  have hdescent : baseEnd_2835761 < baseStart_2835761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835780 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2835780 : Nat := 118140960795 + 2835780 * 2 ^ 59
def prefixEnd_2835780 : Nat := 4983230072969 + 3 ^ 40 * 2835780 * 2
def baseEnd_2835780 : Nat := 970745446938013487605661

theorem tailTrace_2835780 : CollatzResearch.WordTrace tailWord_2835780 prefixEnd_2835780 970745446938013487605661 := by
  unfold tailWord_2835780
  simp only [CollatzResearch.WordTrace]
  refine ⟨51714696833230423755504397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68952929110973898340672529 51714696833230423755504397)
  ·
    refine ⟨19393011312461408908314149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51714696833230423755504397 19393011312461408908314149)
    ·
      refine ⟨3636189621086514170308903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19393011312461408908314149 3636189621086514170308903)
      ·
        refine ⟨5454284431629771255463355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3636189621086514170308903 5454284431629771255463355)
        ·
          refine ⟨8181426647444656883195033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5454284431629771255463355 8181426647444656883195033)
          ·
            refine ⟨6136069985583492662396275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8181426647444656883195033 6136069985583492662396275)
            ·
              refine ⟨9204104978375238993594413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136069985583492662396275 9204104978375238993594413)
              ·
                refine ⟨3451539366890714622597905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9204104978375238993594413 3451539366890714622597905)
                ·
                  refine ⟨2588654525168035966948429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3451539366890714622597905 2588654525168035966948429)
                  ·
                    refine ⟨970745446938013487605661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588654525168035966948429 970745446938013487605661)
                    ·
                      rfl

theorem cell22_2835780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2835780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835780 prefixEnd_2835780 := by exact prefixLift 2835780
  have htrace : WordTrace (prefixWord ++ tailWord_2835780) baseStart_2835780 baseEnd_2835780 := by
    simpa [prefixWord, tailWord_2835780, baseEnd_2835780] using wordTrace_append hprefix tailTrace_2835780
  have hstable : (prefixWord ++ tailWord_2835780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835780).length < 2 ^ (prefixWord ++ tailWord_2835780).sum := by decide
  have hdescent : baseEnd_2835780 < baseStart_2835780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835821 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 5]
def baseStart_2835821 : Nat := 118140960795 + 2835821 * 2 ^ 59
def prefixEnd_2835821 : Nat := 4983230072969 + 3 ^ 40 * 2835821 * 2
def baseEnd_2835821 : Nat := 323586494025301015776845

theorem tailTrace_2835821 : CollatzResearch.WordTrace tailWord_2835821 prefixEnd_2835821 323586494025301015776845 := by
  unfold tailWord_2835821
  simp only [CollatzResearch.WordTrace]
  refine ⟨103430889059312311513251317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68953926039541541008834211 103430889059312311513251317)
  ·
    refine ⟨9696645849310529204367311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103430889059312311513251317 9696645849310529204367311)
    ·
      refine ⟨14544968773965793806550967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9696645849310529204367311 14544968773965793806550967)
      ·
        refine ⟨21817453160948690709826451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14544968773965793806550967 21817453160948690709826451)
        ·
          refine ⟨32726179741423036064739677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21817453160948690709826451 32726179741423036064739677)
          ·
            refine ⟨12272317403033638524277379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32726179741423036064739677 12272317403033638524277379)
            ·
              refine ⟨18408476104550457786416069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12272317403033638524277379 18408476104550457786416069)
              ·
                refine ⟨3451589269603210834953013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18408476104550457786416069 3451589269603210834953013)
                ·
                  refine ⟨323586494025301015776845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3451589269603210834953013 323586494025301015776845)
                  ·
                    rfl

theorem cell22_2835821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_2835821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835821 prefixEnd_2835821 := by exact prefixLift 2835821
  have htrace : WordTrace (prefixWord ++ tailWord_2835821) baseStart_2835821 baseEnd_2835821 := by
    simpa [prefixWord, tailWord_2835821, baseEnd_2835821] using wordTrace_append hprefix tailTrace_2835821
  have hstable : (prefixWord ++ tailWord_2835821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835821).length < 2 ^ (prefixWord ++ tailWord_2835821).sum := by decide
  have hdescent : baseEnd_2835821 < baseStart_2835821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835825 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 1, 3]
def baseStart_2835825 : Nat := 118140960795 + 2835825 * 2 ^ 59
def prefixEnd_2835825 : Nat := 4983230072969 + 3 ^ 40 * 2835825 * 2
def baseEnd_2835825 : Nat := 970760851357648370230523

theorem tailTrace_2835825 : CollatzResearch.WordTrace tailWord_2835825 prefixEnd_2835825 970760851357648370230523 := by
  unfold tailWord_2835825
  simp only [CollatzResearch.WordTrace]
  refine ⟨103431034951297820196396929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68954023300865213464264619 103431034951297820196396929)
  ·
    refine ⟨77573276213473365147297697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103431034951297820196396929 77573276213473365147297697)
    ·
      refine ⟨58179957160105023860473273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77573276213473365147297697 58179957160105023860473273)
      ·
        refine ⟨43634967870078767895354955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58179957160105023860473273 43634967870078767895354955)
        ·
          refine ⟨65452451805118151843032433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43634967870078767895354955 65452451805118151843032433)
          ·
            refine ⟨49089338853838613882274325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65452451805118151843032433 49089338853838613882274325)
            ·
              refine ⟨2301062758773685025731609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49089338853838613882274325 2301062758773685025731609)
              ·
                refine ⟨1725797069080263769298707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301062758773685025731609 1725797069080263769298707)
                ·
                  refine ⟨2588695603620395653948061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725797069080263769298707 2588695603620395653948061)
                  ·
                    refine ⟨970760851357648370230523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588695603620395653948061 970760851357648370230523)
                    ·
                      rfl

theorem cell22_2835825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_2835825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835825 prefixEnd_2835825 := by exact prefixLift 2835825
  have htrace : WordTrace (prefixWord ++ tailWord_2835825) baseStart_2835825 baseEnd_2835825 := by
    simpa [prefixWord, tailWord_2835825, baseEnd_2835825] using wordTrace_append hprefix tailTrace_2835825
  have hstable : (prefixWord ++ tailWord_2835825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835825).length < 2 ^ (prefixWord ++ tailWord_2835825).sum := by decide
  have hdescent : baseEnd_2835825 < baseStart_2835825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835851 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 1, 4]
def baseStart_2835851 : Nat := 118140960795 + 2835851 * 2 ^ 59
def prefixEnd_2835851 : Nat := 4983230072969 + 3 ^ 40 * 2835851 * 2
def baseEnd_2835851 : Nat := 970769751688992969080443

theorem tailTrace_2835851 : CollatzResearch.WordTrace tailWord_2835851 prefixEnd_2835851 970769751688992969080443 := by
  unfold tailWord_2835851
  simp only [CollatzResearch.WordTrace]
  refine ⟨103431983249203626636843407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68954655499469084424562271 103431983249203626636843407)
  ·
    refine ⟨155147974873805439955265111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103431983249203626636843407 155147974873805439955265111)
    ·
      refine ⟨232721962310708159932897667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155147974873805439955265111 232721962310708159932897667)
      ·
        refine ⟨349082943466062239899346501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232721962310708159932897667 349082943466062239899346501)
        ·
          refine ⟨65453051899886669981127469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349082943466062239899346501 65453051899886669981127469)
          ·
            refine ⟨24544894462457501242922801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65453051899886669981127469 24544894462457501242922801)
            ·
              refine ⟨18408670846843125932192101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24544894462457501242922801 18408670846843125932192101)
              ·
                refine ⟨3451625783783086112286019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18408670846843125932192101 3451625783783086112286019)
                ·
                  refine ⟨5177438675674629168429029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451625783783086112286019 5177438675674629168429029)
                  ·
                    refine ⟨970769751688992969080443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5177438675674629168429029 970769751688992969080443)
                    ·
                      rfl

theorem cell22_2835851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 4].length) (baseStart_2835851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835851 prefixEnd_2835851 := by exact prefixLift 2835851
  have htrace : WordTrace (prefixWord ++ tailWord_2835851) baseStart_2835851 baseEnd_2835851 := by
    simpa [prefixWord, tailWord_2835851, baseEnd_2835851] using wordTrace_append hprefix tailTrace_2835851
  have hstable : (prefixWord ++ tailWord_2835851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835851).length < 2 ^ (prefixWord ++ tailWord_2835851).sum := by decide
  have hdescent : baseEnd_2835851 < baseStart_2835851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2835949 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_2835949 : Nat := 118140960795 + 2835949 * 2 ^ 59
def prefixEnd_2835949 : Nat := 4983230072969 + 3 ^ 40 * 2835949 * 2
def baseEnd_2835949 : Nat := 970803299091753380130143

theorem tailTrace_2835949 : CollatzResearch.WordTrace tailWord_2835949 prefixEnd_2835949 970803299091753380130143 := by
  unfold tailWord_2835949
  simp only [CollatzResearch.WordTrace]
  refine ⟨103435557602848589373910901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68957038401899059582607267 103435557602848589373910901)
  ·
    refine ⟨9697083525267055253804147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103435557602848589373910901 9697083525267055253804147)
    ·
      refine ⟨14545625287900582880706221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9697083525267055253804147 14545625287900582880706221)
      ·
        refine ⟨5454609482962718580264833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14545625287900582880706221 5454609482962718580264833)
        ·
          refine ⟨4090957112222038935198625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5454609482962718580264833 4090957112222038935198625)
          ·
            refine ⟨3068217834166529201398969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4090957112222038935198625 3068217834166529201398969)
            ·
              refine ⟨2301163375624896901049227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3068217834166529201398969 2301163375624896901049227)
              ·
                refine ⟨3451745063437345351573841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301163375624896901049227 3451745063437345351573841)
                ·
                  refine ⟨2588808797578009013680381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3451745063437345351573841 2588808797578009013680381)
                  ·
                    refine ⟨970803299091753380130143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588808797578009013680381 970803299091753380130143)
                    ·
                      rfl

theorem cell22_2835949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_2835949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2835949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2835949 prefixEnd_2835949 := by exact prefixLift 2835949
  have htrace : WordTrace (prefixWord ++ tailWord_2835949) baseStart_2835949 baseEnd_2835949 := by
    simpa [prefixWord, tailWord_2835949, baseEnd_2835949] using wordTrace_append hprefix tailTrace_2835949
  have hstable : (prefixWord ++ tailWord_2835949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2835949).length < 2 ^ (prefixWord ++ tailWord_2835949).sum := by decide
  have hdescent : baseEnd_2835949 < baseStart_2835949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2835949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836033 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2836033 : Nat := 118140960795 + 2836033 * 2 ^ 59
def prefixEnd_2836033 : Nat := 4983230072969 + 3 ^ 40 * 2836033 * 2
def baseEnd_2836033 : Nat := 970832054008405161029885

theorem tailTrace_2836033 : CollatzResearch.WordTrace tailWord_2836033 prefixEnd_2836033 970832054008405161029885 := by
  unfold tailWord_2836033
  simp only [CollatzResearch.WordTrace]
  refine ⟨103438621334544271719968753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68959080889696181146645835 103438621334544271719968753)
  ·
    refine ⟨77578966000908203789976565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103438621334544271719968753 77578966000908203789976565)
    ·
      refine ⟨7273028062585144105310303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77578966000908203789976565 7273028062585144105310303)
      ·
        refine ⟨10909542093877716157965455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273028062585144105310303 10909542093877716157965455)
        ·
          refine ⟨16364313140816574236948183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10909542093877716157965455 16364313140816574236948183)
          ·
            refine ⟨24546469711224861355422275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16364313140816574236948183 24546469711224861355422275)
            ·
              refine ⟨36819704566837292033133413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24546469711224861355422275 36819704566837292033133413)
              ·
                refine ⟨6903694606281992256212515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36819704566837292033133413 6903694606281992256212515)
                ·
                  refine ⟨10355541909422988384318773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903694606281992256212515 10355541909422988384318773)
                  ·
                    refine ⟨970832054008405161029885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10355541909422988384318773 970832054008405161029885)
                    ·
                      rfl

theorem cell22_2836033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2836033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836033 prefixEnd_2836033 := by exact prefixLift 2836033
  have htrace : WordTrace (prefixWord ++ tailWord_2836033) baseStart_2836033 baseEnd_2836033 := by
    simpa [prefixWord, tailWord_2836033, baseEnd_2836033] using wordTrace_append hprefix tailTrace_2836033
  have hstable : (prefixWord ++ tailWord_2836033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836033).length < 2 ^ (prefixWord ++ tailWord_2836033).sum := by decide
  have hdescent : baseEnd_2836033 < baseStart_2836033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836050 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 4, 3]
def baseStart_2836050 : Nat := 118140960795 + 2836050 * 2 ^ 59
def prefixEnd_2836050 : Nat := 4983230072969 + 3 ^ 40 * 2836050 * 2
def baseEnd_2836050 : Nat := 970837873455822783354833

theorem tailTrace_2836050 : CollatzResearch.WordTrace tailWord_2836050 prefixEnd_2836050 970837873455822783354833 := by
  unfold tailWord_2836050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25859810343870670905834401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68959494250321789082225069 25859810343870670905834401)
  ·
    refine ⟨19394857757903003179375801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25859810343870670905834401 19394857757903003179375801)
    ·
      refine ⟨14546143318427252384531851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19394857757903003179375801 14546143318427252384531851)
      ·
        refine ⟨21819214977640878576797777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14546143318427252384531851 21819214977640878576797777)
        ·
          refine ⟨16364411233230658932598333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21819214977640878576797777 16364411233230658932598333)
          ·
            refine ⟨6136654212461497099724375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16364411233230658932598333 6136654212461497099724375)
            ·
              refine ⟨9204981318692245649586563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136654212461497099724375 9204981318692245649586563)
              ·
                refine ⟨13807471978038368474379845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9204981318692245649586563 13807471978038368474379845)
                ·
                  refine ⟨2588900995882194088946221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13807471978038368474379845 2588900995882194088946221)
                  ·
                    refine ⟨970837873455822783354833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588900995882194088946221 970837873455822783354833)
                    ·
                      rfl

theorem cell22_2836050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_2836050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836050 prefixEnd_2836050 := by exact prefixLift 2836050
  have htrace : WordTrace (prefixWord ++ tailWord_2836050) baseStart_2836050 baseEnd_2836050 := by
    simpa [prefixWord, tailWord_2836050, baseEnd_2836050] using wordTrace_append hprefix tailTrace_2836050
  have hstable : (prefixWord ++ tailWord_2836050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836050).length < 2 ^ (prefixWord ++ tailWord_2836050).sum := by decide
  have hdescent : baseEnd_2836050 < baseStart_2836050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836067 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 2, 3]
def baseStart_2836067 : Nat := 118140960795 + 2836067 * 2 ^ 59
def prefixEnd_2836067 : Nat := 4983230072969 + 3 ^ 40 * 2836067 * 2
def baseEnd_2836067 : Nat := 970843692903240405679781

theorem tailTrace_2836067 : CollatzResearch.WordTrace tailWord_2836067 prefixEnd_2836067 970843692903240405679781 := by
  unfold tailWord_2836067
  simp only [CollatzResearch.WordTrace]
  refine ⟨103439861416421095526706455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68959907610947397017804303 103439861416421095526706455)
  ·
    refine ⟨155159792124631643290059683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103439861416421095526706455 155159792124631643290059683)
    ·
      refine ⟨232739688186947464935089525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155159792124631643290059683 232739688186947464935089525)
      ·
        refine ⟨21819345767526324837664643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232739688186947464935089525 21819345767526324837664643)
        ·
          refine ⟨32729018651289487256496965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21819345767526324837664643 32729018651289487256496965)
          ·
            refine ⟨6136690997116778860593181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32729018651289487256496965 6136690997116778860593181)
            ·
              refine ⟨2301259123918792072722443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6136690997116778860593181 2301259123918792072722443)
              ·
                refine ⟨3451888685878188109083665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301259123918792072722443 3451888685878188109083665)
                ·
                  refine ⟨2588916514408641081812749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3451888685878188109083665 2588916514408641081812749)
                  ·
                    refine ⟨970843692903240405679781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588916514408641081812749 970843692903240405679781)
                    ·
                      rfl

theorem cell22_2836067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 3].length) (baseStart_2836067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836067 prefixEnd_2836067 := by exact prefixLift 2836067
  have htrace : WordTrace (prefixWord ++ tailWord_2836067) baseStart_2836067 baseEnd_2836067 := by
    simpa [prefixWord, tailWord_2836067, baseEnd_2836067] using wordTrace_append hprefix tailTrace_2836067
  have hstable : (prefixWord ++ tailWord_2836067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836067).length < 2 ^ (prefixWord ++ tailWord_2836067).sum := by decide
  have hdescent : baseEnd_2836067 < baseStart_2836067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836080 : List Nat := [2, 1, 1, 1, 6, 3, 2, 6]
def baseStart_2836080 : Nat := 118140960795 + 2836080 * 2 ^ 59
def prefixEnd_2836080 : Nat := 4983230072969 + 3 ^ 40 * 2836080 * 2
def baseEnd_2836080 : Nat := 107872015896545856122749

theorem tailTrace_2836080 : CollatzResearch.WordTrace tailWord_2836080 prefixEnd_2836080 107872015896545856122749 := by
  unfold tailWord_2836080
  simp only [CollatzResearch.WordTrace]
  refine ⟨51720167782686999373464847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68960223710249332497953129 51720167782686999373464847)
  ·
    refine ⟨77580251674030499060197271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51720167782686999373464847 77580251674030499060197271)
    ·
      refine ⟨116370377511045748590295907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77580251674030499060197271 116370377511045748590295907)
      ·
        refine ⟨174555566266568622885443861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116370377511045748590295907 174555566266568622885443861)
        ·
          refine ⟨8182292168745404197755181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174555566266568622885443861 8182292168745404197755181)
          ·
            refine ⟨3068359563279526574158193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8182292168745404197755181 3068359563279526574158193)
            ·
              refine ⟨2301269672459644930618645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3068359563279526574158193 2301269672459644930618645)
              ·
                refine ⟨107872015896545856122749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2301269672459644930618645 107872015896545856122749)
                ·
                  rfl

theorem cell22_2836080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_2836080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836080 prefixEnd_2836080 := by exact prefixLift 2836080
  have htrace : WordTrace (prefixWord ++ tailWord_2836080) baseStart_2836080 baseEnd_2836080 := by
    simpa [prefixWord, tailWord_2836080, baseEnd_2836080] using wordTrace_append hprefix tailTrace_2836080
  have hstable : (prefixWord ++ tailWord_2836080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836080).length < 2 ^ (prefixWord ++ tailWord_2836080).sum := by decide
  have hdescent : baseEnd_2836080 < baseStart_2836080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836091 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 9]
def baseStart_2836091 : Nat := 118140960795 + 2836091 * 2 ^ 59
def prefixEnd_2836091 : Nat := 4983230072969 + 3 ^ 40 * 2836091 * 2
def baseEnd_2836091 : Nat := 323617302864570781026569

theorem tailTrace_2836091 : CollatzResearch.WordTrace tailWord_2836091 prefixEnd_2836091 323617302864570781026569 := by
  unfold tailWord_2836091
  simp only [CollatzResearch.WordTrace]
  refine ⟨103440736768334147625580127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68960491178889431750386751 103440736768334147625580127)
  ·
    refine ⟨155161105152501221438370191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103440736768334147625580127 155161105152501221438370191)
    ·
      refine ⟨232741657728751832157555287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155161105152501221438370191 232741657728751832157555287)
      ·
        refine ⟨349112486593127748236332931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232741657728751832157555287 349112486593127748236332931)
        ·
          refine ⟨523668729889691622354499397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349112486593127748236332931 523668729889691622354499397)
          ·
            refine ⟨98187886854317179191468637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 523668729889691622354499397 98187886854317179191468637)
            ·
              refine ⟨36820457570368942196800739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98187886854317179191468637 36820457570368942196800739)
              ·
                refine ⟨55230686355553413295201109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36820457570368942196800739 55230686355553413295201109)
                ·
                  refine ⟨323617302864570781026569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55230686355553413295201109 323617302864570781026569)
                  ·
                    rfl

theorem cell22_2836091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_2836091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836091 prefixEnd_2836091 := by exact prefixLift 2836091
  have htrace : WordTrace (prefixWord ++ tailWord_2836091) baseStart_2836091 baseEnd_2836091 := by
    simpa [prefixWord, tailWord_2836091, baseEnd_2836091] using wordTrace_append hprefix tailTrace_2836091
  have hstable : (prefixWord ++ tailWord_2836091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836091).length < 2 ^ (prefixWord ++ tailWord_2836091).sum := by decide
  have hdescent : baseEnd_2836091 < baseStart_2836091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836108 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_2836108 : Nat := 118140960795 + 2836108 * 2 ^ 59
def prefixEnd_2836108 : Nat := 4983230072969 + 3 ^ 40 * 2836108 * 2
def baseEnd_2836108 : Nat := 323619242680376655134885

theorem tailTrace_2836108 : CollatzResearch.WordTrace tailWord_2836108 prefixEnd_2836108 323619242680376655134885 := by
  unfold tailWord_2836108
  simp only [CollatzResearch.WordTrace]
  refine ⟨51720678404636279764474489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68960904539515039685965985 51720678404636279764474489)
  ·
    refine ⟨38790508803477209823355867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51720678404636279764474489 38790508803477209823355867)
    ·
      refine ⟨58185763205215814735033801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38790508803477209823355867 58185763205215814735033801)
      ·
        refine ⟨43639322403911861051275351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58185763205215814735033801 43639322403911861051275351)
        ·
          refine ⟨65458983605867791576913027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43639322403911861051275351 65458983605867791576913027)
          ·
            refine ⟨98188475408801687365369541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65458983605867791576913027 98188475408801687365369541)
            ·
              refine ⟨18410339139150316381006789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98188475408801687365369541 18410339139150316381006789)
              ·
                refine ⟨3451938588590684321438773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18410339139150316381006789 3451938588590684321438773)
                ·
                  refine ⟨323619242680376655134885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3451938588590684321438773 323619242680376655134885)
                  ·
                    rfl

theorem cell22_2836108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_2836108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836108 prefixEnd_2836108 := by exact prefixLift 2836108
  have htrace : WordTrace (prefixWord ++ tailWord_2836108) baseStart_2836108 baseEnd_2836108 := by
    simpa [prefixWord, tailWord_2836108, baseEnd_2836108] using wordTrace_append hprefix tailTrace_2836108
  have hstable : (prefixWord ++ tailWord_2836108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836108).length < 2 ^ (prefixWord ++ tailWord_2836108).sum := by decide
  have hdescent : baseEnd_2836108 < baseStart_2836108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836168 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_2836168 : Nat := 118140960795 + 2836168 * 2 ^ 59
def prefixEnd_2836168 : Nat := 4983230072969 + 3 ^ 40 * 2836168 * 2
def baseEnd_2836168 : Nat := 970878267267309808904471

theorem tailTrace_2836168 : CollatzResearch.WordTrace tailWord_2836168 prefixEnd_2836168 970878267267309808904471 := by
  unfold tailWord_2836168
  simp only [CollatzResearch.WordTrace]
  refine ⟨51721772594527594888066579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68962363459370126517422105 51721772594527594888066579)
  ·
    refine ⟨77582658891791392332099869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51721772594527594888066579 77582658891791392332099869)
    ·
      refine ⟨29093497084421772124537451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77582658891791392332099869 29093497084421772124537451)
      ·
        refine ⟨43640245626632658186806177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29093497084421772124537451 43640245626632658186806177)
        ·
          refine ⟨32730184219974493640104633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43640245626632658186806177 32730184219974493640104633)
          ·
            refine ⟨24547638164980870230078475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32730184219974493640104633 24547638164980870230078475)
            ·
              refine ⟨36821457247471305345117713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24547638164980870230078475 36821457247471305345117713)
              ·
                refine ⟨27616092935603479008838285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36821457247471305345117713 27616092935603479008838285)
                ·
                  refine ⟨10356034850851304628314357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27616092935603479008838285 10356034850851304628314357)
                  ·
                    refine ⟨970878267267309808904471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10356034850851304628314357 970878267267309808904471)
                    ·
                      rfl

theorem cell22_2836168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_2836168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836168 prefixEnd_2836168 := by exact prefixLift 2836168
  have htrace : WordTrace (prefixWord ++ tailWord_2836168) baseStart_2836168 baseEnd_2836168 := by
    simpa [prefixWord, tailWord_2836168, baseEnd_2836168] using wordTrace_append hprefix tailTrace_2836168
  have hstable : (prefixWord ++ tailWord_2836168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836168).length < 2 ^ (prefixWord ++ tailWord_2836168).sum := by decide
  have hdescent : baseEnd_2836168 < baseStart_2836168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836183 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_2836183 : Nat := 118140960795 + 2836183 * 2 ^ 59
def prefixEnd_2836183 : Nat := 4983230072969 + 3 ^ 40 * 2836183 * 2
def baseEnd_2836183 : Nat := 970883402073854769779425

theorem tailTrace_2836183 : CollatzResearch.WordTrace tailWord_2836183 prefixEnd_2836183 970883402073854769779425 := by
  unfold tailWord_2836183
  simp only [CollatzResearch.WordTrace]
  refine ⟨103444092284000847337929203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68962728189333898225286135 103444092284000847337929203)
  ·
    refine ⟨155166138426001271006893805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103444092284000847337929203 155166138426001271006893805)
    ·
      refine ⟨58187301909750476627585177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155166138426001271006893805 58187301909750476627585177)
      ·
        refine ⟨43640476432312857470688883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58187301909750476627585177 43640476432312857470688883)
        ·
          refine ⟨65460714648469286206033325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43640476432312857470688883 65460714648469286206033325)
          ·
            refine ⟨24547767993175982327262497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65460714648469286206033325 24547767993175982327262497)
            ·
              refine ⟨18410825994881986745446873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24547767993175982327262497 18410825994881986745446873)
              ·
                refine ⟨13808119496161490059085155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18410825994881986745446873 13808119496161490059085155)
                ·
                  refine ⟨20712179244242235088627733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13808119496161490059085155 20712179244242235088627733)
                  ·
                    refine ⟨970883402073854769779425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20712179244242235088627733 970883402073854769779425)
                    ·
                      rfl

theorem cell22_2836183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_2836183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836183 prefixEnd_2836183 := by exact prefixLift 2836183
  have htrace : WordTrace (prefixWord ++ tailWord_2836183) baseStart_2836183 baseEnd_2836183 := by
    simpa [prefixWord, tailWord_2836183, baseEnd_2836183] using wordTrace_append hprefix tailTrace_2836183
  have hstable : (prefixWord ++ tailWord_2836183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836183).length < 2 ^ (prefixWord ++ tailWord_2836183).sum := by decide
  have hdescent : baseEnd_2836183 < baseStart_2836183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836185 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_2836185 : Nat := 118140960795 + 2836185 * 2 ^ 59
def prefixEnd_2836185 : Nat := 4983230072969 + 3 ^ 40 * 2836185 * 2
def baseEnd_2836185 : Nat := 970884086714727431229419

theorem tailTrace_2836185 : CollatzResearch.WordTrace tailWord_2836185 prefixEnd_2836185 970884086714727431229419 := by
  unfold tailWord_2836185
  simp only [CollatzResearch.WordTrace]
  refine ⟨103444165229993601679502009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68962776819995734453001339 103444165229993601679502009)
  ·
    refine ⟨77583123922495201259626507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103444165229993601679502009 77583123922495201259626507)
    ·
      refine ⟨116374685883742801889439761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77583123922495201259626507 116374685883742801889439761)
      ·
        refine ⟨87281014412807101417079821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116374685883742801889439761 87281014412807101417079821)
        ·
          refine ⟨32730380404802663031404933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87281014412807101417079821 32730380404802663031404933)
          ·
            refine ⟨6136946325900499318388425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32730380404802663031404933 6136946325900499318388425)
            ·
              refine ⟨4602709744425374488791319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6136946325900499318388425 4602709744425374488791319)
              ·
                refine ⟨6904064616638061733186979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602709744425374488791319 6904064616638061733186979)
                ·
                  refine ⟨10356096924957092599780469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6904064616638061733186979 10356096924957092599780469)
                  ·
                    refine ⟨970884086714727431229419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10356096924957092599780469 970884086714727431229419)
                    ·
                      rfl

theorem cell22_2836185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_2836185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836185 prefixEnd_2836185 := by exact prefixLift 2836185
  have htrace : WordTrace (prefixWord ++ tailWord_2836185) baseStart_2836185 baseEnd_2836185 := by
    simpa [prefixWord, tailWord_2836185, baseEnd_2836185] using wordTrace_append hprefix tailTrace_2836185
  have hstable : (prefixWord ++ tailWord_2836185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836185).length < 2 ^ (prefixWord ++ tailWord_2836185).sum := by decide
  have hdescent : baseEnd_2836185 < baseStart_2836185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836200 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_2836200 : Nat := 118140960795 + 2836200 * 2 ^ 59
def prefixEnd_2836200 : Nat := 4983230072969 + 3 ^ 40 * 2836200 * 2
def baseEnd_2836200 : Nat := 970889221521272392104373

theorem tailTrace_2836200 : CollatzResearch.WordTrace tailWord_2836200 prefixEnd_2836200 970889221521272392104373 := by
  unfold tailWord_2836200
  simp only [CollatzResearch.WordTrace]
  refine ⟨51722356162469629620649027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68963141549959506160865369 51722356162469629620649027)
  ·
    refine ⟨77583534243704444430973541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51722356162469629620649027 77583534243704444430973541)
    ·
      refine ⟨14546912670694583330807539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77583534243704444430973541 14546912670694583330807539)
      ·
        refine ⟨21820369006041874996211309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14546912670694583330807539 21820369006041874996211309)
        ·
          refine ⟨8182638377265703123579241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21820369006041874996211309 8182638377265703123579241)
          ·
            refine ⟨6136978782949277342684431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8182638377265703123579241 6136978782949277342684431)
            ·
              refine ⟨9205468174423916014026647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136978782949277342684431 9205468174423916014026647)
              ·
                refine ⟨13808202261635874021039971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9205468174423916014026647 13808202261635874021039971)
                ·
                  refine ⟨20712303392453811031559957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13808202261635874021039971 20712303392453811031559957)
                  ·
                    refine ⟨970889221521272392104373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20712303392453811031559957 970889221521272392104373)
                    ·
                      rfl

theorem cell22_2836200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_2836200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836200 prefixEnd_2836200 := by exact prefixLift 2836200
  have htrace : WordTrace (prefixWord ++ tailWord_2836200) baseStart_2836200 baseEnd_2836200 := by
    simpa [prefixWord, tailWord_2836200, baseEnd_2836200] using wordTrace_append hprefix tailTrace_2836200
  have hstable : (prefixWord ++ tailWord_2836200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836200).length < 2 ^ (prefixWord ++ tailWord_2836200).sum := by decide
  have hdescent : baseEnd_2836200 < baseStart_2836200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836247 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 3, 3]
def baseStart_2836247 : Nat := 118140960795 + 2836247 * 2 ^ 59
def prefixEnd_2836247 : Nat := 4983230072969 + 3 ^ 40 * 2836247 * 2
def baseEnd_2836247 : Nat := 970905310581779936179229

theorem tailTrace_2836247 : CollatzResearch.WordTrace tailWord_2836247 prefixEnd_2836247 970905310581779936179229 := by
  unfold tailWord_2836247
  simp only [CollatzResearch.WordTrace]
  refine ⟨103446426555768986268258995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68964284370512657512172663 103446426555768986268258995)
  ·
    refine ⟨155169639833653479402388493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103446426555768986268258995 155169639833653479402388493)
    ·
      refine ⟨58188614937620054775895685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155169639833653479402388493 58188614937620054775895685)
      ·
        refine ⟨10910365300803760270480441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58188614937620054775895685 10910365300803760270480441)
        ·
          refine ⟨8182773975602820202860331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10910365300803760270480441 8182773975602820202860331)
          ·
            refine ⟨12274160963404230304290497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8182773975602820202860331 12274160963404230304290497)
            ·
              refine ⟨9205620722553172728217873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12274160963404230304290497 9205620722553172728217873)
              ·
                refine ⟨6904215541914879546163405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9205620722553172728217873 6904215541914879546163405)
                ·
                  refine ⟨2589080828218079829811277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6904215541914879546163405 2589080828218079829811277)
                  ·
                    refine ⟨970905310581779936179229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589080828218079829811277 970905310581779936179229)
                    ·
                      rfl

theorem cell22_2836247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 3].length) (baseStart_2836247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836247 prefixEnd_2836247 := by exact prefixLift 2836247
  have htrace : WordTrace (prefixWord ++ tailWord_2836247) baseStart_2836247 baseEnd_2836247 := by
    simpa [prefixWord, tailWord_2836247, baseEnd_2836247] using wordTrace_append hprefix tailTrace_2836247
  have hstable : (prefixWord ++ tailWord_2836247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836247).length < 2 ^ (prefixWord ++ tailWord_2836247).sum := by decide
  have hdescent : baseEnd_2836247 < baseStart_2836247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836260 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_2836260 : Nat := 118140960795 + 2836260 * 2 ^ 59
def prefixEnd_2836260 : Nat := 4983230072969 + 3 ^ 40 * 2836260 * 2
def baseEnd_2836260 : Nat := 323636586915817411868063

theorem tailTrace_2836260 : CollatzResearch.WordTrace tailWord_2836260 prefixEnd_2836260 323636586915817411868063 := by
  unfold tailWord_2836260
  simp only [CollatzResearch.WordTrace]
  refine ⟨51723450352360944744241117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68964600469814592992321489 51723450352360944744241117)
  ·
    refine ⟨19396293882135354279090419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51723450352360944744241117 19396293882135354279090419)
    ·
      refine ⟨29094440823203031418635629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19396293882135354279090419 29094440823203031418635629)
      ·
        refine ⟨10910415308701136781988361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29094440823203031418635629 10910415308701136781988361)
        ·
          refine ⟨8182811481525852586491271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10910415308701136781988361 8182811481525852586491271)
          ·
            refine ⟨12274217222288778879736907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8182811481525852586491271 12274217222288778879736907)
            ·
              refine ⟨18411325833433168319605361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12274217222288778879736907 18411325833433168319605361)
              ·
                refine ⟨13808494375074876239704021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18411325833433168319605361 13808494375074876239704021)
                ·
                  refine ⟨323636586915817411868063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13808494375074876239704021 323636586915817411868063)
                  ·
                    rfl

theorem cell22_2836260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_2836260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836260 prefixEnd_2836260 := by exact prefixLift 2836260
  have htrace : WordTrace (prefixWord ++ tailWord_2836260) baseStart_2836260 baseEnd_2836260 := by
    simpa [prefixWord, tailWord_2836260, baseEnd_2836260] using wordTrace_append hprefix tailTrace_2836260
  have hstable : (prefixWord ++ tailWord_2836260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836260).length < 2 ^ (prefixWord ++ tailWord_2836260).sum := by decide
  have hdescent : baseEnd_2836260 < baseStart_2836260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836281 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_2836281 : Nat := 118140960795 + 2836281 * 2 ^ 59
def prefixEnd_2836281 : Nat := 4983230072969 + 3 ^ 40 * 2836281 * 2
def baseEnd_2836281 : Nat := 970916949476615180829125

theorem tailTrace_2836281 : CollatzResearch.WordTrace tailWord_2836281 prefixEnd_2836281 970916949476615180829125 := by
  unfold tailWord_2836281
  simp only [CollatzResearch.WordTrace]
  refine ⟨103447666637645810074996697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68965111091763873383331131 103447666637645810074996697)
  ·
    refine ⟨77585749978234357556247523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103447666637645810074996697 77585749978234357556247523)
    ·
      refine ⟨116378624967351536334371285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77585749978234357556247523 116378624967351536334371285)
      ·
        refine ⟨2727624022672301632836827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 116378624967351536334371285 2727624022672301632836827)
        ·
          refine ⟨4091436034008452449255241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727624022672301632836827 4091436034008452449255241)
          ·
            refine ⟨3068577025506339336941431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4091436034008452449255241 3068577025506339336941431)
            ·
              refine ⟨4602865538259509005412147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068577025506339336941431 4602865538259509005412147)
              ·
                refine ⟨6904298307389263508118221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602865538259509005412147 6904298307389263508118221)
                ·
                  refine ⟨2589111865270973815544333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6904298307389263508118221 2589111865270973815544333)
                  ·
                    refine ⟨970916949476615180829125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589111865270973815544333 970916949476615180829125)
                    ·
                      rfl

theorem cell22_2836281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_2836281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836281 prefixEnd_2836281 := by exact prefixLift 2836281
  have htrace : WordTrace (prefixWord ++ tailWord_2836281) baseStart_2836281 baseEnd_2836281 := by
    simpa [prefixWord, tailWord_2836281, baseEnd_2836281] using wordTrace_append hprefix tailTrace_2836281
  have hstable : (prefixWord ++ tailWord_2836281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836281).length < 2 ^ (prefixWord ++ tailWord_2836281).sum := by decide
  have hdescent : baseEnd_2836281 < baseStart_2836281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836320 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_2836320 : Nat := 118140960795 + 2836320 * 2 ^ 59
def prefixEnd_2836320 : Nat := 4983230072969 + 3 ^ 40 * 2836320 * 2
def baseEnd_2836320 : Nat := 970930299973632079104005

theorem tailTrace_2836320 : CollatzResearch.WordTrace tailWord_2836320 prefixEnd_2836320 970930299973632079104005 := by
  unfold tailWord_2836320
  simp only [CollatzResearch.WordTrace]
  refine ⟨51724544542252259867833207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68966059389669679823777609 51724544542252259867833207)
  ·
    refine ⟨77586816813378389801749811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51724544542252259867833207 77586816813378389801749811)
    ·
      refine ⟨116380225220067584702624717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77586816813378389801749811 116380225220067584702624717)
      ·
        refine ⟨43642584457525344263484269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116380225220067584702624717 43642584457525344263484269)
        ·
          refine ⟨16365969171572004098806601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43642584457525344263484269 16365969171572004098806601)
          ·
            refine ⟨12274476878679003074104951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16365969171572004098806601 12274476878679003074104951)
            ·
              refine ⟨18411715318018504611157427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12274476878679003074104951 18411715318018504611157427)
              ·
                refine ⟨27617572977027756916736141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18411715318018504611157427 27617572977027756916736141)
                ·
                  refine ⟨10356589866385408843776053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27617572977027756916736141 10356589866385408843776053)
                  ·
                    refine ⟨970930299973632079104005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10356589866385408843776053 970930299973632079104005)
                    ·
                      rfl

theorem cell22_2836320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_2836320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836320 prefixEnd_2836320 := by exact prefixLift 2836320
  have htrace : WordTrace (prefixWord ++ tailWord_2836320) baseStart_2836320 baseEnd_2836320 := by
    simpa [prefixWord, tailWord_2836320, baseEnd_2836320] using wordTrace_append hprefix tailTrace_2836320
  have hstable : (prefixWord ++ tailWord_2836320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836320).length < 2 ^ (prefixWord ++ tailWord_2836320).sum := by decide
  have hdescent : baseEnd_2836320 < baseStart_2836320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836399 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 1, 3]
def baseStart_2836399 : Nat := 118140960795 + 2836399 * 2 ^ 59
def prefixEnd_2836399 : Nat := 4983230072969 + 3 ^ 40 * 2836399 * 2
def baseEnd_2836399 : Nat := 970957343288102206378763

theorem tailTrace_2836399 : CollatzResearch.WordTrace tailWord_2836399 prefixEnd_2836399 970957343288102206378763 := by
  unfold tailWord_2836399
  simp only [CollatzResearch.WordTrace]
  refine ⟨103451970451218316227792251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68967980300812210818528167 103451970451218316227792251)
  ·
    refine ⟨155177955676827474341688377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103451970451218316227792251 155177955676827474341688377)
    ·
      refine ⟨116383466757620605756266283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155177955676827474341688377 116383466757620605756266283)
      ·
        refine ⟨174575200136430908634399425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116383466757620605756266283 174575200136430908634399425)
        ·
          refine ⟨130931400102323181475799569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174575200136430908634399425 130931400102323181475799569)
          ·
            refine ⟨98198550076742386106849677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130931400102323181475799569 98198550076742386106849677)
            ·
              refine ⟨36824456278778394790068629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98198550076742386106849677 36824456278778394790068629)
              ·
                refine ⟨1726146388067737255784467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36824456278778394790068629 1726146388067737255784467)
                ·
                  refine ⟨2589219582101605883676701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726146388067737255784467 2589219582101605883676701)
                  ·
                    refine ⟨970957343288102206378763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589219582101605883676701 970957343288102206378763)
                    ·
                      rfl

theorem cell22_2836399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 1, 3].length) (baseStart_2836399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836399 prefixEnd_2836399 := by exact prefixLift 2836399
  have htrace : WordTrace (prefixWord ++ tailWord_2836399) baseStart_2836399 baseEnd_2836399 := by
    simpa [prefixWord, tailWord_2836399, baseEnd_2836399] using wordTrace_append hprefix tailTrace_2836399
  have hstable : (prefixWord ++ tailWord_2836399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836399).length < 2 ^ (prefixWord ++ tailWord_2836399).sum := by decide
  have hdescent : baseEnd_2836399 < baseStart_2836399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836410 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2836410 : Nat := 118140960795 + 2836410 * 2 ^ 59
def prefixEnd_2836410 : Nat := 4983230072969 + 3 ^ 40 * 2836410 * 2
def baseEnd_2836410 : Nat := 970961108812901844353729

theorem tailTrace_2836410 : CollatzResearch.WordTrace tailWord_2836410 prefixEnd_2836410 970961108812901844353729 := by
  unfold tailWord_2836410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863092913544616276610671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68968247769452310070961789 25863092913544616276610671)
  ·
    refine ⟨38794639370316924414916007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25863092913544616276610671 38794639370316924414916007)
    ·
      refine ⟨58191959055475386622374011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38794639370316924414916007 58191959055475386622374011)
      ·
        refine ⟨87287938583213079933561017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58191959055475386622374011 87287938583213079933561017)
        ·
          refine ⟨65465953937409809950170763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87287938583213079933561017 65465953937409809950170763)
          ·
            refine ⟨98198930906114714925256145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65465953937409809950170763 98198930906114714925256145)
            ·
              refine ⟨73649198179586036193942109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98198930906114714925256145 73649198179586036193942109)
              ·
                refine ⟨27618449317344763572728291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73649198179586036193942109 27618449317344763572728291)
                ·
                  refine ⟨41427673976017145359092437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27618449317344763572728291 41427673976017145359092437)
                  ·
                    refine ⟨970961108812901844353729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41427673976017145359092437 970961108812901844353729)
                    ·
                      rfl

theorem cell22_2836410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2836410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836410 prefixEnd_2836410 := by exact prefixLift 2836410
  have htrace : WordTrace (prefixWord ++ tailWord_2836410) baseStart_2836410 baseEnd_2836410 := by
    simpa [prefixWord, tailWord_2836410, baseEnd_2836410] using wordTrace_append hprefix tailTrace_2836410
  have hstable : (prefixWord ++ tailWord_2836410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836410).length < 2 ^ (prefixWord ++ tailWord_2836410).sum := by decide
  have hdescent : baseEnd_2836410 < baseStart_2836410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836450 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2836450 : Nat := 118140960795 + 2836450 * 2 ^ 59
def prefixEnd_2836450 : Nat := 4983230072969 + 3 ^ 40 * 2836450 * 2
def baseEnd_2836450 : Nat := 970974801630355073353607

theorem tailTrace_2836450 : CollatzResearch.WordTrace tailWord_2836450 prefixEnd_2836450 970974801630355073353607 := by
  unfold tailWord_2836450
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863457643508387984474701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68969220382689034625265869 25863457643508387984474701)
  ·
    refine ⟨9698796616315645494178013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25863457643508387984474701 9698796616315645494178013)
    ·
      refine ⟨3637048731118367060316755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9698796616315645494178013 3637048731118367060316755)
      ·
        refine ⟨5455573096677550590475133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637048731118367060316755 5455573096677550590475133)
        ·
          refine ⟨2045839911254081471428175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5455573096677550590475133 2045839911254081471428175)
          ·
            refine ⟨3068759866881122207142263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045839911254081471428175 3068759866881122207142263)
            ·
              refine ⟨4603139800321683310713395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068759866881122207142263 4603139800321683310713395)
              ·
                refine ⟨6904709700482524966070093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603139800321683310713395 6904709700482524966070093)
                ·
                  refine ⟨2589266137680946862276285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6904709700482524966070093 2589266137680946862276285)
                  ·
                    refine ⟨970974801630355073353607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589266137680946862276285 970974801630355073353607)
                    ·
                      rfl

theorem cell22_2836450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2836450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836450 prefixEnd_2836450 := by exact prefixLift 2836450
  have htrace : WordTrace (prefixWord ++ tailWord_2836450) baseStart_2836450 baseEnd_2836450 := by
    simpa [prefixWord, tailWord_2836450, baseEnd_2836450] using wordTrace_append hprefix tailTrace_2836450
  have hstable : (prefixWord ++ tailWord_2836450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836450).length < 2 ^ (prefixWord ++ tailWord_2836450).sum := by decide
  have hdescent : baseEnd_2836450 < baseStart_2836450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836506 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 2, 3]
def baseStart_2836506 : Nat := 118140960795 + 2836506 * 2 ^ 59
def prefixEnd_2836506 : Nat := 4983230072969 + 3 ^ 40 * 2836506 * 2
def baseEnd_2836506 : Nat := 970993971574789593953435

theorem tailTrace_2836506 : CollatzResearch.WordTrace tailWord_2836506 prefixEnd_2836506 970993971574789593953435 := by
  unfold tailWord_2836506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863968265457668375484343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68970582041220449001291581 25863968265457668375484343)
  ·
    refine ⟨38795952398186502563226515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25863968265457668375484343 38795952398186502563226515)
    ·
      refine ⟨58193928597279753844839773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38795952398186502563226515 58193928597279753844839773)
      ·
        refine ⟨21822723223979907691814915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58193928597279753844839773 21822723223979907691814915)
        ·
          refine ⟨32734084835969861537722373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21822723223979907691814915 32734084835969861537722373)
          ·
            refine ⟨6137640906744349038322945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32734084835969861537722373 6137640906744349038322945)
            ·
              refine ⟨4603230680058261778742209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137640906744349038322945 4603230680058261778742209)
              ·
                refine ⟨3452423010043696334056657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603230680058261778742209 3452423010043696334056657)
                ·
                  refine ⟨2589317257532772250542493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3452423010043696334056657 2589317257532772250542493)
                  ·
                    refine ⟨970993971574789593953435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589317257532772250542493 970993971574789593953435)
                    ·
                      rfl

theorem cell22_2836506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_2836506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836506 prefixEnd_2836506 := by exact prefixLift 2836506
  have htrace : WordTrace (prefixWord ++ tailWord_2836506) baseStart_2836506 baseEnd_2836506 := by
    simpa [prefixWord, tailWord_2836506, baseEnd_2836506] using wordTrace_append hprefix tailTrace_2836506
  have hstable : (prefixWord ++ tailWord_2836506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836506).length < 2 ^ (prefixWord ++ tailWord_2836506).sum := by decide
  have hdescent : baseEnd_2836506 < baseStart_2836506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836508 : List Nat := [2, 2, 3, 1, 3, 3, 2, 2, 4]
def baseStart_2836508 : Nat := 118140960795 + 2836508 * 2 ^ 59
def prefixEnd_2836508 : Nat := 4983230072969 + 3 ^ 40 * 2836508 * 2
def baseEnd_2836508 : Nat := 323664885405220751801143

theorem tailTrace_2836508 : CollatzResearch.WordTrace tailWord_2836508 prefixEnd_2836508 323664885405220751801143 := by
  unfold tailWord_2836508
  simp only [CollatzResearch.WordTrace]
  refine ⟨51727973003911713921755089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68970630671882285229006785 51727973003911713921755089)
  ·
    refine ⟨38795979752933785441316317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51727973003911713921755089 38795979752933785441316317)
    ·
      refine ⟨14548492407350169540493619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38795979752933785441316317 14548492407350169540493619)
      ·
        refine ⟨21822738611025254310740429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14548492407350169540493619 21822738611025254310740429)
        ·
          refine ⟨8183526979134470366527661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21822738611025254310740429 8183526979134470366527661)
          ·
            refine ⟨3068822617175426387447873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8183526979134470366527661 3068822617175426387447873)
            ·
              refine ⟨2301616962881569790585905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3068822617175426387447873 2301616962881569790585905)
              ·
                refine ⟨1726212722161177342939429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301616962881569790585905 1726212722161177342939429)
                ·
                  refine ⟨323664885405220751801143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726212722161177342939429 323664885405220751801143)
                  ·
                    rfl

theorem cell22_2836508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_2836508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836508 prefixEnd_2836508 := by exact prefixLift 2836508
  have htrace : WordTrace (prefixWord ++ tailWord_2836508) baseStart_2836508 baseEnd_2836508 := by
    simpa [prefixWord, tailWord_2836508, baseEnd_2836508] using wordTrace_append hprefix tailTrace_2836508
  have hstable : (prefixWord ++ tailWord_2836508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836508).length < 2 ^ (prefixWord ++ tailWord_2836508).sum := by decide
  have hdescent : baseEnd_2836508 < baseStart_2836508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836581 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 5]
def baseStart_2836581 : Nat := 118140960795 + 2836581 * 2 ^ 59
def prefixEnd_2836581 : Nat := 4983230072969 + 3 ^ 40 * 2836581 * 2
def baseEnd_2836581 : Nat := 323673215202504799442735

theorem tailTrace_2836581 : CollatzResearch.WordTrace tailWord_2836581 prefixEnd_2836581 323673215202504799442735 := by
  unfold tailWord_2836581
  simp only [CollatzResearch.WordTrace]
  refine ⟨103458608536558961310917597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68972405691039307540611731 103458608536558961310917597)
  ·
    refine ⟨38796978201209610491594099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103458608536558961310917597 38796978201209610491594099)
    ·
      refine ⟨58195467301814415737391149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38796978201209610491594099 58195467301814415737391149)
      ·
        refine ⟨21823300238180405901521681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58195467301814415737391149 21823300238180405901521681)
        ·
          refine ⟨16367475178635304426141261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21823300238180405901521681 16367475178635304426141261)
          ·
            refine ⟨6137803191988239159802973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16367475178635304426141261 6137803191988239159802973)
            ·
              refine ⟨2301676196995589684926115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6137803191988239159802973 2301676196995589684926115)
              ·
                refine ⟨3452514295493384527389173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301676196995589684926115 3452514295493384527389173)
                ·
                  refine ⟨323673215202504799442735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3452514295493384527389173 323673215202504799442735)
                  ·
                    rfl

theorem cell22_2836581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_2836581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836581 prefixEnd_2836581 := by exact prefixLift 2836581
  have htrace : WordTrace (prefixWord ++ tailWord_2836581) baseStart_2836581 baseEnd_2836581 := by
    simpa [prefixWord, tailWord_2836581, baseEnd_2836581] using wordTrace_append hprefix tailTrace_2836581
  have hstable : (prefixWord ++ tailWord_2836581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836581).length < 2 ^ (prefixWord ++ tailWord_2836581).sum := by decide
  have hdescent : baseEnd_2836581 < baseStart_2836581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836624 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_2836624 : Nat := 118140960795 + 2836624 * 2 ^ 59
def prefixEnd_2836624 : Nat := 4983230072969 + 3 ^ 40 * 2836624 * 2
def baseEnd_2836624 : Nat := 971034365386276619503073

theorem tailTrace_2836624 : CollatzResearch.WordTrace tailWord_2836624 prefixEnd_2836624 971034365386276619503073 := by
  unfold tailWord_2836624
  simp only [CollatzResearch.WordTrace]
  refine ⟨51730088437701589827366463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68973451250268786436488617 51730088437701589827366463)
  ·
    refine ⟨77595132656552384741049695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51730088437701589827366463 77595132656552384741049695)
    ·
      refine ⟨116392698984828577111574543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77595132656552384741049695 116392698984828577111574543)
      ·
        refine ⟨174589048477242865667361815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116392698984828577111574543 174589048477242865667361815)
        ·
          refine ⟨261883572715864298501042723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174589048477242865667361815 261883572715864298501042723)
          ·
            refine ⟨392825359073796447751564085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261883572715864298501042723 392825359073796447751564085)
            ·
              refine ⟨36827377413168416976709133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 392825359073796447751564085 36827377413168416976709133)
              ·
                refine ⟨13810266529938156366265925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36827377413168416976709133 13810266529938156366265925)
                ·
                  refine ⟨2589424974363404318674861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13810266529938156366265925 2589424974363404318674861)
                  ·
                    refine ⟨971034365386276619503073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589424974363404318674861 971034365386276619503073)
                    ·
                      rfl

theorem cell22_2836624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_2836624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836624 prefixEnd_2836624 := by exact prefixLift 2836624
  have htrace : WordTrace (prefixWord ++ tailWord_2836624) baseStart_2836624 baseEnd_2836624 := by
    simpa [prefixWord, tailWord_2836624, baseEnd_2836624] using wordTrace_append hprefix tailTrace_2836624
  have hstable : (prefixWord ++ tailWord_2836624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836624).length < 2 ^ (prefixWord ++ tailWord_2836624).sum := by decide
  have hdescent : baseEnd_2836624 < baseStart_2836624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836714 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2836714 : Nat := 118140960795 + 2836714 * 2 ^ 59
def prefixEnd_2836714 : Nat := 4983230072969 + 3 ^ 40 * 2836714 * 2
def baseEnd_2836714 : Nat := 971065174225546384752797

theorem tailTrace_2836714 : CollatzResearch.WordTrace tailWord_2836714 prefixEnd_2836714 971065174225546384752797 := by
  unfold tailWord_2836714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25865864861269281256377299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68975639630051416683672797 25865864861269281256377299)
  ·
    refine ⟨38798797291903921884565949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25865864861269281256377299 38798797291903921884565949)
    ·
      refine ⟨14549548984463970706712231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38798797291903921884565949 14549548984463970706712231)
      ·
        refine ⟨21824323476695956060068347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14549548984463970706712231 21824323476695956060068347)
        ·
          refine ⟨32736485215043934090102521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21824323476695956060068347 32736485215043934090102521)
          ·
            refine ⟨24552363911282950567576891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32736485215043934090102521 24552363911282950567576891)
            ·
              refine ⟨36828545866924425851365337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24552363911282950567576891 36828545866924425851365337)
              ·
                refine ⟨27621409400193319388524003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36828545866924425851365337 27621409400193319388524003)
                ·
                  refine ⟨41432114100289979082786005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27621409400193319388524003 41432114100289979082786005)
                  ·
                    refine ⟨971065174225546384752797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41432114100289979082786005 971065174225546384752797)
                    ·
                      rfl

theorem cell22_2836714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2836714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836714 prefixEnd_2836714 := by exact prefixLift 2836714
  have htrace : WordTrace (prefixWord ++ tailWord_2836714) baseStart_2836714 baseEnd_2836714 := by
    simpa [prefixWord, tailWord_2836714, baseEnd_2836714] using wordTrace_append hprefix tailTrace_2836714
  have hstable : (prefixWord ++ tailWord_2836714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836714).length < 2 ^ (prefixWord ++ tailWord_2836714).sum := by decide
  have hdescent : baseEnd_2836714 < baseStart_2836714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836729 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_2836729 : Nat := 118140960795 + 2836729 * 2 ^ 59
def prefixEnd_2836729 : Nat := 4983230072969 + 3 ^ 40 * 2836729 * 2
def baseEnd_2836729 : Nat := 971070309032091345627751

theorem tailTrace_2836729 : CollatzResearch.WordTrace tailWord_2836729 prefixEnd_2836729 971070309032091345627751 := by
  unfold tailWord_2836729
  simp only [CollatzResearch.WordTrace]
  refine ⟨103464006540022782587305241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68976004360015188391536827 103464006540022782587305241)
  ·
    refine ⟨77598004905017086940478931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103464006540022782587305241 77598004905017086940478931)
    ·
      refine ⟨116397007357525630410718397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77598004905017086940478931 116397007357525630410718397)
      ·
        refine ⟨43648877759072111404019399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116397007357525630410718397 43648877759072111404019399)
        ·
          refine ⟨65473316638608167106029099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43648877759072111404019399 65473316638608167106029099)
          ·
            refine ⟨98209974957912250659043649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65473316638608167106029099 98209974957912250659043649)
            ·
              refine ⟨73657481218434187994282737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98209974957912250659043649 73657481218434187994282737)
              ·
                refine ⟨55243110913825640995712053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73657481218434187994282737 55243110913825640995712053)
                ·
                  refine ⟨5179041648171153843348005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55243110913825640995712053 5179041648171153843348005)
                  ·
                    refine ⟨971070309032091345627751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5179041648171153843348005 971070309032091345627751)
                    ·
                      rfl

theorem cell22_2836729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_2836729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836729 prefixEnd_2836729 := by exact prefixLift 2836729
  have htrace : WordTrace (prefixWord ++ tailWord_2836729) baseStart_2836729 baseEnd_2836729 := by
    simpa [prefixWord, tailWord_2836729, baseEnd_2836729] using wordTrace_append hprefix tailTrace_2836729
  have hstable : (prefixWord ++ tailWord_2836729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836729).length < 2 ^ (prefixWord ++ tailWord_2836729).sum := by decide
  have hdescent : baseEnd_2836729 < baseStart_2836729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836793 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_2836793 : Nat := 118140960795 + 2836793 * 2 ^ 59
def prefixEnd_2836793 : Nat := 4983230072969 + 3 ^ 40 * 2836793 * 2
def baseEnd_2836793 : Nat := 971092217540016512027555

theorem tailTrace_2836793 : CollatzResearch.WordTrace tailWord_2836793 prefixEnd_2836793 971092217540016512027555 := by
  unfold tailWord_2836793
  simp only [CollatzResearch.WordTrace]
  refine ⟨103466340811790921517635033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68977560541193947678423355 103466340811790921517635033)
  ·
    refine ⟨77599755608843191138226275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103466340811790921517635033 77599755608843191138226275)
    ·
      refine ⟨116399633413264786707339413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77599755608843191138226275 116399633413264786707339413)
      ·
        refine ⟨5456232816246786876906535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116399633413264786707339413 5456232816246786876906535)
        ·
          refine ⟨8184349224370180315359803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456232816246786876906535 8184349224370180315359803)
          ·
            refine ⟨12276523836555270473039705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8184349224370180315359803 12276523836555270473039705)
            ·
              refine ⟨9207392877416452854779779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12276523836555270473039705 9207392877416452854779779)
              ·
                refine ⟨13811089316124679282169669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9207392877416452854779779 13811089316124679282169669)
                ·
                  refine ⟨2589579246773377365406813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13811089316124679282169669 2589579246773377365406813)
                  ·
                    refine ⟨971092217540016512027555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589579246773377365406813 971092217540016512027555)
                    ·
                      rfl

theorem cell22_2836793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_2836793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836793 prefixEnd_2836793 := by exact prefixLift 2836793
  have htrace : WordTrace (prefixWord ++ tailWord_2836793) baseStart_2836793 baseEnd_2836793 := by
    simpa [prefixWord, tailWord_2836793, baseEnd_2836793] using wordTrace_append hprefix tailTrace_2836793
  have hstable : (prefixWord ++ tailWord_2836793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836793).length < 2 ^ (prefixWord ++ tailWord_2836793).sum := by decide
  have hdescent : baseEnd_2836793 < baseStart_2836793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836819 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_2836819 : Nat := 118140960795 + 2836819 * 2 ^ 59
def prefixEnd_2836819 : Nat := 4983230072969 + 3 ^ 40 * 2836819 * 2
def baseEnd_2836819 : Nat := 971101117871361110877475

theorem tailTrace_2836819 : CollatzResearch.WordTrace tailWord_2836819 prefixEnd_2836819 971101117871361110877475 := by
  unfold tailWord_2836819
  simp only [CollatzResearch.WordTrace]
  refine ⟨103467289109696727958081511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68978192739797818638721007 103467289109696727958081511)
  ·
    refine ⟨155200933664545091937122267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103467289109696727958081511 155200933664545091937122267)
    ·
      refine ⟨232801400496817637905683401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155200933664545091937122267 232801400496817637905683401)
      ·
        refine ⟨174601050372613228429262551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232801400496817637905683401 174601050372613228429262551)
        ·
          refine ⟨261901575558919842643893827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174601050372613228429262551 261901575558919842643893827)
          ·
            refine ⟨392852363338379763965840741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261901575558919842643893827 392852363338379763965840741)
            ·
              refine ⟨73659818125946205743595139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 392852363338379763965840741 73659818125946205743595139)
              ·
                refine ⟨110489727188919308615392709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73659818125946205743595139 110489727188919308615392709)
                ·
                  refine ⟨20716823847922370365386133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110489727188919308615392709 20716823847922370365386133)
                  ·
                    refine ⟨971101117871361110877475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20716823847922370365386133 971101117871361110877475)
                    ·
                      rfl

theorem cell22_2836819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_2836819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836819 prefixEnd_2836819 := by exact prefixLift 2836819
  have htrace : WordTrace (prefixWord ++ tailWord_2836819) baseStart_2836819 baseEnd_2836819 := by
    simpa [prefixWord, tailWord_2836819, baseEnd_2836819] using wordTrace_append hprefix tailTrace_2836819
  have hstable : (prefixWord ++ tailWord_2836819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836819).length < 2 ^ (prefixWord ++ tailWord_2836819).sum := by decide
  have hdescent : baseEnd_2836819 < baseStart_2836819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836913 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 6]
def baseStart_2836913 : Nat := 118140960795 + 2836913 * 2 ^ 59
def prefixEnd_2836913 : Nat := 4983230072969 + 3 ^ 40 * 2836913 * 2
def baseEnd_2836913 : Nat := 323711098664125399675729

theorem tailTrace_2836913 : CollatzResearch.WordTrace tailWord_2836913 prefixEnd_2836913 323711098664125399675729 := by
  unfold tailWord_2836913
  simp only [CollatzResearch.WordTrace]
  refine ⟨103470717571356182012003393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68980478380904121341335595 103470717571356182012003393)
  ·
    refine ⟨77603038178517136509002545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103470717571356182012003393 77603038178517136509002545)
    ·
      refine ⟨58202278633887852381751909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77603038178517136509002545 58202278633887852381751909)
      ·
        refine ⟨10912927243853972321578483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58202278633887852381751909 10912927243853972321578483)
        ·
          refine ⟨16369390865780958482367725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10912927243853972321578483 16369390865780958482367725)
          ·
            refine ⟨6138521574667859430887897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16369390865780958482367725 6138521574667859430887897)
            ·
              refine ⟨4603891181000894573165923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6138521574667859430887897 4603891181000894573165923)
              ·
                refine ⟨6905836771501341859748885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603891181000894573165923 6905836771501341859748885)
                ·
                  refine ⟨323711098664125399675729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6905836771501341859748885 323711098664125399675729)
                  ·
                    rfl

theorem cell22_2836913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_2836913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836913 prefixEnd_2836913 := by exact prefixLift 2836913
  have htrace : WordTrace (prefixWord ++ tailWord_2836913) baseStart_2836913 baseEnd_2836913 := by
    simpa [prefixWord, tailWord_2836913, baseEnd_2836913] using wordTrace_append hprefix tailTrace_2836913
  have hstable : (prefixWord ++ tailWord_2836913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836913).length < 2 ^ (prefixWord ++ tailWord_2836913).sum := by decide
  have hdescent : baseEnd_2836913 < baseStart_2836913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836932 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2836932 : Nat := 118140960795 + 2836932 * 2 ^ 59
def prefixEnd_2836932 : Nat := 4983230072969 + 3 ^ 40 * 2836932 * 2
def baseEnd_2836932 : Nat := 971139800080666482802129

theorem tailTrace_2836932 : CollatzResearch.WordTrace tailWord_2836932 prefixEnd_2836932 971139800080666482802129 := by
  unfold tailWord_2836932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51735705279143674128472525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68980940372191565504630033 51735705279143674128472525)
  ·
    refine ⟨19400889479678877798177197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51735705279143674128472525 19400889479678877798177197)
    ·
      refine ⟨7275333554879579174316449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19400889479678877798177197 7275333554879579174316449)
      ·
        refine ⟨5456500166159684380737337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7275333554879579174316449 5456500166159684380737337)
        ·
          refine ⟨4092375124619763285553003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5456500166159684380737337 4092375124619763285553003)
          ·
            refine ⟨6138562686929644928329505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092375124619763285553003 6138562686929644928329505)
            ·
              refine ⟨4603922015197233696247129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6138562686929644928329505 4603922015197233696247129)
              ·
                refine ⟨3452941511397925272185347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4603922015197233696247129 3452941511397925272185347)
                ·
                  refine ⟨5179412267096887908278021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452941511397925272185347 5179412267096887908278021)
                  ·
                    refine ⟨971139800080666482802129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5179412267096887908278021 971139800080666482802129)
                    ·
                      rfl

theorem cell22_2836932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2836932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836932 prefixEnd_2836932 := by exact prefixLift 2836932
  have htrace : WordTrace (prefixWord ++ tailWord_2836932) baseStart_2836932 baseEnd_2836932 := by
    simpa [prefixWord, tailWord_2836932, baseEnd_2836932] using wordTrace_append hprefix tailTrace_2836932
  have hstable : (prefixWord ++ tailWord_2836932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836932).length < 2 ^ (prefixWord ++ tailWord_2836932).sum := by decide
  have hdescent : baseEnd_2836932 < baseStart_2836932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836971 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 2, 6]
def baseStart_2836971 : Nat := 118140960795 + 2836971 * 2 ^ 59
def prefixEnd_2836971 : Nat := 4983230072969 + 3 ^ 40 * 2836971 * 2
def baseEnd_2836971 : Nat := 971153150577683381077009

theorem tailTrace_2836971 : CollatzResearch.WordTrace tailWord_2836971 prefixEnd_2836971 971153150577683381077009 := by
  unfold tailWord_2836971
  simp only [CollatzResearch.WordTrace]
  refine ⟨103472833005146057917614767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68981888670097371945076511 103472833005146057917614767)
  ·
    refine ⟨155209249507719086876422151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103472833005146057917614767 155209249507719086876422151)
    ·
      refine ⟨232813874261578630314633227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155209249507719086876422151 232813874261578630314633227)
      ·
        refine ⟨349220811392367945471949841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232813874261578630314633227 349220811392367945471949841)
        ·
          refine ⟨261915608544275959103962381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349220811392367945471949841 261915608544275959103962381)
          ·
            refine ⟨98218353204103484663985893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261915608544275959103962381 98218353204103484663985893)
            ·
              refine ⟨18415941225769403374497355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98218353204103484663985893 18415941225769403374497355)
              ·
                refine ⟨27623911838654105061746033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18415941225769403374497355 27623911838654105061746033)
                ·
                  refine ⟨20717933878990578796309525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27623911838654105061746033 20717933878990578796309525)
                  ·
                    refine ⟨971153150577683381077009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20717933878990578796309525 971153150577683381077009)
                    ·
                      rfl

theorem cell22_2836971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_2836971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836971 prefixEnd_2836971 := by exact prefixLift 2836971
  have htrace : WordTrace (prefixWord ++ tailWord_2836971) baseStart_2836971 baseEnd_2836971 := by
    simpa [prefixWord, tailWord_2836971, baseEnd_2836971] using wordTrace_append hprefix tailTrace_2836971
  have hstable : (prefixWord ++ tailWord_2836971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836971).length < 2 ^ (prefixWord ++ tailWord_2836971).sum := by decide
  have hdescent : baseEnd_2836971 < baseStart_2836971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2836986 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_2836986 : Nat := 118140960795 + 2836986 * 2 ^ 59
def prefixEnd_2836986 : Nat := 4983230072969 + 3 ^ 40 * 2836986 * 2
def baseEnd_2836986 : Nat := 323719428461409447317321

theorem tailTrace_2836986 : CollatzResearch.WordTrace tailWord_2836986 prefixEnd_2836986 323719428461409447317321 := by
  unfold tailWord_2836986
  simp only [CollatzResearch.WordTrace]
  refine ⟨25868345025022928869852703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68982253400061143652940541 25868345025022928869852703)
  ·
    refine ⟨38802517537534393304779055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25868345025022928869852703 38802517537534393304779055)
    ·
      refine ⟨58203776306301589957168583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38802517537534393304779055 58203776306301589957168583)
      ·
        refine ⟨87305664459452384935752875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58203776306301589957168583 87305664459452384935752875)
        ·
          refine ⟨130958496689178577403629313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87305664459452384935752875 130958496689178577403629313)
          ·
            refine ⟨98218872516883933052721985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130958496689178577403629313 98218872516883933052721985)
            ·
              refine ⟨73664154387662949789541489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98218872516883933052721985 73664154387662949789541489)
              ·
                refine ⟨55248115790747212342156117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73664154387662949789541489 55248115790747212342156117)
                ·
                  refine ⟨323719428461409447317321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55248115790747212342156117 323719428461409447317321)
                  ·
                    rfl

theorem cell22_2836986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_2836986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2836986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2836986 prefixEnd_2836986 := by exact prefixLift 2836986
  have htrace : WordTrace (prefixWord ++ tailWord_2836986) baseStart_2836986 baseEnd_2836986 := by
    simpa [prefixWord, tailWord_2836986, baseEnd_2836986] using wordTrace_append hprefix tailTrace_2836986
  have hstable : (prefixWord ++ tailWord_2836986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2836986).length < 2 ^ (prefixWord ++ tailWord_2836986).sum := by decide
  have hdescent : baseEnd_2836986 < baseStart_2836986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2836986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837001 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_2837001 : Nat := 118140960795 + 2837001 * 2 ^ 59
def prefixEnd_2837001 : Nat := 4983230072969 + 3 ^ 40 * 2837001 * 2
def baseEnd_2837001 : Nat := 971163420190773302826917

theorem tailTrace_2837001 : CollatzResearch.WordTrace tailWord_2837001 prefixEnd_2837001 971163420190773302826917 := by
  unfold tailWord_2837001
  simp only [CollatzResearch.WordTrace]
  refine ⟨103473927195037373041206857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68982618130024915360804571 103473927195037373041206857)
  ·
    refine ⟨77605445396278029780905143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103473927195037373041206857 77605445396278029780905143)
    ·
      refine ⟨116408168094417044671357715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77605445396278029780905143 116408168094417044671357715)
      ·
        refine ⟨174612252141625567007036573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116408168094417044671357715 174612252141625567007036573)
        ·
          refine ⟨65479594553109587627638715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174612252141625567007036573 65479594553109587627638715)
          ·
            refine ⟨98219391829664381441458073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65479594553109587627638715 98219391829664381441458073)
            ·
              refine ⟨73664543872248286081093555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98219391829664381441458073 73664543872248286081093555)
              ·
                refine ⟨110496815808372429121640333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73664543872248286081093555 110496815808372429121640333)
                ·
                  refine ⟨41436305928139660920615125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110496815808372429121640333 41436305928139660920615125)
                  ·
                    refine ⟨971163420190773302826917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41436305928139660920615125 971163420190773302826917)
                    ·
                      rfl

theorem cell22_2837001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_2837001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837001 prefixEnd_2837001 := by exact prefixLift 2837001
  have htrace : WordTrace (prefixWord ++ tailWord_2837001) baseStart_2837001 baseEnd_2837001 := by
    simpa [prefixWord, tailWord_2837001, baseEnd_2837001] using wordTrace_append hprefix tailTrace_2837001
  have hstable : (prefixWord ++ tailWord_2837001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837001).length < 2 ^ (prefixWord ++ tailWord_2837001).sum := by decide
  have hdescent : baseEnd_2837001 < baseStart_2837001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837020 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_2837020 : Nat := 118140960795 + 2837020 * 2 ^ 59
def prefixEnd_2837020 : Nat := 4983230072969 + 3 ^ 40 * 2837020 * 2
def baseEnd_2837020 : Nat := 323723308093021195533953

theorem tailTrace_2837020 : CollatzResearch.WordTrace tailWord_2837020 prefixEnd_2837020 323723308093021195533953 := by
  unfold tailWord_2837020
  simp only [CollatzResearch.WordTrace]
  refine ⟨51737310090984269643074257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68983080121312359524099009 51737310090984269643074257)
  ·
    refine ⟨38802982568238202232305693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51737310090984269643074257 38802982568238202232305693)
    ·
      refine ⟨14551118463089325837114635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38802982568238202232305693 14551118463089325837114635)
      ·
        refine ⟨21826677694633988755671953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14551118463089325837114635 21826677694633988755671953)
        ·
          refine ⟨16370008270975491566753965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21826677694633988755671953 16370008270975491566753965)
          ·
            refine ⟨6138753101615809337532737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16370008270975491566753965 6138753101615809337532737)
            ·
              refine ⟨4604064826211857003149553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6138753101615809337532737 4604064826211857003149553)
              ·
                refine ⟨3453048619658892752362165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604064826211857003149553 3453048619658892752362165)
                ·
                  refine ⟨323723308093021195533953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453048619658892752362165 323723308093021195533953)
                  ·
                    rfl

theorem cell22_2837020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_2837020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837020 prefixEnd_2837020 := by exact prefixLift 2837020
  have htrace : WordTrace (prefixWord ++ tailWord_2837020) baseStart_2837020 baseEnd_2837020 := by
    simpa [prefixWord, tailWord_2837020, baseEnd_2837020] using wordTrace_append hprefix tailTrace_2837020
  have hstable : (prefixWord ++ tailWord_2837020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837020).length < 2 ^ (prefixWord ++ tailWord_2837020).sum := by decide
  have hdescent : baseEnd_2837020 < baseStart_2837020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837024 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 1, 3]
def baseStart_2837024 : Nat := 118140960795 + 2837024 * 2 ^ 59
def prefixEnd_2837024 : Nat := 4983230072969 + 3 ^ 40 * 2837024 * 2
def baseEnd_2837024 : Nat := 971171293560808909501847

theorem tailTrace_2837024 : CollatzResearch.WordTrace tailWord_2837024 prefixEnd_2837024 971171293560808909501847 := by
  unfold tailWord_2837024
  simp only [CollatzResearch.WordTrace]
  refine ⟨51737383036977023984647063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68983177382636031979529417 51737383036977023984647063)
  ·
    refine ⟨77606074555465535976970595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51737383036977023984647063 77606074555465535976970595)
    ·
      refine ⟨116409111833198303965455893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77606074555465535976970595 116409111833198303965455893)
      ·
        refine ⟨5456677117181170498380745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116409111833198303965455893 5456677117181170498380745)
        ·
          refine ⟨4092507837885877873785559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5456677117181170498380745 4092507837885877873785559)
          ·
            refine ⟨6138761756828816810678339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092507837885877873785559 6138761756828816810678339)
            ·
              refine ⟨9208142635243225216017509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138761756828816810678339 9208142635243225216017509)
              ·
                refine ⟨1726526744108104728003283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9208142635243225216017509 1726526744108104728003283)
                ·
                  refine ⟨2589790116162157092004925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726526744108104728003283 2589790116162157092004925)
                  ·
                    refine ⟨971171293560808909501847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589790116162157092004925 971171293560808909501847)
                    ·
                      rfl

theorem cell22_2837024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_2837024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837024 prefixEnd_2837024 := by exact prefixLift 2837024
  have htrace : WordTrace (prefixWord ++ tailWord_2837024) baseStart_2837024 baseEnd_2837024 := by
    simpa [prefixWord, tailWord_2837024, baseEnd_2837024] using wordTrace_append hprefix tailTrace_2837024
  have hstable : (prefixWord ++ tailWord_2837024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837024).length < 2 ^ (prefixWord ++ tailWord_2837024).sum := by decide
  have hdescent : baseEnd_2837024 < baseStart_2837024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837048 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_2837048 : Nat := 118140960795 + 2837048 * 2 ^ 59
def prefixEnd_2837048 : Nat := 4983230072969 + 3 ^ 40 * 2837048 * 2
def baseEnd_2837048 : Nat := 323726503083760282300591

theorem tailTrace_2837048 : CollatzResearch.WordTrace tailWord_2837048 prefixEnd_2837048 323726503083760282300591 := by
  unfold tailWord_2837048
  simp only [CollatzResearch.WordTrace]
  refine ⟨51737820712933550034083899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68983760950578066712111865 51737820712933550034083899)
  ·
    refine ⟨77606731069400325051125849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51737820712933550034083899 77606731069400325051125849)
    ·
      refine ⟨58205048302050243788344387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77606731069400325051125849 58205048302050243788344387)
      ·
        refine ⟨87307572453075365682516581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58205048302050243788344387 87307572453075365682516581)
        ·
          refine ⟨16370169834951631065471859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87307572453075365682516581 16370169834951631065471859)
          ·
            refine ⟨24555254752427446598207789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16370169834951631065471859 24555254752427446598207789)
            ·
              refine ⟨9208220532160292474327921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24555254752427446598207789 9208220532160292474327921)
              ·
                refine ⟨6906165399120219355745941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9208220532160292474327921 6906165399120219355745941)
                ·
                  refine ⟨323726503083760282300591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6906165399120219355745941 323726503083760282300591)
                  ·
                    rfl

theorem cell22_2837048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_2837048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837048 prefixEnd_2837048 := by exact prefixLift 2837048
  have htrace : WordTrace (prefixWord ++ tailWord_2837048) baseStart_2837048 baseEnd_2837048 := by
    simpa [prefixWord, tailWord_2837048, baseEnd_2837048] using wordTrace_append hprefix tailTrace_2837048
  have hstable : (prefixWord ++ tailWord_2837048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837048).length < 2 ^ (prefixWord ++ tailWord_2837048).sum := by decide
  have hdescent : baseEnd_2837048 < baseStart_2837048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837215 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 1, 5]
def baseStart_2837215 : Nat := 118140960795 + 2837215 * 2 ^ 59
def prefixEnd_2837215 : Nat := 4983230072969 + 3 ^ 40 * 2837215 * 2
def baseEnd_2837215 : Nat := 971236676764148077976261

theorem tailTrace_2837215 : CollatzResearch.WordTrace tailWord_2837215 prefixEnd_2837215 971236676764148077976261 := by
  unfold tailWord_2837215
  simp only [CollatzResearch.WordTrace]
  refine ⟨103481732416262087589497099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68987821610841391726331399 103481732416262087589497099)
  ·
    refine ⟨155222598624393131384245649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103481732416262087589497099 155222598624393131384245649)
    ·
      refine ⟨116416948968294848538184237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155222598624393131384245649 116416948968294848538184237)
      ·
        refine ⟨43656355863110568201819089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116416948968294848538184237 43656355863110568201819089)
        ·
          refine ⟨32742266897332926151364317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43656355863110568201819089 32742266897332926151364317)
          ·
            refine ⟨12278350086499847306761619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32742266897332926151364317 12278350086499847306761619)
            ·
              refine ⟨18417525129749770960142429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12278350086499847306761619 18417525129749770960142429)
              ·
                refine ⟨6906571923656164110053411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18417525129749770960142429 6906571923656164110053411)
                ·
                  refine ⟨10359857885484246165080117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906571923656164110053411 10359857885484246165080117)
                  ·
                    refine ⟨971236676764148077976261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10359857885484246165080117 971236676764148077976261)
                    ·
                      rfl

theorem cell22_2837215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_2837215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837215 prefixEnd_2837215 := by exact prefixLift 2837215
  have htrace : WordTrace (prefixWord ++ tailWord_2837215) baseStart_2837215 baseEnd_2837215 := by
    simpa [prefixWord, tailWord_2837215, baseEnd_2837215] using wordTrace_append hprefix tailTrace_2837215
  have hstable : (prefixWord ++ tailWord_2837215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837215).length < 2 ^ (prefixWord ++ tailWord_2837215).sum := by decide
  have hdescent : baseEnd_2837215 < baseStart_2837215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837234 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_2837234 : Nat := 118140960795 + 2837234 * 2 ^ 59
def prefixEnd_2837234 : Nat := 4983230072969 + 3 ^ 40 * 2837234 * 2
def baseEnd_2837234 : Nat := 323747726950812787250401

theorem tailTrace_2837234 : CollatzResearch.WordTrace tailWord_2837234 prefixEnd_2837234 323747726950812787250401 := by
  unfold tailWord_2837234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870606350798313458609689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68988283602128835889625837 25870606350798313458609689)
  ·
    refine ⟨19402954763098735093957267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25870606350798313458609689 19402954763098735093957267)
    ·
      refine ⟨29104432144648102640935901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19402954763098735093957267 29104432144648102640935901)
      ·
        refine ⟨10914162054243038490350963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29104432144648102640935901 10914162054243038490350963)
        ·
          refine ⟨16371243081364557735526445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10914162054243038490350963 16371243081364557735526445)
          ·
            refine ⟨6139216155511709150822417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16371243081364557735526445 6139216155511709150822417)
            ·
              refine ⟨4604412116633781863116813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139216155511709150822417 4604412116633781863116813)
              ·
                refine ⟨1726654543737668198668805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4604412116633781863116813 1726654543737668198668805)
                ·
                  refine ⟨323747726950812787250401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726654543737668198668805 323747726950812787250401)
                  ·
                    rfl

theorem cell22_2837234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_2837234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837234 prefixEnd_2837234 := by exact prefixLift 2837234
  have htrace : WordTrace (prefixWord ++ tailWord_2837234) baseStart_2837234 baseEnd_2837234 := by
    simpa [prefixWord, tailWord_2837234, baseEnd_2837234] using wordTrace_append hprefix tailTrace_2837234
  have hstable : (prefixWord ++ tailWord_2837234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837234).length < 2 ^ (prefixWord ++ tailWord_2837234).sum := by decide
  have hdescent : baseEnd_2837234 < baseStart_2837234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837266 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2837266 : Nat := 118140960795 + 2837266 * 2 ^ 59
def prefixEnd_2837266 : Nat := 4983230072969 + 3 ^ 40 * 2837266 * 2
def baseEnd_2837266 : Nat := 971254135106400944951105

theorem tailTrace_2837266 : CollatzResearch.WordTrace tailWord_2837266 prefixEnd_2837266 971254135106400944951105 := by
  unfold tailWord_2837266
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870898134769330824900913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68989061692718215533069101 25870898134769330824900913)
  ·
    refine ⟨19403173601076998118675685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25870898134769330824900913 19403173601076998118675685)
    ·
      refine ⟨3638095050201937147251691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19403173601076998118675685 3638095050201937147251691)
      ·
        refine ⟨5457142575302905720877537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638095050201937147251691 5457142575302905720877537)
        ·
          refine ⟨4092856931477179290658153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5457142575302905720877537 4092856931477179290658153)
          ·
            refine ⟨3069642698607884467993615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092856931477179290658153 3069642698607884467993615)
            ·
              refine ⟨4604464047911826701990423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069642698607884467993615 4604464047911826701990423)
              ·
                refine ⟨6906696071867740052985635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604464047911826701990423 6906696071867740052985635)
                ·
                  refine ⟨10360044107801610079478453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906696071867740052985635 10360044107801610079478453)
                  ·
                    refine ⟨971254135106400944951105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10360044107801610079478453 971254135106400944951105)
                    ·
                      rfl

theorem cell22_2837266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2837266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837266 prefixEnd_2837266 := by exact prefixLift 2837266
  have htrace : WordTrace (prefixWord ++ tailWord_2837266) baseStart_2837266 baseEnd_2837266 := by
    simpa [prefixWord, tailWord_2837266, baseEnd_2837266] using wordTrace_append hprefix tailTrace_2837266
  have hstable : (prefixWord ++ tailWord_2837266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837266).length < 2 ^ (prefixWord ++ tailWord_2837266).sum := by decide
  have hdescent : baseEnd_2837266 < baseStart_2837266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837324 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 5]
def baseStart_2837324 : Nat := 118140960795 + 2837324 * 2 ^ 59
def prefixEnd_2837324 : Nat := 4983230072969 + 3 ^ 40 * 2837324 * 2
def baseEnd_2837324 : Nat := 323757996563902709000309

theorem tailTrace_2837324 : CollatzResearch.WordTrace tailWord_2837324 prefixEnd_2837324 323757996563902709000309 := by
  unfold tailWord_2837324
  simp only [CollatzResearch.WordTrace]
  refine ⟨51742853986433599602607513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68990471981911466136810017 51742853986433599602607513)
  ·
    refine ⟨38807140489825199701955635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51742853986433599602607513 38807140489825199701955635)
    ·
      refine ⟨58210710734737799552933453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38807140489825199701955635 58210710734737799552933453)
      ·
        refine ⟨21829016525526674832350045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58210710734737799552933453 21829016525526674832350045)
        ·
          refine ⟨8185881197072503062131267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21829016525526674832350045 8185881197072503062131267)
          ·
            refine ⟨12278821795608754593196901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185881197072503062131267 12278821795608754593196901)
            ·
              refine ⟨2302279086676641486224419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12278821795608754593196901 2302279086676641486224419)
              ·
                refine ⟨3453418630014962229336629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302279086676641486224419 3453418630014962229336629)
                ·
                  refine ⟨323757996563902709000309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453418630014962229336629 323757996563902709000309)
                  ·
                    rfl

theorem cell22_2837324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_2837324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837324 prefixEnd_2837324 := by exact prefixLift 2837324
  have htrace : WordTrace (prefixWord ++ tailWord_2837324) baseStart_2837324 baseEnd_2837324 := by
    simpa [prefixWord, tailWord_2837324, baseEnd_2837324] using wordTrace_append hprefix tailTrace_2837324
  have hstable : (prefixWord ++ tailWord_2837324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837324).length < 2 ^ (prefixWord ++ tailWord_2837324).sum := by decide
  have hdescent : baseEnd_2837324 < baseStart_2837324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837337 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_2837337 : Nat := 118140960795 + 2837337 * 2 ^ 59
def prefixEnd_2837337 : Nat := 4983230072969 + 3 ^ 40 * 2837337 * 2
def baseEnd_2837337 : Nat := 971278439857380426425887

theorem tailTrace_2837337 : CollatzResearch.WordTrace tailWord_2837337 prefixEnd_2837337 971278439857380426425887 := by
  unfold tailWord_2837337
  simp only [CollatzResearch.WordTrace]
  refine ⟨103486182121820102425438265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68990788081213401616958843 103486182121820102425438265)
  ·
    refine ⟨77614636591365076819078699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103486182121820102425438265 77614636591365076819078699)
    ·
      refine ⟨116421954887047615228618049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77614636591365076819078699 116421954887047615228618049)
      ·
        refine ⟨87316466165285711421463537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116421954887047615228618049 87316466165285711421463537)
        ·
          refine ⟨65487349623964283566097653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87316466165285711421463537 65487349623964283566097653)
          ·
            refine ⟨6139439027246651584321655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65487349623964283566097653 6139439027246651584321655)
            ·
              refine ⟨9209158540869977376482483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6139439027246651584321655 9209158540869977376482483)
              ·
                refine ⟨13813737811304966064723725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9209158540869977376482483 13813737811304966064723725)
                ·
                  refine ⟨5180151679239362274271397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13813737811304966064723725 5180151679239362274271397)
                  ·
                    refine ⟨971278439857380426425887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180151679239362274271397 971278439857380426425887)
                    ·
                      rfl

theorem cell22_2837337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_2837337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837337 prefixEnd_2837337 := by exact prefixLift 2837337
  have htrace : WordTrace (prefixWord ++ tailWord_2837337) baseStart_2837337 baseEnd_2837337 := by
    simpa [prefixWord, tailWord_2837337, baseEnd_2837337] using wordTrace_append hprefix tailTrace_2837337
  have hstable : (prefixWord ++ tailWord_2837337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837337).length < 2 ^ (prefixWord ++ tailWord_2837337).sum := by decide
  have hdescent : baseEnd_2837337 < baseStart_2837337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837367 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 4, 3]
def baseStart_2837367 : Nat := 118140960795 + 2837367 * 2 ^ 59
def prefixEnd_2837367 : Nat := 4983230072969 + 3 ^ 40 * 2837367 * 2
def baseEnd_2837367 : Nat := 971288709470470348175795

theorem tailTrace_2837367 : CollatzResearch.WordTrace tailWord_2837367 prefixEnd_2837367 971288709470470348175795 := by
  unfold tailWord_2837367
  simp only [CollatzResearch.WordTrace]
  refine ⟨103487276311711417549030355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68991517541140945032686903 103487276311711417549030355)
  ·
    refine ⟨155230914467567126323545533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103487276311711417549030355 155230914467567126323545533)
    ·
      refine ⟨58211592925337672371329575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155230914467567126323545533 58211592925337672371329575)
      ·
        refine ⟨87317389388006508556994363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58211592925337672371329575 87317389388006508556994363)
        ·
          refine ⟨130976084082009762835491545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87317389388006508556994363 130976084082009762835491545)
          ·
            refine ⟨98232063061507322126618659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130976084082009762835491545 98232063061507322126618659)
            ·
              refine ⟨147348094592260983189927989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98232063061507322126618659 147348094592260983189927989)
              ·
                refine ⟨13813883868024467174055749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147348094592260983189927989 13813883868024467174055749)
                ·
                  refine ⟨2590103225254587595135453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13813883868024467174055749 2590103225254587595135453)
                  ·
                    refine ⟨971288709470470348175795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2590103225254587595135453 971288709470470348175795)
                    ·
                      rfl

theorem cell22_2837367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_2837367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837367 prefixEnd_2837367 := by exact prefixLift 2837367
  have htrace : WordTrace (prefixWord ++ tailWord_2837367) baseStart_2837367 baseEnd_2837367 := by
    simpa [prefixWord, tailWord_2837367, baseEnd_2837367] using wordTrace_append hprefix tailTrace_2837367
  have hstable : (prefixWord ++ tailWord_2837367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837367).length < 2 ^ (prefixWord ++ tailWord_2837367).sum := by decide
  have hdescent : baseEnd_2837367 < baseStart_2837367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837369 : List Nat := [1, 2, 1, 3, 2, 4, 1, 4, 4]
def baseStart_2837369 : Nat := 118140960795 + 2837369 * 2 ^ 59
def prefixEnd_2837369 : Nat := 4983230072969 + 3 ^ 40 * 2837369 * 2
def baseEnd_2837369 : Nat := 323763131370447669875263

theorem tailTrace_2837369 : CollatzResearch.WordTrace tailWord_2837369 prefixEnd_2837369 323763131370447669875263 := by
  unfold tailWord_2837369
  simp only [CollatzResearch.WordTrace]
  refine ⟨103487349257704171890603161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68991566171802781260402107 103487349257704171890603161)
  ·
    refine ⟨77615511943278128917952371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103487349257704171890603161 77615511943278128917952371)
    ·
      refine ⟨116423267914917193376928557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77615511943278128917952371 116423267914917193376928557)
      ·
        refine ⟨43658725468093947516348209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116423267914917193376928557 43658725468093947516348209)
        ·
          refine ⟨32744044101070460637261157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43658725468093947516348209 32744044101070460637261157)
          ·
            refine ⟨6139508268950711369486467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32744044101070460637261157 6139508268950711369486467)
            ·
              refine ⟨9209262403426067054229701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6139508268950711369486467 9209262403426067054229701)
              ·
                refine ⟨1726736700642387572668069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9209262403426067054229701 1726736700642387572668069)
                ·
                  refine ⟨323763131370447669875263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726736700642387572668069 323763131370447669875263)
                  ·
                    rfl

theorem cell22_2837369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_2837369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837369 prefixEnd_2837369 := by exact prefixLift 2837369
  have htrace : WordTrace (prefixWord ++ tailWord_2837369) baseStart_2837369 baseEnd_2837369 := by
    simpa [prefixWord, tailWord_2837369, baseEnd_2837369] using wordTrace_append hprefix tailTrace_2837369
  have hstable : (prefixWord ++ tailWord_2837369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837369).length < 2 ^ (prefixWord ++ tailWord_2837369).sum := by decide
  have hdescent : baseEnd_2837369 < baseStart_2837369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837384 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_2837384 : Nat := 118140960795 + 2837384 * 2 ^ 59
def prefixEnd_2837384 : Nat := 4983230072969 + 3 ^ 40 * 2837384 * 2
def baseEnd_2837384 : Nat := 971294528917887970500743

theorem tailTrace_2837384 : CollatzResearch.WordTrace tailWord_2837384 prefixEnd_2837384 971294528917887970500743 := by
  unfold tailWord_2837384
  simp only [CollatzResearch.WordTrace]
  refine ⟨51743948176324914726199603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68991930901766552968266137 51743948176324914726199603)
  ·
    refine ⟨77615922264487372089299405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51743948176324914726199603 77615922264487372089299405)
    ·
      refine ⟨29105970849182764533487277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77615922264487372089299405 29105970849182764533487277)
      ·
        refine ⟨10914739068443536700057729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29105970849182764533487277 10914739068443536700057729)
        ·
          refine ⟨8186054301332652525043297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10914739068443536700057729 8186054301332652525043297)
          ·
            refine ⟨6139540725999489393782473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8186054301332652525043297 6139540725999489393782473)
            ·
              refine ⟨4604655544499617045336855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139540725999489393782473 4604655544499617045336855)
              ·
                refine ⟨6906983316749425568005283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604655544499617045336855 6906983316749425568005283)
                ·
                  refine ⟨10360474975124138352007925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906983316749425568005283 10360474975124138352007925)
                  ·
                    refine ⟨971294528917887970500743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10360474975124138352007925 971294528917887970500743)
                    ·
                      rfl

theorem cell22_2837384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_2837384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837384 prefixEnd_2837384 := by exact prefixLift 2837384
  have htrace : WordTrace (prefixWord ++ tailWord_2837384) baseStart_2837384 baseEnd_2837384 := by
    simpa [prefixWord, tailWord_2837384, baseEnd_2837384] using wordTrace_append hprefix tailTrace_2837384
  have hstable : (prefixWord ++ tailWord_2837384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837384).length < 2 ^ (prefixWord ++ tailWord_2837384).sum := by decide
  have hdescent : baseEnd_2837384 < baseStart_2837384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837395 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 9]
def baseStart_2837395 : Nat := 118140960795 + 2837395 * 2 ^ 59
def prefixEnd_2837395 : Nat := 4983230072969 + 3 ^ 40 * 2837395 * 2
def baseEnd_2837395 : Nat := 971298294442687608475709

theorem tailTrace_2837395 : CollatzResearch.WordTrace tailWord_2837395 prefixEnd_2837395 971298294442687608475709 := by
  unfold tailWord_2837395
  simp only [CollatzResearch.WordTrace]
  refine ⟨103488297555609978331049639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68992198370406652220699759 103488297555609978331049639)
  ·
    refine ⟨155232446333414967496574459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103488297555609978331049639 155232446333414967496574459)
    ·
      refine ⟨232848669500122451244861689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155232446333414967496574459 232848669500122451244861689)
      ·
        refine ⟨174636502125091838433646267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232848669500122451244861689 174636502125091838433646267)
        ·
          refine ⟨261954753187637757650469401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174636502125091838433646267 261954753187637757650469401)
          ·
            refine ⟨196466064890728318237852051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261954753187637757650469401 196466064890728318237852051)
            ·
              refine ⟨294699097336092477356778077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196466064890728318237852051 294699097336092477356778077)
              ·
                refine ⟨110512161501034679008791779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294699097336092477356778077 110512161501034679008791779)
                ·
                  refine ⟨165768242251552018513187669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110512161501034679008791779 165768242251552018513187669)
                  ·
                    refine ⟨971298294442687608475709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 165768242251552018513187669 971298294442687608475709)
                    ·
                      rfl

theorem cell22_2837395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_2837395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837395 prefixEnd_2837395 := by exact prefixLift 2837395
  have htrace : WordTrace (prefixWord ++ tailWord_2837395) baseStart_2837395 baseEnd_2837395 := by
    simpa [prefixWord, tailWord_2837395, baseEnd_2837395] using wordTrace_append hprefix tailTrace_2837395
  have hstable : (prefixWord ++ tailWord_2837395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837395).length < 2 ^ (prefixWord ++ tailWord_2837395).sum := by decide
  have hdescent : baseEnd_2837395 < baseStart_2837395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837472 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_2837472 : Nat := 118140960795 + 2837472 * 2 ^ 59
def prefixEnd_2837472 : Nat := 4983230072969 + 3 ^ 40 * 2837472 * 2
def baseEnd_2837472 : Nat := 971324653116285074300473

theorem tailTrace_2837472 : CollatzResearch.WordTrace tailWord_2837472 prefixEnd_2837472 971324653116285074300473 := by
  unfold tailWord_2837472
  simp only [CollatzResearch.WordTrace]
  refine ⟨51745552988165510240801335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68994070650887346987735113 51745552988165510240801335)
  ·
    refine ⟨77618329482248265361202003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51745552988165510240801335 77618329482248265361202003)
    ·
      refine ⟨116427494223372398041803005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77618329482248265361202003 116427494223372398041803005)
      ·
        refine ⟨43660310333764649265676127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116427494223372398041803005 43660310333764649265676127)
        ·
          refine ⟨65490465500646973898514191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43660310333764649265676127 65490465500646973898514191)
          ·
            refine ⟨98235698250970460847771287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65490465500646973898514191 98235698250970460847771287)
            ·
              refine ⟨147353547376455691271656931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98235698250970460847771287 147353547376455691271656931)
              ·
                refine ⟨221030321064683536907485397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147353547376455691271656931 221030321064683536907485397)
                ·
                  refine ⟨5180398149953520396269189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 221030321064683536907485397 5180398149953520396269189)
                  ·
                    refine ⟨971324653116285074300473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180398149953520396269189 971324653116285074300473)
                    ·
                      rfl

theorem cell22_2837472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_2837472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837472 prefixEnd_2837472 := by exact prefixLift 2837472
  have htrace : WordTrace (prefixWord ++ tailWord_2837472) baseStart_2837472 baseEnd_2837472 := by
    simpa [prefixWord, tailWord_2837472, baseEnd_2837472] using wordTrace_append hprefix tailTrace_2837472
  have hstable : (prefixWord ++ tailWord_2837472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837472).length < 2 ^ (prefixWord ++ tailWord_2837472).sum := by decide
  have hdescent : baseEnd_2837472 < baseStart_2837472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837493 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 5]
def baseStart_2837493 : Nat := 118140960795 + 2837493 * 2 ^ 59
def prefixEnd_2837493 : Nat := 4983230072969 + 3 ^ 40 * 2837493 * 2
def baseEnd_2837493 : Nat := 323777280615149339841803

theorem tailTrace_2837493 : CollatzResearch.WordTrace tailWord_2837493 prefixEnd_2837493 323777280615149339841803 := by
  unfold tailWord_2837493
  simp only [CollatzResearch.WordTrace]
  refine ⟨103491871909254941068117133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68994581272836627378744755 103491871909254941068117133)
  ·
    refine ⟨38809451965970602900543925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103491871909254941068117133 38809451965970602900543925)
    ·
      refine ⟨3638386121809744021925993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38809451965970602900543925 3638386121809744021925993)
      ·
        refine ⟨2728789591357308016444495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3638386121809744021925993 2728789591357308016444495)
        ·
          refine ⟨4093184387035962024666743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2728789591357308016444495 4093184387035962024666743)
          ·
            refine ⟨6139776580553943037000115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093184387035962024666743 6139776580553943037000115)
            ·
              refine ⟨9209664870830914555500173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6139776580553943037000115 9209664870830914555500173)
              ·
                refine ⟨3453624326561592958312565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9209664870830914555500173 3453624326561592958312565)
                ·
                  refine ⟨323777280615149339841803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453624326561592958312565 323777280615149339841803)
                  ·
                    rfl

theorem cell22_2837493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_2837493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837493 prefixEnd_2837493 := by exact prefixLift 2837493
  have htrace : WordTrace (prefixWord ++ tailWord_2837493) baseStart_2837493 baseEnd_2837493 := by
    simpa [prefixWord, tailWord_2837493, baseEnd_2837493] using wordTrace_append hprefix tailTrace_2837493
  have hstable : (prefixWord ++ tailWord_2837493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837493).length < 2 ^ (prefixWord ++ tailWord_2837493).sum := by decide
  have hdescent : baseEnd_2837493 < baseStart_2837493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837532 : List Nat := [2, 2, 3, 1, 14]
def baseStart_2837532 : Nat := 118140960795 + 2837532 * 2 ^ 59
def prefixEnd_2837532 : Nat := 4983230072969 + 3 ^ 40 * 2837532 * 2
def baseEnd_2837532 : Nat := 3997305318281748632923

theorem tailTrace_2837532 : CollatzResearch.WordTrace tailWord_2837532 prefixEnd_2837532 3997305318281748632923 := by
  unfold tailWord_2837532
  simp only [CollatzResearch.WordTrace]
  refine ⟨51746647178056825364393425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68995529570742433819191233 51746647178056825364393425)
  ·
    refine ⟨38809985383542619023295069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51746647178056825364393425 38809985383542619023295069)
    ·
      refine ⟨14553744518828482133735651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38809985383542619023295069 14553744518828482133735651)
      ·
        refine ⟨21830616778242723200603477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553744518828482133735651 21830616778242723200603477)
        ·
          refine ⟨3997305318281748632923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 21830616778242723200603477 3997305318281748632923)
          ·
            rfl

theorem cell22_2837532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 14].length) (baseStart_2837532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837532 prefixEnd_2837532 := by exact prefixLift 2837532
  have htrace : WordTrace (prefixWord ++ tailWord_2837532) baseStart_2837532 baseEnd_2837532 := by
    simpa [prefixWord, tailWord_2837532, baseEnd_2837532] using wordTrace_append hprefix tailTrace_2837532
  have hstable : (prefixWord ++ tailWord_2837532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837532).length < 2 ^ (prefixWord ++ tailWord_2837532).sum := by decide
  have hdescent : baseEnd_2837532 < baseStart_2837532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837538 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_2837538 : Nat := 118140960795 + 2837538 * 2 ^ 59
def prefixEnd_2837538 : Nat := 4983230072969 + 3 ^ 40 * 2837538 * 2
def baseEnd_2837538 : Nat := 323782415421694300716757

theorem tailTrace_2837538 : CollatzResearch.WordTrace tailWord_2837538 prefixEnd_2837538 323782415421694300716757 := by
  unfold tailWord_2837538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25873378298522978438376317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68995675462727942502336845 25873378298522978438376317)
  ·
    refine ⟨9702516861946116914391119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25873378298522978438376317 9702516861946116914391119)
    ·
      refine ⟨14553775292919175371586679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9702516861946116914391119 14553775292919175371586679)
      ·
        refine ⟨21830662939378763057380019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14553775292919175371586679 21830662939378763057380019)
        ·
          refine ⟨32745994409068144586070029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21830662939378763057380019 32745994409068144586070029)
          ·
            refine ⟨12279747903400554219776261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32745994409068144586070029 12279747903400554219776261)
            ·
              refine ⟨2302452731887603916208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12279747903400554219776261 2302452731887603916208049)
              ·
                refine ⟨1726839548915702937156037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302452731887603916208049 1726839548915702937156037)
                ·
                  refine ⟨323782415421694300716757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726839548915702937156037 323782415421694300716757)
                  ·
                    rfl

theorem cell22_2837538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_2837538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837538 prefixEnd_2837538 := by exact prefixLift 2837538
  have htrace : WordTrace (prefixWord ++ tailWord_2837538) baseStart_2837538 baseEnd_2837538 := by
    simpa [prefixWord, tailWord_2837538, baseEnd_2837538] using wordTrace_append hprefix tailTrace_2837538
  have hstable : (prefixWord ++ tailWord_2837538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837538).length < 2 ^ (prefixWord ++ tailWord_2837538).sum := by decide
  have hdescent : baseEnd_2837538 < baseStart_2837538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837594 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_2837594 : Nat := 118140960795 + 2837594 * 2 ^ 59
def prefixEnd_2837594 : Nat := 4983230072969 + 3 ^ 40 * 2837594 * 2
def baseEnd_2837594 : Nat := 323788805403172474250033

theorem tailTrace_2837594 : CollatzResearch.WordTrace tailWord_2837594 prefixEnd_2837594 323788805403172474250033 := by
  unfold tailWord_2837594
  simp only [CollatzResearch.WordTrace]
  refine ⟨25873888920472258829385959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68997037121259356878362557 25873888920472258829385959)
  ·
    refine ⟨38810833380708388244078939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25873888920472258829385959 38810833380708388244078939)
    ·
      refine ⟨58216250071062582366118409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38810833380708388244078939 58216250071062582366118409)
      ·
        refine ⟨43662187553296936774588807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58216250071062582366118409 43662187553296936774588807)
        ·
          refine ⟨65493281329945405161883211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43662187553296936774588807 65493281329945405161883211)
          ·
            refine ⟨98239921994918107742824817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65493281329945405161883211 98239921994918107742824817)
            ·
              refine ⟨73679941496188580807118613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98239921994918107742824817 73679941496188580807118613)
              ·
                refine ⟨3453747257633839725333685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73679941496188580807118613 3453747257633839725333685)
                ·
                  refine ⟨323788805403172474250033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453747257633839725333685 323788805403172474250033)
                  ·
                    rfl

theorem cell22_2837594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_2837594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837594 prefixEnd_2837594 := by exact prefixLift 2837594
  have htrace : WordTrace (prefixWord ++ tailWord_2837594) baseStart_2837594 baseEnd_2837594 := by
    simpa [prefixWord, tailWord_2837594, baseEnd_2837594] using wordTrace_append hprefix tailTrace_2837594
  have hstable : (prefixWord ++ tailWord_2837594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837594).length < 2 ^ (prefixWord ++ tailWord_2837594).sum := by decide
  have hdescent : baseEnd_2837594 < baseStart_2837594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837609 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_2837609 : Nat := 118140960795 + 2837609 * 2 ^ 59
def prefixEnd_2837609 : Nat := 4983230072969 + 3 ^ 40 * 2837609 * 2
def baseEnd_2837609 : Nat := 971371551016062383625053

theorem tailTrace_2837609 : CollatzResearch.WordTrace tailWord_2837609 prefixEnd_2837609 971371551016062383625053 := by
  unfold tailWord_2837609
  simp only [CollatzResearch.WordTrace]
  refine ⟨103496102776834692879339881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68997401851223128586226587 103496102776834692879339881)
  ·
    refine ⟨77622077082626019659504911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103496102776834692879339881 77622077082626019659504911)
    ·
      refine ⟨116433115623939029489257367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77622077082626019659504911 116433115623939029489257367)
      ·
        refine ⟨174649673435908544233886051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116433115623939029489257367 174649673435908544233886051)
        ·
          refine ⟨261974510153862816350829077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174649673435908544233886051 261974510153862816350829077)
          ·
            refine ⟨12280055163462319516445113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 261974510153862816350829077 12280055163462319516445113)
            ·
              refine ⟨9210041372596739637333835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12280055163462319516445113 9210041372596739637333835)
              ·
                refine ⟨13815062058895109456000753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9210041372596739637333835 13815062058895109456000753)
                ·
                  refine ⟨10361296544171332092000565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13815062058895109456000753 10361296544171332092000565)
                  ·
                    refine ⟨971371551016062383625053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10361296544171332092000565 971371551016062383625053)
                    ·
                      rfl

theorem cell22_2837609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_2837609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837609 prefixEnd_2837609 := by exact prefixLift 2837609
  have htrace : WordTrace (prefixWord ++ tailWord_2837609) baseStart_2837609 baseEnd_2837609 := by
    simpa [prefixWord, tailWord_2837609, baseEnd_2837609] using wordTrace_append hprefix tailTrace_2837609
  have hstable : (prefixWord ++ tailWord_2837609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837609).length < 2 ^ (prefixWord ++ tailWord_2837609).sum := by decide
  have hdescent : baseEnd_2837609 < baseStart_2837609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837624 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_2837624 : Nat := 118140960795 + 2837624 * 2 ^ 59
def prefixEnd_2837624 : Nat := 4983230072969 + 3 ^ 40 * 2837624 * 2
def baseEnd_2837624 : Nat := 971376685822607344500007

theorem tailTrace_2837624 : CollatzResearch.WordTrace tailWord_2837624 prefixEnd_2837624 971376685822607344500007 := by
  unfold tailWord_2837624
  simp only [CollatzResearch.WordTrace]
  refine ⟨51748324935890175220567963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68997766581186900294090617 51748324935890175220567963)
  ·
    refine ⟨77622487403835262830851945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51748324935890175220567963 77622487403835262830851945)
    ·
      refine ⟨58216865552876447123138959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77622487403835262830851945 58216865552876447123138959)
      ·
        refine ⟨87325298329314670684708439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58216865552876447123138959 87325298329314670684708439)
        ·
          refine ⟨130987947493972006027062659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87325298329314670684708439 130987947493972006027062659)
          ·
            refine ⟨196481921240958009040593989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130987947493972006027062659 196481921240958009040593989)
            ·
              refine ⟨36840360232679626695111373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196481921240958009040593989 36840360232679626695111373)
              ·
                refine ⟨13815135087254860010666765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36840360232679626695111373 13815135087254860010666765)
                ·
                  refine ⟨5180675657720572504000037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13815135087254860010666765 5180675657720572504000037)
                  ·
                    refine ⟨971376685822607344500007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180675657720572504000037 971376685822607344500007)
                    ·
                      rfl

theorem cell22_2837624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_2837624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837624 prefixEnd_2837624 := by exact prefixLift 2837624
  have htrace : WordTrace (prefixWord ++ tailWord_2837624) baseStart_2837624 baseEnd_2837624 := by
    simpa [prefixWord, tailWord_2837624, baseEnd_2837624] using wordTrace_append hprefix tailTrace_2837624
  have hstable : (prefixWord ++ tailWord_2837624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837624).length < 2 ^ (prefixWord ++ tailWord_2837624).sum := by decide
  have hdescent : baseEnd_2837624 < baseStart_2837624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837641 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_2837641 : Nat := 118140960795 + 2837641 * 2 ^ 59
def prefixEnd_2837641 : Nat := 4983230072969 + 3 ^ 40 * 2837641 * 2
def baseEnd_2837641 : Nat := 971382505270024966824955

theorem tailTrace_2837641 : CollatzResearch.WordTrace tailWord_2837641 prefixEnd_2837641 971382505270024966824955 := by
  unfold tailWord_2837641
  simp only [CollatzResearch.WordTrace]
  refine ⟨103497269912718762344504777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68998179941812508229669851 103497269912718762344504777)
  ·
    refine ⟨77622952434539071758378583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103497269912718762344504777 77622952434539071758378583)
    ·
      refine ⟨116434428651808607637567875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77622952434539071758378583 116434428651808607637567875)
      ·
        refine ⟨174651642977712911456351813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116434428651808607637567875 174651642977712911456351813)
        ·
          refine ⟨32747183058321170898065965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174651642977712911456351813 32747183058321170898065965)
          ·
            refine ⟨12280193646870439086774737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32747183058321170898065965 12280193646870439086774737)
            ·
              refine ⟨9210145235152829315081053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12280193646870439086774737 9210145235152829315081053)
              ·
                refine ⟨3453804463182310993155395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9210145235152829315081053 3453804463182310993155395)
                ·
                  refine ⟨5180706694773466489733093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453804463182310993155395 5180706694773466489733093)
                  ·
                    refine ⟨971382505270024966824955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180706694773466489733093 971382505270024966824955)
                    ·
                      rfl

theorem cell22_2837641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_2837641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837641 prefixEnd_2837641 := by exact prefixLift 2837641
  have htrace : WordTrace (prefixWord ++ tailWord_2837641) baseStart_2837641 baseEnd_2837641 := by
    simpa [prefixWord, tailWord_2837641, baseEnd_2837641] using wordTrace_append hprefix tailTrace_2837641
  have hstable : (prefixWord ++ tailWord_2837641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837641).length < 2 ^ (prefixWord ++ tailWord_2837641).sum := by decide
  have hdescent : baseEnd_2837641 < baseStart_2837641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837656 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_2837656 : Nat := 118140960795 + 2837656 * 2 ^ 59
def prefixEnd_2837656 : Nat := 4983230072969 + 3 ^ 40 * 2837656 * 2
def baseEnd_2837656 : Nat := 323795880025523309233303

theorem tailTrace_2837656 : CollatzResearch.WordTrace tailWord_2837656 prefixEnd_2837656 323795880025523309233303 := by
  unfold tailWord_2837656
  simp only [CollatzResearch.WordTrace]
  refine ⟨51748908503832209953150411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68998544671776279937533881 51748908503832209953150411)
  ·
    refine ⟨77623362755748314929725617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51748908503832209953150411 77623362755748314929725617)
    ·
      refine ⟨58217522066811236197294213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77623362755748314929725617 58217522066811236197294213)
      ·
        refine ⟨10915785387527106786992665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58217522066811236197294213 10915785387527106786992665)
        ·
          refine ⟨8186839040645330090244499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10915785387527106786992665 8186839040645330090244499)
          ·
            refine ⟨12280258560967995135366749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186839040645330090244499 12280258560967995135366749)
            ·
              refine ⟨4605096960362998175762531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12280258560967995135366749 4605096960362998175762531)
              ·
                refine ⟨6907645440544497263643797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605096960362998175762531 6907645440544497263643797)
                ·
                  refine ⟨323795880025523309233303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6907645440544497263643797 323795880025523309233303)
                  ·
                    rfl

theorem cell22_2837656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_2837656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837656 prefixEnd_2837656 := by exact prefixLift 2837656
  have htrace : WordTrace (prefixWord ++ tailWord_2837656) baseStart_2837656 baseEnd_2837656 := by
    simpa [prefixWord, tailWord_2837656, baseEnd_2837656] using wordTrace_append hprefix tailTrace_2837656
  have hstable : (prefixWord ++ tailWord_2837656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837656).length < 2 ^ (prefixWord ++ tailWord_2837656).sum := by decide
  have hdescent : baseEnd_2837656 < baseStart_2837656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837761 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2837761 : Nat := 118140960795 + 2837761 * 2 ^ 59
def prefixEnd_2837761 : Nat := 4983230072969 + 3 ^ 40 * 2837761 * 2
def baseEnd_2837761 : Nat := 971423583722384653824587

theorem tailTrace_2837761 : CollatzResearch.WordTrace tailWord_2837761 prefixEnd_2837761 971423583722384653824587 := by
  unfold tailWord_2837761
  simp only [CollatzResearch.WordTrace]
  refine ⟨103501646672284022838873137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69001097781522681892582091 103501646672284022838873137)
  ·
    refine ⟨77626235004213017129154853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103501646672284022838873137 77626235004213017129154853)
    ·
      refine ⟨14554919063289940711716535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77626235004213017129154853 14554919063289940711716535)
      ·
        refine ⟨21832378594934911067574803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14554919063289940711716535 21832378594934911067574803)
        ·
          refine ⟨32748567892402366601362205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21832378594934911067574803 32748567892402366601362205)
          ·
            refine ⟨12280712959650887475510827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32748567892402366601362205 12280712959650887475510827)
            ·
              refine ⟨18421069439476331213266241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12280712959650887475510827 18421069439476331213266241)
              ·
                refine ⟨13815802079607248409949681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18421069439476331213266241 13815802079607248409949681)
                ·
                  refine ⟨10361851559705436307462261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13815802079607248409949681 10361851559705436307462261)
                  ·
                    refine ⟨971423583722384653824587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10361851559705436307462261 971423583722384653824587)
                    ·
                      rfl

theorem cell22_2837761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2837761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837761 prefixEnd_2837761 := by exact prefixLift 2837761
  have htrace : WordTrace (prefixWord ++ tailWord_2837761) baseStart_2837761 baseEnd_2837761 := by
    simpa [prefixWord, tailWord_2837761, baseEnd_2837761] using wordTrace_append hprefix tailTrace_2837761
  have hstable : (prefixWord ++ tailWord_2837761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837761).length < 2 ^ (prefixWord ++ tailWord_2837761).sum := by decide
  have hdescent : baseEnd_2837761 < baseStart_2837761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837763 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 5]
def baseStart_2837763 : Nat := 118140960795 + 2837763 * 2 ^ 59
def prefixEnd_2837763 : Nat := 4983230072969 + 3 ^ 40 * 2837763 * 2
def baseEnd_2837763 : Nat := 323808089454419105091527

theorem tailTrace_2837763 : CollatzResearch.WordTrace tailWord_2837763 prefixEnd_2837763 323808089454419105091527 := by
  unfold tailWord_2837763
  simp only [CollatzResearch.WordTrace]
  refine ⟨103501719618276777180445943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69001146412184518120297295 103501719618276777180445943)
  ·
    refine ⟨155252579427415165770668915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103501719618276777180445943 155252579427415165770668915)
    ·
      refine ⟨232878869141122748656003373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155252579427415165770668915 232878869141122748656003373)
      ·
        refine ⟨87329575927921030746001265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232878869141122748656003373 87329575927921030746001265)
        ·
          refine ⟨65497181945940773059500949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87329575927921030746001265 65497181945940773059500949)
          ·
            refine ⟨3070180403715973737164107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65497181945940773059500949 3070180403715973737164107)
            ·
              refine ⟨4605270605573960605746161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070180403715973737164107 4605270605573960605746161)
              ·
                refine ⟨3453952954180470454309621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4605270605573960605746161 3453952954180470454309621)
                ·
                  refine ⟨323808089454419105091527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453952954180470454309621 323808089454419105091527)
                  ·
                    rfl

theorem cell22_2837763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 5].length) (baseStart_2837763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837763 prefixEnd_2837763 := by exact prefixLift 2837763
  have htrace : WordTrace (prefixWord ++ tailWord_2837763) baseStart_2837763 baseEnd_2837763 := by
    simpa [prefixWord, tailWord_2837763, baseEnd_2837763] using wordTrace_append hprefix tailTrace_2837763
  have hstable : (prefixWord ++ tailWord_2837763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837763).length < 2 ^ (prefixWord ++ tailWord_2837763).sum := by decide
  have hdescent : baseEnd_2837763 < baseStart_2837763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837823 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 4, 3]
def baseStart_2837823 : Nat := 118140960795 + 2837823 * 2 ^ 59
def prefixEnd_2837823 : Nat := 4983230072969 + 3 ^ 40 * 2837823 * 2
def baseEnd_2837823 : Nat := 971444807589437158774397

theorem tailTrace_2837823 : CollatzResearch.WordTrace tailWord_2837823 prefixEnd_2837823 971444807589437158774397 := by
  unfold tailWord_2837823
  simp only [CollatzResearch.WordTrace]
  refine ⟨103503907998059407427630123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69002605332039604951753415 103503907998059407427630123)
  ·
    refine ⟨155255861997089111141445185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103503907998059407427630123 155255861997089111141445185)
    ·
      refine ⟨116441896497816833356083889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155255861997089111141445185 116441896497816833356083889)
      ·
        refine ⟨87331422373362625017062917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116441896497816833356083889 87331422373362625017062917)
        ·
          refine ⟨16374641695005492190699297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87331422373362625017062917 16374641695005492190699297)
          ·
            refine ⟨12280981271254119143024473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16374641695005492190699297 12280981271254119143024473)
            ·
              refine ⟨9210735953440589357268355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12280981271254119143024473 9210735953440589357268355)
              ·
                refine ⟨13816103930160884035902533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9210735953440589357268355 13816103930160884035902533)
                ·
                  refine ⟨2590519486905165756731725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13816103930160884035902533 2590519486905165756731725)
                  ·
                    refine ⟨971444807589437158774397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2590519486905165756731725 971444807589437158774397)
                    ·
                      rfl

theorem cell22_2837823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_2837823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837823 prefixEnd_2837823 := by exact prefixLift 2837823
  have htrace : WordTrace (prefixWord ++ tailWord_2837823) baseStart_2837823 baseEnd_2837823 := by
    simpa [prefixWord, tailWord_2837823, baseEnd_2837823] using wordTrace_append hprefix tailTrace_2837823
  have hstable : (prefixWord ++ tailWord_2837823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837823).length < 2 ^ (prefixWord ++ tailWord_2837823).sum := by decide
  have hdescent : baseEnd_2837823 < baseStart_2837823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837825 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 6]
def baseStart_2837825 : Nat := 118140960795 + 2837825 * 2 ^ 59
def prefixEnd_2837825 : Nat := 4983230072969 + 3 ^ 40 * 2837825 * 2
def baseEnd_2837825 : Nat := 323815164076769940074797

theorem tailTrace_2837825 : CollatzResearch.WordTrace tailWord_2837825 prefixEnd_2837825 323815164076769940074797 := by
  unfold tailWord_2837825
  simp only [CollatzResearch.WordTrace]
  refine ⟨103503980944052161769202929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69002653962701441179468619 103503980944052161769202929)
  ·
    refine ⟨77627985708039121326902197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103503980944052161769202929 77627985708039121326902197)
    ·
      refine ⟨7277623660128667624397081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77627985708039121326902197 7277623660128667624397081)
      ·
        refine ⟨5458217745096500718297811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7277623660128667624397081 5458217745096500718297811)
        ·
          refine ⟨8187326617644751077446717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458217745096500718297811 8187326617644751077446717)
          ·
            refine ⟨3070247481616781654042519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8187326617644751077446717 3070247481616781654042519)
            ·
              refine ⟨4605371222425172481063779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070247481616781654042519 4605371222425172481063779)
              ·
                refine ⟨6908056833637758721595669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605371222425172481063779 6908056833637758721595669)
                ·
                  refine ⟨323815164076769940074797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6908056833637758721595669 323815164076769940074797)
                  ·
                    rfl

theorem cell22_2837825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_2837825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837825 prefixEnd_2837825 := by exact prefixLift 2837825
  have htrace : WordTrace (prefixWord ++ tailWord_2837825) baseStart_2837825 baseEnd_2837825 := by
    simpa [prefixWord, tailWord_2837825, baseEnd_2837825] using wordTrace_append hprefix tailTrace_2837825
  have hstable : (prefixWord ++ tailWord_2837825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837825).length < 2 ^ (prefixWord ++ tailWord_2837825).sum := by decide
  have hdescent : baseEnd_2837825 < baseStart_2837825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837836 : List Nat := [2, 2, 1, 3, 2, 2, 1, 9]
def baseStart_2837836 : Nat := 118140960795 + 2837836 * 2 ^ 59
def prefixEnd_2837836 : Nat := 4983230072969 + 3 ^ 40 * 2837836 * 2
def baseEnd_2837836 : Nat := 107938806417234384244373

theorem tailTrace_2837836 : CollatzResearch.WordTrace tailWord_2837836 prefixEnd_2837836 107938806417234384244373 := by
  unfold tailWord_2837836
  simp only [CollatzResearch.WordTrace]
  refine ⟨51752191073506155323926681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69002921431341540431902241 51752191073506155323926681)
  ·
    refine ⟨38814143305129616492945011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51752191073506155323926681 38814143305129616492945011)
    ·
      refine ⟨58221214957694424739417517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38814143305129616492945011 58221214957694424739417517)
      ·
        refine ⟨21832955609135409277281569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58221214957694424739417517 21832955609135409277281569)
        ·
          refine ⟨16374716706851556957961177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21832955609135409277281569 16374716706851556957961177)
          ·
            refine ⟨12281037530138667718470883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16374716706851556957961177 12281037530138667718470883)
            ·
              refine ⟨18421556295208001577706325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281037530138667718470883 18421556295208001577706325)
              ·
                refine ⟨107938806417234384244373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18421556295208001577706325 107938806417234384244373)
                ·
                  rfl

theorem cell22_2837836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_2837836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837836 prefixEnd_2837836 := by exact prefixLift 2837836
  have htrace : WordTrace (prefixWord ++ tailWord_2837836) baseStart_2837836 baseEnd_2837836 := by
    simpa [prefixWord, tailWord_2837836, baseEnd_2837836] using wordTrace_append hprefix tailTrace_2837836
  have hstable : (prefixWord ++ tailWord_2837836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837836).length < 2 ^ (prefixWord ++ tailWord_2837836).sum := by decide
  have hdescent : baseEnd_2837836 < baseStart_2837836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837870 : List Nat := [4, 1, 2, 4, 2, 9]
def baseStart_2837870 : Nat := 118140960795 + 2837870 * 2 ^ 59
def prefixEnd_2837870 : Nat := 4983230072969 + 3 ^ 40 * 2837870 * 2
def baseEnd_2837870 : Nat := 11993344403085737072213

theorem tailTrace_2837870 : CollatzResearch.WordTrace tailWord_2837870 prefixEnd_2837870 11993344403085737072213 := by
  unfold tailWord_2837870
  simp only [CollatzResearch.WordTrace]
  refine ⟨12938202778611141806823883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69003748152592756303060709 12938202778611141806823883)
  ·
    refine ⟨19407304167916712710235825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12938202778611141806823883 19407304167916712710235825)
    ·
      refine ⟨14555478125937534532676869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19407304167916712710235825 14555478125937534532676869)
      ·
        refine ⟨2729152148613287724876913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14555478125937534532676869 2729152148613287724876913)
        ·
          refine ⟨2046864111459965793657685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729152148613287724876913 2046864111459965793657685)
          ·
            refine ⟨11993344403085737072213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2046864111459965793657685 11993344403085737072213)
            ·
              rfl

theorem cell22_2837870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 9].length) (baseStart_2837870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837870 prefixEnd_2837870 := by exact prefixLift 2837870
  have htrace : WordTrace (prefixWord ++ tailWord_2837870) baseStart_2837870 baseEnd_2837870 := by
    simpa [prefixWord, tailWord_2837870, baseEnd_2837870] using wordTrace_append hprefix tailTrace_2837870
  have hstable : (prefixWord ++ tailWord_2837870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837870).length < 2 ^ (prefixWord ++ tailWord_2837870).sum := by decide
  have hdescent : baseEnd_2837870 < baseStart_2837870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837881 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 7]
def baseStart_2837881 : Nat := 118140960795 + 2837881 * 2 ^ 59
def prefixEnd_2837881 : Nat := 4983230072969 + 3 ^ 40 * 2837881 * 2
def baseEnd_2837881 : Nat := 323821554058248113608073

theorem tailTrace_2837881 : CollatzResearch.WordTrace tailWord_2837881 prefixEnd_2837881 323821554058248113608073 := by
  unfold tailWord_2837881
  simp only [CollatzResearch.WordTrace]
  refine ⟨103506023431849283333241497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69004015621232855555494331 103506023431849283333241497)
  ·
    refine ⟨77629517573886962499931123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103506023431849283333241497 77629517573886962499931123)
    ·
      refine ⟨116444276360830443749896685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77629517573886962499931123 116444276360830443749896685)
      ·
        refine ⟨43666603635311416406211257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116444276360830443749896685 43666603635311416406211257)
        ·
          refine ⟨32749952726483562304658443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43666603635311416406211257 32749952726483562304658443)
          ·
            refine ⟨49124929089725343456987665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32749952726483562304658443 49124929089725343456987665)
            ·
              refine ⟨36843696817294007592740749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49124929089725343456987665 36843696817294007592740749)
              ·
                refine ⟨13816386306485252847277781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36843696817294007592740749 13816386306485252847277781)
                ·
                  refine ⟨323821554058248113608073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13816386306485252847277781 323821554058248113608073)
                  ·
                    rfl

theorem cell22_2837881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_2837881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837881 prefixEnd_2837881 := by exact prefixLift 2837881
  have htrace : WordTrace (prefixWord ++ tailWord_2837881) baseStart_2837881 baseEnd_2837881 := by
    simpa [prefixWord, tailWord_2837881, baseEnd_2837881] using wordTrace_append hprefix tailTrace_2837881
  have hstable : (prefixWord ++ tailWord_2837881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837881).length < 2 ^ (prefixWord ++ tailWord_2837881).sum := by decide
  have hdescent : baseEnd_2837881 < baseStart_2837881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837902 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_2837902 : Nat := 118140960795 + 2837902 * 2 ^ 59
def prefixEnd_2837902 : Nat := 4983230072969 + 3 ^ 40 * 2837902 * 2
def baseEnd_2837902 : Nat := 971471850903907286049155

theorem tailTrace_2837902 : CollatzResearch.WordTrace tailWord_2837902 prefixEnd_2837902 971471850903907286049155 := by
  unfold tailWord_2837902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12938348670596650489969495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69004526243182135946503973 12938348670596650489969495)
  ·
    refine ⟨19407523005894975734954243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12938348670596650489969495 19407523005894975734954243)
    ·
      refine ⟨29111284508842463602431365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19407523005894975734954243 29111284508842463602431365)
      ·
        refine ⟨5458365845407961925455881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29111284508842463602431365 5458365845407961925455881)
        ·
          refine ⟨4093774384055971444091911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5458365845407961925455881 4093774384055971444091911)
          ·
            refine ⟨6140661576083957166137867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093774384055971444091911 6140661576083957166137867)
            ·
              refine ⟨9210992364125935749206801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140661576083957166137867 9210992364125935749206801)
              ·
                refine ⟨6908244273094451811905101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9210992364125935749206801 6908244273094451811905101)
                ·
                  refine ⟨2590591602410419429464413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6908244273094451811905101 2590591602410419429464413)
                  ·
                    refine ⟨971471850903907286049155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2590591602410419429464413 971471850903907286049155)
                    ·
                      rfl

theorem cell22_2837902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_2837902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837902 prefixEnd_2837902 := by exact prefixLift 2837902
  have htrace : WordTrace (prefixWord ++ tailWord_2837902) baseStart_2837902 baseEnd_2837902 := by
    simpa [prefixWord, tailWord_2837902, baseEnd_2837902] using wordTrace_append hprefix tailTrace_2837902
  have hstable : (prefixWord ++ tailWord_2837902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837902).length < 2 ^ (prefixWord ++ tailWord_2837902).sum := by decide
  have hdescent : baseEnd_2837902 < baseStart_2837902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837943 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 6]
def baseStart_2837943 : Nat := 118140960795 + 2837943 * 2 ^ 59
def prefixEnd_2837943 : Nat := 4983230072969 + 3 ^ 40 * 2837943 * 2
def baseEnd_2837943 : Nat := 323828628680598948591343

theorem tailTrace_2837943 : CollatzResearch.WordTrace tailWord_2837943 prefixEnd_2837943 323828628680598948591343 := by
  unfold tailWord_2837943
  simp only [CollatzResearch.WordTrace]
  refine ⟨103508284757624667921998483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69005523171749778614665655 103508284757624667921998483)
  ·
    refine ⟨155262427136437001882997725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103508284757624667921998483 155262427136437001882997725)
    ·
      refine ⟨58223410176163875706124147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155262427136437001882997725 58223410176163875706124147)
      ·
        refine ⟨87335115264245813559186221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58223410176163875706124147 87335115264245813559186221)
        ·
          refine ⟨32750668224092180084694833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87335115264245813559186221 32750668224092180084694833)
          ·
            refine ⟨24563001168069135063521125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32750668224092180084694833 24563001168069135063521125)
            ·
              refine ⟨4605562719012962824410211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24563001168069135063521125 4605562719012962824410211)
              ·
                refine ⟨6908344078519444236615317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605562719012962824410211 6908344078519444236615317)
                ·
                  refine ⟨323828628680598948591343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6908344078519444236615317 323828628680598948591343)
                  ·
                    rfl

theorem cell22_2837943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 6].length) (baseStart_2837943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837943 prefixEnd_2837943 := by exact prefixLift 2837943
  have htrace : WordTrace (prefixWord ++ tailWord_2837943) baseStart_2837943 baseEnd_2837943 := by
    simpa [prefixWord, tailWord_2837943, baseEnd_2837943] using wordTrace_append hprefix tailTrace_2837943
  have hstable : (prefixWord ++ tailWord_2837943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837943).length < 2 ^ (prefixWord ++ tailWord_2837943).sum := by decide
  have hdescent : baseEnd_2837943 < baseStart_2837943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837973 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2837973 : Nat := 118140960795 + 2837973 * 2 ^ 59
def prefixEnd_2837973 : Nat := 4983230072969 + 3 ^ 40 * 2837973 * 2
def baseEnd_2837973 : Nat := 971496155654886767523937

theorem tailTrace_2837973 : CollatzResearch.WordTrace tailWord_2837973 prefixEnd_2837973 971496155654886767523937 := by
  unfold tailWord_2837973
  simp only [CollatzResearch.WordTrace]
  refine ⟨103509378947515983045590573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69006252631677322030393715 103509378947515983045590573)
  ·
    refine ⟨38816017105318493642096465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103509378947515983045590573 38816017105318493642096465)
    ·
      refine ⟨29112012828988870231572349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38816017105318493642096465 29112012828988870231572349)
      ·
        refine ⟨10917004810870826336839631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29112012828988870231572349 10917004810870826336839631)
        ·
          refine ⟨16375507216306239505259447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10917004810870826336839631 16375507216306239505259447)
          ·
            refine ⟨24563260824459359257889171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16375507216306239505259447 24563260824459359257889171)
            ·
              refine ⟨36844891236689038886833757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24563260824459359257889171 36844891236689038886833757)
              ·
                refine ⟨13816834213758389582562659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36844891236689038886833757 13816834213758389582562659)
                ·
                  refine ⟨20725251320637584373843989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13816834213758389582562659 20725251320637584373843989)
                  ·
                    refine ⟨971496155654886767523937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20725251320637584373843989 971496155654886767523937)
                    ·
                      rfl

theorem cell22_2837973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2837973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837973 prefixEnd_2837973 := by exact prefixLift 2837973
  have htrace : WordTrace (prefixWord ++ tailWord_2837973) baseStart_2837973 baseEnd_2837973 := by
    simpa [prefixWord, tailWord_2837973, baseEnd_2837973] using wordTrace_append hprefix tailTrace_2837973
  have hstable : (prefixWord ++ tailWord_2837973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837973).length < 2 ^ (prefixWord ++ tailWord_2837973).sum := by decide
  have hdescent : baseEnd_2837973 < baseStart_2837973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837977 : List Nat := [1, 2, 1, 2, 4, 4, 1, 3, 4]
def baseStart_2837977 : Nat := 118140960795 + 2837977 * 2 ^ 59
def prefixEnd_2837977 : Nat := 4983230072969 + 3 ^ 40 * 2837977 * 2
def baseEnd_2837977 : Nat := 323832508312210696807975

theorem tailTrace_2837977 : CollatzResearch.WordTrace tailWord_2837977 prefixEnd_2837977 323832508312210696807975 := by
  unfold tailWord_2837977
  simp only [CollatzResearch.WordTrace]
  refine ⟨103509524839501491728736185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69006349893000994485824123 103509524839501491728736185)
  ·
    refine ⟨77632143629626118796552139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103509524839501491728736185 77632143629626118796552139)
    ·
      refine ⟨116448215444439178194828209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77632143629626118796552139 116448215444439178194828209)
      ·
        refine ⟨87336161583329383646121157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116448215444439178194828209 87336161583329383646121157)
        ·
          refine ⟨16375530296874259433647717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87336161583329383646121157 16375530296874259433647717)
          ·
            refine ⟨3070411930663923643808947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16375530296874259433647717 3070411930663923643808947)
            ·
              refine ⟨4605617895995885465713421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070411930663923643808947 4605617895995885465713421)
              ·
                refine ⟨1727106710998457049642533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4605617895995885465713421 1727106710998457049642533)
                ·
                  refine ⟨323832508312210696807975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727106710998457049642533 323832508312210696807975)
                  ·
                    rfl

theorem cell22_2837977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_2837977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837977 prefixEnd_2837977 := by exact prefixLift 2837977
  have htrace : WordTrace (prefixWord ++ tailWord_2837977) baseStart_2837977 baseEnd_2837977 := by
    simpa [prefixWord, tailWord_2837977, baseEnd_2837977] using wordTrace_append hprefix tailTrace_2837977
  have hstable : (prefixWord ++ tailWord_2837977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837977).length < 2 ^ (prefixWord ++ tailWord_2837977).sum := by decide
  have hdescent : baseEnd_2837977 < baseStart_2837977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2837994 : List Nat := [3, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_2837994 : Nat := 118140960795 + 2837994 * 2 ^ 59
def prefixEnd_2837994 : Nat := 4983230072969 + 3 ^ 40 * 2837994 * 2
def baseEnd_2837994 : Nat := 323834448128016570916291

theorem tailTrace_2837994 : CollatzResearch.WordTrace tailWord_2837994 prefixEnd_2837994 323834448128016570916291 := by
  unfold tailWord_2837994
  simp only [CollatzResearch.WordTrace]
  refine ⟨25877536220109975908026259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69006763253626602421403357 25877536220109975908026259)
  ·
    refine ⟨38816304330164963862039389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25877536220109975908026259 38816304330164963862039389)
    ·
      refine ⟨14556114123811861448264771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38816304330164963862039389 14556114123811861448264771)
      ·
        refine ⟨21834171185717792172397157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14556114123811861448264771 21834171185717792172397157)
        ·
          refine ⟨4093907097322086032324467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21834171185717792172397157 4093907097322086032324467)
          ·
            refine ⟨6140860645983129048486701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4093907097322086032324467 6140860645983129048486701)
            ·
              refine ⟨2302822742243673393182513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6140860645983129048486701 2302822742243673393182513)
              ·
                refine ⟨1727117056682755044886885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2302822742243673393182513 1727117056682755044886885)
                ·
                  refine ⟨323834448128016570916291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727117056682755044886885 323834448128016570916291)
                  ·
                    rfl

theorem cell22_2837994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_2837994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2837994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2837994 prefixEnd_2837994 := by exact prefixLift 2837994
  have htrace : WordTrace (prefixWord ++ tailWord_2837994) baseStart_2837994 baseEnd_2837994 := by
    simpa [prefixWord, tailWord_2837994, baseEnd_2837994] using wordTrace_append hprefix tailTrace_2837994
  have hstable : (prefixWord ++ tailWord_2837994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2837994).length < 2 ^ (prefixWord ++ tailWord_2837994).sum := by decide
  have hdescent : baseEnd_2837994 < baseStart_2837994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2837994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838005 : List Nat := [1, 3, 5, 1, 1, 1, 1, 9]
def baseStart_2838005 : Nat := 118140960795 + 2838005 * 2 ^ 59
def prefixEnd_2838005 : Nat := 4983230072969 + 3 ^ 40 * 2838005 * 2
def baseEnd_2838005 : Nat := 107945234434316594524871

theorem tailTrace_2838005 : CollatzResearch.WordTrace tailWord_2838005 prefixEnd_2838005 107945234434316594524871 := by
  unfold tailWord_2838005
  simp only [CollatzResearch.WordTrace]
  refine ⟨103510546083400052510755469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69007030722266701673836979 103510546083400052510755469)
  ·
    refine ⟨38816454781275019691533301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103510546083400052510755469 38816454781275019691533301)
    ·
      refine ⟨3639042635744533096081247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38816454781275019691533301 3639042635744533096081247)
      ·
        refine ⟨5458563953616799644121871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639042635744533096081247 5458563953616799644121871)
        ·
          refine ⟨8187845930425199466182807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458563953616799644121871 8187845930425199466182807)
          ·
            refine ⟨12281768895637799199274211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187845930425199466182807 12281768895637799199274211)
            ·
              refine ⟨18422653343456698798911317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281768895637799199274211 18422653343456698798911317)
              ·
                refine ⟨107945234434316594524871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18422653343456698798911317 107945234434316594524871)
                ·
                  rfl

theorem cell22_2838005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 9].length) (baseStart_2838005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838005 prefixEnd_2838005 := by exact prefixLift 2838005
  have htrace : WordTrace (prefixWord ++ tailWord_2838005) baseStart_2838005 baseEnd_2838005 := by
    simpa [prefixWord, tailWord_2838005, baseEnd_2838005] using wordTrace_append hprefix tailTrace_2838005
  have hstable : (prefixWord ++ tailWord_2838005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838005).length < 2 ^ (prefixWord ++ tailWord_2838005).sum := by decide
  have hdescent : baseEnd_2838005 < baseStart_2838005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838050 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2838050 : Nat := 118140960795 + 2838050 * 2 ^ 59
def prefixEnd_2838050 : Nat := 4983230072969 + 3 ^ 40 * 2838050 * 2
def baseEnd_2838050 : Nat := 323840838109494744449567

theorem tailTrace_2838050 : CollatzResearch.WordTrace tailWord_2838050 prefixEnd_2838050 323840838109494744449567 := by
  unfold tailWord_2838050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25878046842059256299035901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69008124912158016797429069 25878046842059256299035901)
  ·
    refine ⟨9704267565772221112138463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25878046842059256299035901 9704267565772221112138463)
    ·
      refine ⟨14556401348658331668207695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9704267565772221112138463 14556401348658331668207695)
      ·
        refine ⟨21834602022987497502311543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14556401348658331668207695 21834602022987497502311543)
        ·
          refine ⟨32751903034481246253467315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21834602022987497502311543 32751903034481246253467315)
          ·
            refine ⟨49127854551721869380200973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32751903034481246253467315 49127854551721869380200973)
            ·
              refine ⟨18422945456895701017575365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49127854551721869380200973 18422945456895701017575365)
              ·
                refine ⟨3454302273167943940795381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18422945456895701017575365 3454302273167943940795381)
                ·
                  refine ⟨323840838109494744449567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3454302273167943940795381 323840838109494744449567)
                  ·
                    rfl

theorem cell22_2838050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2838050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838050 prefixEnd_2838050 := by exact prefixLift 2838050
  have htrace : WordTrace (prefixWord ++ tailWord_2838050) baseStart_2838050 baseEnd_2838050 := by
    simpa [prefixWord, tailWord_2838050, baseEnd_2838050] using wordTrace_append hprefix tailTrace_2838050
  have hstable : (prefixWord ++ tailWord_2838050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838050).length < 2 ^ (prefixWord ++ tailWord_2838050).sum := by decide
  have hdescent : baseEnd_2838050 < baseStart_2838050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838080 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_2838080 : Nat := 118140960795 + 2838080 * 2 ^ 59
def prefixEnd_2838080 : Nat := 4983230072969 + 3 ^ 40 * 2838080 * 2
def baseEnd_2838080 : Nat := 971532783941574155098609

theorem tailTrace_2838080 : CollatzResearch.WordTrace tailWord_2838080 prefixEnd_2838080 971532783941574155098609 := by
  unfold tailWord_2838080
  simp only [CollatzResearch.WordTrace]
  refine ⟨51756640779064170159867847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69008854372085560213157129 51756640779064170159867847)
  ·
    refine ⟨77634961168596255239801771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51756640779064170159867847 77634961168596255239801771)
    ·
      refine ⟨116452441752894382859702657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77634961168596255239801771 116452441752894382859702657)
      ·
        refine ⟨87339331314670787144776993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116452441752894382859702657 87339331314670787144776993)
        ·
          refine ⟨65504498486003090358582745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87339331314670787144776993 65504498486003090358582745)
          ·
            refine ⟨49128373864502317768937059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65504498486003090358582745 49128373864502317768937059)
            ·
              refine ⟨73692560796753476653405589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49128373864502317768937059 73692560796753476653405589)
              ·
                refine ⟨3454338787347819218128387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73692560796753476653405589 3454338787347819218128387)
                ·
                  refine ⟨5181508181021728827192581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454338787347819218128387 5181508181021728827192581)
                  ·
                    refine ⟨971532783941574155098609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5181508181021728827192581 971532783941574155098609)
                    ·
                      rfl

theorem cell22_2838080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_2838080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838080 prefixEnd_2838080 := by exact prefixLift 2838080
  have htrace : WordTrace (prefixWord ++ tailWord_2838080) baseStart_2838080 baseEnd_2838080 := by
    simpa [prefixWord, tailWord_2838080, baseEnd_2838080] using wordTrace_append hprefix tailTrace_2838080
  have hstable : (prefixWord ++ tailWord_2838080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838080).length < 2 ^ (prefixWord ++ tailWord_2838080).sum := by decide
  have hdescent : baseEnd_2838080 < baseStart_2838080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838309 : List Nat := [1, 3, 1, 2, 3, 4, 2, 6]
def baseStart_2838309 : Nat := 118140960795 + 2838309 * 2 ^ 59
def prefixEnd_2838309 : Nat := 4983230072969 + 3 ^ 40 * 2838309 * 2
def baseEnd_2838309 : Nat := 107956797257943765680323

theorem tailTrace_2838309 : CollatzResearch.WordTrace tailWord_2838309 prefixEnd_2838309 107956797257943765680323 := by
  unfold tailWord_2838309
  simp only [CollatzResearch.WordTrace]
  refine ⟨103521633874298712429821981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69014422582865808286547987 103521633874298712429821981)
  ·
    refine ⟨38820612702862017161183243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103521633874298712429821981 38820612702862017161183243)
    ·
      refine ⟨58230919054293025741774865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38820612702862017161183243 58230919054293025741774865)
      ·
        refine ⟨43673189290719769306331149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58230919054293025741774865 43673189290719769306331149)
        ·
          refine ⟨16377445984019913489874181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43673189290719769306331149 16377445984019913489874181)
          ·
            refine ⟨3070771122003733779351409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16377445984019913489874181 3070771122003733779351409)
            ·
              refine ⟨2303078341502800334513557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3070771122003733779351409 2303078341502800334513557)
              ·
                refine ⟨107956797257943765680323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2303078341502800334513557 107956797257943765680323)
                ·
                  rfl

theorem cell22_2838309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 6].length) (baseStart_2838309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838309 prefixEnd_2838309 := by exact prefixLift 2838309
  have htrace : WordTrace (prefixWord ++ tailWord_2838309) baseStart_2838309 baseEnd_2838309 := by
    simpa [prefixWord, tailWord_2838309, baseEnd_2838309] using wordTrace_append hprefix tailTrace_2838309
  have hstable : (prefixWord ++ tailWord_2838309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838309).length < 2 ^ (prefixWord ++ tailWord_2838309).sum := by decide
  have hdescent : baseEnd_2838309 < baseStart_2838309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838354 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_2838354 : Nat := 118140960795 + 2838354 * 2 ^ 59
def prefixEnd_2838354 : Nat := 4983230072969 + 3 ^ 40 * 2838354 * 2
def baseEnd_2838354 : Nat := 323875526580376257915923

theorem tailTrace_2838354 : CollatzResearch.WordTrace tailWord_2838354 prefixEnd_2838354 323875526580376257915923 := by
  unfold tailWord_2838354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25880818789783921278802529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69015516772757123410140077 25880818789783921278802529)
  ·
    refine ⟨19410614092337940959101897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25880818789783921278802529 19410614092337940959101897)
    ·
      refine ⟨14557960569253455719326423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19410614092337940959101897 14557960569253455719326423)
      ·
        refine ⟨21836940853880183578989635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14557960569253455719326423 21836940853880183578989635)
        ·
          refine ⟨32755411280820275368484453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21836940853880183578989635 32755411280820275368484453)
          ·
            refine ⟨6141639615153801631590835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32755411280820275368484453 6141639615153801631590835)
            ·
              refine ⟨9212459422730702447386253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141639615153801631590835 9212459422730702447386253)
              ·
                refine ⟨3454672283524013417769845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9212459422730702447386253 3454672283524013417769845)
                ·
                  refine ⟨323875526580376257915923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3454672283524013417769845 323875526580376257915923)
                  ·
                    rfl

theorem cell22_2838354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_2838354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838354 prefixEnd_2838354 := by exact prefixLift 2838354
  have htrace : WordTrace (prefixWord ++ tailWord_2838354) baseStart_2838354 baseEnd_2838354 := by
    simpa [prefixWord, tailWord_2838354, baseEnd_2838354] using wordTrace_append hprefix tailTrace_2838354
  have hstable : (prefixWord ++ tailWord_2838354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838354).length < 2 ^ (prefixWord ++ tailWord_2838354).sum := by decide
  have hdescent : baseEnd_2838354 < baseStart_2838354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838397 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_2838397 : Nat := 118140960795 + 2838397 * 2 ^ 59
def prefixEnd_2838397 : Nat := 4983230072969 + 3 ^ 40 * 2838397 * 2
def baseEnd_2838397 : Nat := 971641299519890994922637

theorem tailTrace_2838397 : CollatzResearch.WordTrace tailWord_2838397 prefixEnd_2838397 971641299519890994922637 := by
  unfold tailWord_2838397
  simp only [CollatzResearch.WordTrace]
  refine ⟨103524843497979903459025445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69016562331986602306016963 103524843497979903459025445)
  ·
    refine ⟨19410908155871231898567271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103524843497979903459025445 19410908155871231898567271)
    ·
      refine ⟨29116362233806847847850907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19410908155871231898567271 29116362233806847847850907)
      ·
        refine ⟨43674543350710271771776361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29116362233806847847850907 43674543350710271771776361)
        ·
          refine ⟨32755907513032703828832271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43674543350710271771776361 32755907513032703828832271)
          ·
            refine ⟨49133861269549055743248407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32755907513032703828832271 49133861269549055743248407)
            ·
              refine ⟨73700791904323583614872611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49133861269549055743248407 73700791904323583614872611)
              ·
                refine ⟨110551187856485375422308917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73700791904323583614872611 110551187856485375422308917)
                ·
                  refine ⟨10364173861545503945841461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110551187856485375422308917 10364173861545503945841461)
                  ·
                    refine ⟨971641299519890994922637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10364173861545503945841461 971641299519890994922637)
                    ·
                      rfl

theorem cell22_2838397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_2838397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838397 prefixEnd_2838397 := by exact prefixLift 2838397
  have htrace : WordTrace (prefixWord ++ tailWord_2838397) baseStart_2838397 baseEnd_2838397 := by
    simpa [prefixWord, tailWord_2838397, baseEnd_2838397] using wordTrace_append hprefix tailTrace_2838397
  have hstable : (prefixWord ++ tailWord_2838397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838397).length < 2 ^ (prefixWord ++ tailWord_2838397).sum := by decide
  have hdescent : baseEnd_2838397 < baseStart_2838397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838412 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_2838412 : Nat := 118140960795 + 2838412 * 2 ^ 59
def prefixEnd_2838412 : Nat := 4983230072969 + 3 ^ 40 * 2838412 * 2
def baseEnd_2838412 : Nat := 971646434326435955797591

theorem tailTrace_2838412 : CollatzResearch.WordTrace tailWord_2838412 prefixEnd_2838412 971646434326435955797591 := by
  unfold tailWord_2838412
  simp only [CollatzResearch.WordTrace]
  refine ⟨51762695296462780510410745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69016927061950374013880993 51762695296462780510410745)
  ·
    refine ⟨38822021472347085382808059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51762695296462780510410745 38822021472347085382808059)
    ·
      refine ⟨58233032208520628074212089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38822021472347085382808059 58233032208520628074212089)
      ·
        refine ⟨43674774156390471055659067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58233032208520628074212089 43674774156390471055659067)
        ·
          refine ⟨65512161234585706583488601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43674774156390471055659067 65512161234585706583488601)
          ·
            refine ⟨49134120925939279937616451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65512161234585706583488601 49134120925939279937616451)
            ·
              refine ⟨73701181388908919906424677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49134120925939279937616451 73701181388908919906424677)
              ·
                refine ⟨13818971510420422482454627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73701181388908919906424677 13818971510420422482454627)
                ·
                  refine ⟨20728457265630633723681941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13818971510420422482454627 20728457265630633723681941)
                  ·
                    refine ⟨971646434326435955797591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20728457265630633723681941 971646434326435955797591)
                    ·
                      rfl

theorem cell22_2838412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_2838412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838412 prefixEnd_2838412 := by exact prefixLift 2838412
  have htrace : WordTrace (prefixWord ++ tailWord_2838412) baseStart_2838412 baseEnd_2838412 := by
    simpa [prefixWord, tailWord_2838412, baseEnd_2838412] using wordTrace_append hprefix tailTrace_2838412
  have hstable : (prefixWord ++ tailWord_2838412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838412).length < 2 ^ (prefixWord ++ tailWord_2838412).sum := by decide
  have hdescent : baseEnd_2838412 < baseStart_2838412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838429 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2838429 : Nat := 118140960795 + 2838429 * 2 ^ 59
def prefixEnd_2838429 : Nat := 4983230072969 + 3 ^ 40 * 2838429 * 2
def baseEnd_2838429 : Nat := 971652253773853578122539

theorem tailTrace_2838429 : CollatzResearch.WordTrace tailWord_2838429 prefixEnd_2838429 971652253773853578122539 := by
  unfold tailWord_2838429
  simp only [CollatzResearch.WordTrace]
  refine ⟨103526010633863972924190341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69017340422575981949460227 103526010633863972924190341)
  ·
    refine ⟨19411126993849494923285689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103526010633863972924190341 19411126993849494923285689)
    ·
      refine ⟨14558345245387121192464267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19411126993849494923285689 14558345245387121192464267)
      ·
        refine ⟨21837517868080681788696401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14558345245387121192464267 21837517868080681788696401)
        ·
          refine ⟨16378138401060511341522301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21837517868080681788696401 16378138401060511341522301)
          ·
            refine ⟨6141801900397691753070863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16378138401060511341522301 6141801900397691753070863)
            ·
              refine ⟨9212702850596537629606295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141801900397691753070863 9212702850596537629606295)
              ·
                refine ⟨13819054275894806444409443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9212702850596537629606295 13819054275894806444409443)
                ·
                  refine ⟨20728581413842209666614165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13819054275894806444409443 20728581413842209666614165)
                  ·
                    refine ⟨971652253773853578122539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20728581413842209666614165 971652253773853578122539)
                    ·
                      rfl

theorem cell22_2838429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2838429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838429 prefixEnd_2838429 := by exact prefixLift 2838429
  have htrace : WordTrace (prefixWord ++ tailWord_2838429) baseStart_2838429 baseEnd_2838429 := by
    simpa [prefixWord, tailWord_2838429, baseEnd_2838429] using wordTrace_append hprefix tailTrace_2838429
  have hstable : (prefixWord ++ tailWord_2838429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838429).length < 2 ^ (prefixWord ++ tailWord_2838429).sum := by decide
  have hdescent : baseEnd_2838429 < baseStart_2838429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838433 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 4]
def baseStart_2838433 : Nat := 118140960795 + 2838433 * 2 ^ 59
def prefixEnd_2838433 : Nat := 4983230072969 + 3 ^ 40 * 2838433 * 2
def baseEnd_2838433 : Nat := 323884541018532967007509

theorem tailTrace_2838433 : CollatzResearch.WordTrace tailWord_2838433 prefixEnd_2838433 323884541018532967007509 := by
  unfold tailWord_2838433
  simp only [CollatzResearch.WordTrace]
  refine ⟨103526156525849481607335953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69017437683899654404890635 103526156525849481607335953)
  ·
    refine ⟨77644617394387111205501965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103526156525849481607335953 77644617394387111205501965)
    ·
      refine ⟨29116731522895166702063237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77644617394387111205501965 29116731522895166702063237)
      ·
        refine ⟨5459387160542843756636857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29116731522895166702063237 5459387160542843756636857)
        ·
          refine ⟨4094540370407132817477643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5459387160542843756636857 4094540370407132817477643)
          ·
            refine ⟨6141810555610699226216465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094540370407132817477643 6141810555610699226216465)
            ·
              refine ⟨4606357916708024419662349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6141810555610699226216465 4606357916708024419662349)
              ·
                refine ⟨1727384218765509157373381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4606357916708024419662349 1727384218765509157373381)
                ·
                  refine ⟨323884541018532967007509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727384218765509157373381 323884541018532967007509)
                  ·
                    rfl

theorem cell22_2838433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_2838433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838433 prefixEnd_2838433 := by exact prefixLift 2838433
  have htrace : WordTrace (prefixWord ++ tailWord_2838433) baseStart_2838433 baseEnd_2838433 := by
    simpa [prefixWord, tailWord_2838433, baseEnd_2838433] using wordTrace_append hprefix tailTrace_2838433
  have hstable : (prefixWord ++ tailWord_2838433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838433).length < 2 ^ (prefixWord ++ tailWord_2838433).sum := by decide
  have hdescent : baseEnd_2838433 < baseStart_2838433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838459 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 3, 3]
def baseStart_2838459 : Nat := 118140960795 + 2838459 * 2 ^ 59
def prefixEnd_2838459 : Nat := 4983230072969 + 3 ^ 40 * 2838459 * 2
def baseEnd_2838459 : Nat := 971662523386943499872447

theorem tailTrace_2838459 : CollatzResearch.WordTrace tailWord_2838459 prefixEnd_2838459 971662523386943499872447 := by
  unfold tailWord_2838459
  simp only [CollatzResearch.WordTrace]
  refine ⟨103527104823755288047782431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69018069882503525365188287 103527104823755288047782431)
  ·
    refine ⟨155290657235632932071673647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103527104823755288047782431 155290657235632932071673647)
    ·
      refine ⟨232935985853449398107510471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155290657235632932071673647 232935985853449398107510471)
      ·
        refine ⟨349403978780174097161265707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232935985853449398107510471 349403978780174097161265707)
        ·
          refine ⟨524105968170261145741898561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349403978780174097161265707 524105968170261145741898561)
          ·
            refine ⟨393079476127695859306423921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524105968170261145741898561 393079476127695859306423921)
            ·
              refine ⟨294809607095771894479817941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393079476127695859306423921 294809607095771894479817941)
              ·
                refine ⟨6909600166307153776870733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 294809607095771894479817941 6909600166307153776870733)
                ·
                  refine ⟨2591100062365182666326525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6909600166307153776870733 2591100062365182666326525)
                  ·
                    refine ⟨971662523386943499872447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2591100062365182666326525 971662523386943499872447)
                    ·
                      rfl

theorem cell22_2838459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3, 3].length) (baseStart_2838459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838459 prefixEnd_2838459 := by exact prefixLift 2838459
  have htrace : WordTrace (prefixWord ++ tailWord_2838459) baseStart_2838459 baseEnd_2838459 := by
    simpa [prefixWord, tailWord_2838459, baseEnd_2838459] using wordTrace_append hprefix tailTrace_2838459
  have hstable : (prefixWord ++ tailWord_2838459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838459).length < 2 ^ (prefixWord ++ tailWord_2838459).sum := by decide
  have hdescent : baseEnd_2838459 < baseStart_2838459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838476 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_2838476 : Nat := 118140960795 + 2838476 * 2 ^ 59
def prefixEnd_2838476 : Nat := 4983230072969 + 3 ^ 40 * 2838476 * 2
def baseEnd_2838476 : Nat := 971668342834361122197395

theorem tailTrace_2838476 : CollatzResearch.WordTrace tailWord_2838476 prefixEnd_2838476 971668342834361122197395 := by
  unfold tailWord_2838476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51763862432346849975575641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69018483243129133300767521 51763862432346849975575641)
  ·
    refine ⟨38822896824260137481681731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51763862432346849975575641 38822896824260137481681731)
    ·
      refine ⟨58234345236390206222522597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38822896824260137481681731 58234345236390206222522597)
      ·
        refine ⟨10918939731823163666722987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58234345236390206222522597 10918939731823163666722987)
        ·
          refine ⟨16378409597734745500084481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10918939731823163666722987 16378409597734745500084481)
          ·
            refine ⟨12283807198301059125063361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16378409597734745500084481 12283807198301059125063361)
            ·
              refine ⟨9212855398725794343797521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12283807198301059125063361 9212855398725794343797521)
              ·
                refine ⟨6909641549044345757848141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9212855398725794343797521 6909641549044345757848141)
                ·
                  refine ⟨2591115580891629659193053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6909641549044345757848141 2591115580891629659193053)
                  ·
                    refine ⟨971668342834361122197395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2591115580891629659193053 971668342834361122197395)
                    ·
                      rfl

theorem cell22_2838476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_2838476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838476 prefixEnd_2838476 := by exact prefixLift 2838476
  have htrace : WordTrace (prefixWord ++ tailWord_2838476) baseStart_2838476 baseEnd_2838476 := by
    simpa [prefixWord, tailWord_2838476, baseEnd_2838476] using wordTrace_append hprefix tailTrace_2838476
  have hstable : (prefixWord ++ tailWord_2838476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838476).length < 2 ^ (prefixWord ++ tailWord_2838476).sum := by decide
  have hdescent : baseEnd_2838476 < baseStart_2838476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838579 : List Nat := [1, 1, 1, 2, 4, 1, 5, 7]
def baseStart_2838579 : Nat := 118140960795 + 2838579 * 2 ^ 59
def prefixEnd_2838579 : Nat := 4983230072969 + 3 ^ 40 * 2838579 * 2
def baseEnd_2838579 : Nat := 107967066871033687430231

theorem tailTrace_2838579 : CollatzResearch.WordTrace tailWord_2838579 prefixEnd_2838579 107967066871033687430231 := by
  unfold tailWord_2838579
  simp only [CollatzResearch.WordTrace]
  refine ⟨103531481583320548542150791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69020987722213699028100527 103531481583320548542150791)
  ·
    refine ⟨155297222374980822813226187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103531481583320548542150791 155297222374980822813226187)
    ·
      refine ⟨232945833562471234219839281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155297222374980822813226187 232945833562471234219839281)
      ·
        refine ⟨174709375171853425664879461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232945833562471234219839281 174709375171853425664879461)
        ·
          refine ⟨32758007844722517312164899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174709375171853425664879461 32758007844722517312164899)
          ·
            refine ⟨49137011767083775968247349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32758007844722517312164899 49137011767083775968247349)
            ·
              refine ⟨4606594853164103997023189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49137011767083775968247349 4606594853164103997023189)
              ·
                refine ⟨107967066871033687430231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4606594853164103997023189 107967066871033687430231)
                ·
                  rfl

theorem cell22_2838579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 7].length) (baseStart_2838579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838579 prefixEnd_2838579 := by exact prefixLift 2838579
  have htrace : WordTrace (prefixWord ++ tailWord_2838579) baseStart_2838579 baseEnd_2838579 := by
    simpa [prefixWord, tailWord_2838579, baseEnd_2838579] using wordTrace_append hprefix tailTrace_2838579
  have hstable : (prefixWord ++ tailWord_2838579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838579).length < 2 ^ (prefixWord ++ tailWord_2838579).sum := by decide
  have hdescent : baseEnd_2838579 < baseStart_2838579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838598 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2838598 : Nat := 118140960795 + 2838598 * 2 ^ 59
def prefixEnd_2838598 : Nat := 4983230072969 + 3 ^ 40 * 2838598 * 2
def baseEnd_2838598 : Nat := 971710105927593470647021

theorem tailTrace_2838598 : CollatzResearch.WordTrace tailWord_2838598 prefixEnd_2838598 971710105927593470647021 := by
  unfold tailWord_2838598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235380455320366087096639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69021449713501143191394965 3235380455320366087096639)
  ·
    refine ⟨4853070682980549130644959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3235380455320366087096639 4853070682980549130644959)
    ·
      refine ⟨7279606024470823695967439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4853070682980549130644959 7279606024470823695967439)
      ·
        refine ⟨10919409036706235543951159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7279606024470823695967439 10919409036706235543951159)
        ·
          refine ⟨16379113555059353315926739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10919409036706235543951159 16379113555059353315926739)
          ·
            refine ⟨24568670332589029973890109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16379113555059353315926739 24568670332589029973890109)
            ·
              refine ⟨9213251374720886240208791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24568670332589029973890109 9213251374720886240208791)
              ·
                refine ⟨13819877062081329360313187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9213251374720886240208791 13819877062081329360313187)
                ·
                  refine ⟨20729815593121994040469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13819877062081329360313187 20729815593121994040469781)
                  ·
                    refine ⟨971710105927593470647021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20729815593121994040469781 971710105927593470647021)
                    ·
                      rfl

theorem cell22_2838598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2838598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838598 prefixEnd_2838598 := by exact prefixLift 2838598
  have htrace : WordTrace (prefixWord ++ tailWord_2838598) baseStart_2838598 baseEnd_2838598 := by
    simpa [prefixWord, tailWord_2838598, baseEnd_2838598] using wordTrace_append hprefix tailTrace_2838598
  have hstable : (prefixWord ++ tailWord_2838598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838598).length < 2 ^ (prefixWord ++ tailWord_2838598).sum := by decide
  have hdescent : baseEnd_2838598 < baseStart_2838598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838692 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2838692 : Nat := 118140960795 + 2838692 * 2 ^ 59
def prefixEnd_2838692 : Nat := 4983230072969 + 3 ^ 40 * 2838692 * 2
def baseEnd_2838692 : Nat := 323914094682869519598911

theorem tailTrace_2838692 : CollatzResearch.WordTrace tailWord_2838692 prefixEnd_2838692 323914094682869519598911 := by
  unfold tailWord_2838692
  simp only [CollatzResearch.WordTrace]
  refine ⟨51767801515955584420507165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69023735354607445894009553 51767801515955584420507165)
  ·
    refine ⟨19412925568483344157690187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51767801515955584420507165 19412925568483344157690187)
    ·
      refine ⟨29119388352725016236535281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19412925568483344157690187 29119388352725016236535281)
      ·
        refine ⟨21839541264543762177401461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29119388352725016236535281 21839541264543762177401461)
        ·
          refine ⟨2047456993550977704131387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21839541264543762177401461 2047456993550977704131387)
          ·
            refine ⟨3071185490326466556197081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047456993550977704131387 3071185490326466556197081)
            ·
              refine ⟨2303389117744849917147811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071185490326466556197081 2303389117744849917147811)
              ·
                refine ⟨3455083676617274875721717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303389117744849917147811 3455083676617274875721717)
                ·
                  refine ⟨323914094682869519598911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3455083676617274875721717 323914094682869519598911)
                  ·
                    rfl

theorem cell22_2838692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2838692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838692 prefixEnd_2838692 := by exact prefixLift 2838692
  have htrace : WordTrace (prefixWord ++ tailWord_2838692) baseStart_2838692 baseEnd_2838692 := by
    simpa [prefixWord, tailWord_2838692, baseEnd_2838692] using wordTrace_append hprefix tailTrace_2838692
  have hstable : (prefixWord ++ tailWord_2838692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838692).length < 2 ^ (prefixWord ++ tailWord_2838692).sum := by decide
  have hdescent : baseEnd_2838692 < baseStart_2838692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838763 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 3, 3]
def baseStart_2838763 : Nat := 118140960795 + 2838763 * 2 ^ 59
def prefixEnd_2838763 : Nat := 4983230072969 + 3 ^ 40 * 2838763 * 2
def baseEnd_2838763 : Nat := 971766588799588040271515

theorem tailTrace_2838763 : CollatzResearch.WordTrace tailWord_2838763 prefixEnd_2838763 971766588799588040271515 := by
  unfold tailWord_2838763
  simp only [CollatzResearch.WordTrace]
  refine ⟨103538192614653947966848943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69025461743102631977899295 103538192614653947966848943)
  ·
    refine ⟨155307288921980921950273415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103538192614653947966848943 155307288921980921950273415)
    ·
      refine ⟨232960933382971382925410123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155307288921980921950273415 232960933382971382925410123)
      ·
        refine ⟨349441400074457074388115185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232960933382971382925410123 349441400074457074388115185)
        ·
          refine ⟨262081050055842805791086389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349441400074457074388115185 262081050055842805791086389)
          ·
            refine ⟨24570098442735263042914349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262081050055842805791086389 24570098442735263042914349)
            ·
              refine ⟨9213786916025723641092881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24570098442735263042914349 9213786916025723641092881)
              ·
                refine ⟨6910340187019292730819661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9213786916025723641092881 6910340187019292730819661)
                ·
                  refine ⟨2591377570132234774057373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6910340187019292730819661 2591377570132234774057373)
                  ·
                    refine ⟨971766588799588040271515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2591377570132234774057373 971766588799588040271515)
                    ·
                      rfl

theorem cell22_2838763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 3].length) (baseStart_2838763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838763 prefixEnd_2838763 := by exact prefixLift 2838763
  have htrace : WordTrace (prefixWord ++ tailWord_2838763) baseStart_2838763 baseEnd_2838763 := by
    simpa [prefixWord, tailWord_2838763, baseEnd_2838763] using wordTrace_append hprefix tailTrace_2838763
  have hstable : (prefixWord ++ tailWord_2838763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838763).length < 2 ^ (prefixWord ++ tailWord_2838763).sum := by decide
  have hdescent : baseEnd_2838763 < baseStart_2838763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838765 : List Nat := [1, 5, 1, 2, 3, 1, 3, 6]
def baseStart_2838765 : Nat := 118140960795 + 2838765 * 2 ^ 59
def prefixEnd_2838765 : Nat := 4983230072969 + 3 ^ 40 * 2838765 * 2
def baseEnd_2838765 : Nat := 107974141493384522413501

theorem tailTrace_2838765 : CollatzResearch.WordTrace tailWord_2838765 prefixEnd_2838765 107974141493384522413501 := by
  unfold tailWord_2838765
  simp only [CollatzResearch.WordTrace]
  refine ⟨103538265560646702308421749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69025510373764468205614499 103538265560646702308421749)
  ·
    refine ⟨9706712396310628341414539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103538265560646702308421749 9706712396310628341414539)
    ·
      refine ⟨14560068594465942512121809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9706712396310628341414539 14560068594465942512121809)
      ·
        refine ⟨10920051445849456884091357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14560068594465942512121809 10920051445849456884091357)
        ·
          refine ⟨4095019292193546331534259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10920051445849456884091357 4095019292193546331534259)
          ·
            refine ⟨6142528938290319497301389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095019292193546331534259 6142528938290319497301389)
            ·
              refine ⟨2303448351858869811488021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6142528938290319497301389 2303448351858869811488021)
              ·
                refine ⟨107974141493384522413501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2303448351858869811488021 107974141493384522413501)
                ·
                  rfl

theorem cell22_2838765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 6].length) (baseStart_2838765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838765 prefixEnd_2838765 := by exact prefixLift 2838765
  have htrace : WordTrace (prefixWord ++ tailWord_2838765) baseStart_2838765 baseEnd_2838765 := by
    simpa [prefixWord, tailWord_2838765, baseEnd_2838765] using wordTrace_append hprefix tailTrace_2838765
  have hstable : (prefixWord ++ tailWord_2838765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838765).length < 2 ^ (prefixWord ++ tailWord_2838765).sum := by decide
  have hdescent : baseEnd_2838765 < baseStart_2838765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838793 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 5]
def baseStart_2838793 : Nat := 118140960795 + 2838793 * 2 ^ 59
def prefixEnd_2838793 : Nat := 4983230072969 + 3 ^ 40 * 2838793 * 2
def baseEnd_2838793 : Nat := 323925619470892654007141

theorem tailTrace_2838793 : CollatzResearch.WordTrace tailWord_2838793 prefixEnd_2838793 323925619470892654007141 := by
  unfold tailWord_2838793
  simp only [CollatzResearch.WordTrace]
  refine ⟨103539286804545263090441033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69026191203030175393627355 103539286804545263090441033)
  ·
    refine ⟨77654465103408947317830775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103539286804545263090441033 77654465103408947317830775)
    ·
      refine ⟨116481697655113420976746163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77654465103408947317830775 116481697655113420976746163)
      ·
        refine ⟨174722546482670131465119245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116481697655113420976746163 174722546482670131465119245)
        ·
          refine ⟨65520954931001299299419717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174722546482670131465119245 65520954931001299299419717)
          ·
            refine ⟨12285179049562743618641197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65520954931001299299419717 12285179049562743618641197)
            ·
              refine ⟨4606942143586028856990449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12285179049562743618641197 4606942143586028856990449)
              ·
                refine ⟨3455206607689521642742837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4606942143586028856990449 3455206607689521642742837)
                ·
                  refine ⟨323925619470892654007141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3455206607689521642742837 323925619470892654007141)
                  ·
                    rfl

theorem cell22_2838793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_2838793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838793 prefixEnd_2838793 := by exact prefixLift 2838793
  have htrace : WordTrace (prefixWord ++ tailWord_2838793) baseStart_2838793 baseEnd_2838793 := by
    simpa [prefixWord, tailWord_2838793, baseEnd_2838793] using wordTrace_append hprefix tailTrace_2838793
  have hstable : (prefixWord ++ tailWord_2838793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838793).length < 2 ^ (prefixWord ++ tailWord_2838793).sum := by decide
  have hdescent : baseEnd_2838793 < baseStart_2838793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2838885 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_2838885 : Nat := 118140960795 + 2838885 * 2 ^ 59
def prefixEnd_2838885 : Nat := 4983230072969 + 3 ^ 40 * 2838885 * 2
def baseEnd_2838885 : Nat := 971808351892820388721141

theorem tailTrace_2838885 : CollatzResearch.WordTrace tailWord_2838885 prefixEnd_2838885 971808351892820388721141 := by
  unfold tailWord_2838885
  simp only [CollatzResearch.WordTrace]
  refine ⟨103542642320211962802790109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69028428213474641868526739 103542642320211962802790109)
  ·
    refine ⟨38828490870079486051046291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103542642320211962802790109 38828490870079486051046291)
    ·
      refine ⟨58242736305119229076569437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38828490870079486051046291 58242736305119229076569437)
      ·
        refine ⟨21841026114419710903713539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58242736305119229076569437 21841026114419710903713539)
        ·
          refine ⟨32761539171629566355570309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21841026114419710903713539 32761539171629566355570309)
          ·
            refine ⟨6142788594680543691669433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32761539171629566355570309 6142788594680543691669433)
            ·
              refine ⟨4607091446010407768752075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6142788594680543691669433 4607091446010407768752075)
              ·
                refine ⟨6910637169015611653128113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607091446010407768752075 6910637169015611653128113)
                ·
                  refine ⟨5182977876761708739846085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910637169015611653128113 5182977876761708739846085)
                  ·
                    refine ⟨971808351892820388721141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5182977876761708739846085 971808351892820388721141)
                    ·
                      rfl

theorem cell22_2838885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_2838885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2838885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2838885 prefixEnd_2838885 := by exact prefixLift 2838885
  have htrace : WordTrace (prefixWord ++ tailWord_2838885) baseStart_2838885 baseEnd_2838885 := by
    simpa [prefixWord, tailWord_2838885, baseEnd_2838885] using wordTrace_append hprefix tailTrace_2838885
  have hstable : (prefixWord ++ tailWord_2838885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2838885).length < 2 ^ (prefixWord ++ tailWord_2838885).sum := by decide
  have hdescent : baseEnd_2838885 < baseStart_2838885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2838885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
