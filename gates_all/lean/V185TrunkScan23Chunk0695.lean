import V185TrunkScan23Chunk0694

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4108824 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4108824 : Nat := 118140960795 + 4108824 * 2 ^ 59
def prefixEnd_4108824 : Nat := 4983230072969 + 3 ^ 40 * 4108824 * 2
def baseEnd_4108824 : Nat := 2109801636729337440903869

theorem tailTrace_4108824 : CollatzResearch.WordTrace tailWord_4108824 prefixEnd_4108824 2109801636729337440903869 := by
  unfold tailWord_4108824
  simp only [CollatzResearch.WordTrace]
  refine ⟨74930561433219927058314763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99907415244293236077753017 74930561433219927058314763)
  ·
    refine ⟨112395842149829890587472145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74930561433219927058314763 112395842149829890587472145)
    ·
      refine ⟨84296881612372417940604109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112395842149829890587472145 84296881612372417940604109)
      ·
        refine ⟨31611330604639656727726541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84296881612372417940604109 31611330604639656727726541)
        ·
          refine ⟨11854248976739871272897453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31611330604639656727726541 11854248976739871272897453)
          ·
            refine ⟨4445343366277451727336545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11854248976739871272897453 4445343366277451727336545)
            ·
              refine ⟨3334007524708088795502409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4445343366277451727336545 3334007524708088795502409)
              ·
                refine ⟨2500505643531066596626807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334007524708088795502409 2500505643531066596626807)
                ·
                  refine ⟨3750758465296599894940211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500505643531066596626807 3750758465296599894940211)
                  ·
                    refine ⟨5626137697944899842410317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750758465296599894940211 5626137697944899842410317)
                    ·
                      refine ⟨2109801636729337440903869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5626137697944899842410317 2109801636729337440903869)
                      ·
                        rfl

theorem cell23_4108824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4108824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108824 prefixEnd_4108824 := by exact prefixLift 4108824
  have htrace : WordTrace (prefixWord ++ tailWord_4108824) baseStart_4108824 baseEnd_4108824 := by
    simpa [prefixWord, tailWord_4108824, baseEnd_4108824] using wordTrace_append hprefix tailTrace_4108824
  have hstable : (prefixWord ++ tailWord_4108824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108824).length < 2 ^ (prefixWord ++ tailWord_4108824).sum := by decide
  have hdescent : baseEnd_4108824 < baseStart_4108824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108840 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4108840 : Nat := 118140960795 + 4108840 * 2 ^ 59
def prefixEnd_4108840 : Nat := 4983230072969 + 3 ^ 40 * 4108840 * 2
def baseEnd_4108840 : Nat := 703269950806603126101265

theorem tailTrace_4108840 : CollatzResearch.WordTrace tailWord_4108840 prefixEnd_4108840 703269950806603126101265 := by
  unfold tailWord_4108840
  simp only [CollatzResearch.WordTrace]
  refine ⟨74930853217190944424605987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99907804289587925899474649 74930853217190944424605987)
  ·
    refine ⟨112396279825786416636908981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74930853217190944424605987 112396279825786416636908981)
    ·
      refine ⟨10537151233667476559710217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112396279825786416636908981 10537151233667476559710217)
      ·
        refine ⟨7902863425250607419782663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10537151233667476559710217 7902863425250607419782663)
        ·
          refine ⟨11854295137875911129673995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902863425250607419782663 11854295137875911129673995)
          ·
            refine ⟨17781442706813866694510993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854295137875911129673995 17781442706813866694510993)
            ·
              refine ⟨13336082030110400020883245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17781442706813866694510993 13336082030110400020883245)
              ·
                refine ⟨5001030761291400007831217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13336082030110400020883245 5001030761291400007831217)
                ·
                  refine ⟨3750773070968550005873413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001030761291400007831217 3750773070968550005873413)
                  ·
                    refine ⟨703269950806603126101265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3750773070968550005873413 703269950806603126101265)
                    ·
                      rfl

theorem cell23_4108840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4108840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108840 prefixEnd_4108840 := by exact prefixLift 4108840
  have htrace : WordTrace (prefixWord ++ tailWord_4108840) baseStart_4108840 baseEnd_4108840 := by
    simpa [prefixWord, tailWord_4108840, baseEnd_4108840] using wordTrace_append hprefix tailTrace_4108840
  have hstable : (prefixWord ++ tailWord_4108840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108840).length < 2 ^ (prefixWord ++ tailWord_4108840).sum := by decide
  have hdescent : baseEnd_4108840 < baseStart_4108840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108863 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 3]
def baseStart_4108863 : Nat := 118140960795 + 4108863 * 2 ^ 59
def prefixEnd_4108863 : Nat := 4983230072969 + 3 ^ 40 * 4108863 * 2
def baseEnd_4108863 : Nat := 2109821662474862788316189

theorem tailTrace_4108863 : CollatzResearch.WordTrace tailWord_4108863 prefixEnd_4108863 2109821662474862788316189 := by
  unfold tailWord_4108863
  simp only [CollatzResearch.WordTrace]
  refine ⟨149862545313298563777299243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99908363542199042518199495 149862545313298563777299243)
  ·
    refine ⟨224793817969947845665948865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149862545313298563777299243 224793817969947845665948865)
    ·
      refine ⟨168595363477460884249461649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224793817969947845665948865 168595363477460884249461649)
      ·
        refine ⟨126446522608095663187096237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168595363477460884249461649 126446522608095663187096237)
        ·
          refine ⟨47417445978035873695161089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126446522608095663187096237 47417445978035873695161089)
          ·
            refine ⟨35563084483526905271370817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47417445978035873695161089 35563084483526905271370817)
            ·
              refine ⟨26672313362645178953528113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35563084483526905271370817 26672313362645178953528113)
              ·
                refine ⟨20004235021983884215146085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26672313362645178953528113 20004235021983884215146085)
                ·
                  refine ⟨3750794066621978290339891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20004235021983884215146085 3750794066621978290339891)
                  ·
                    refine ⟨5626191099932967435509837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750794066621978290339891 5626191099932967435509837)
                    ·
                      refine ⟨2109821662474862788316189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5626191099932967435509837 2109821662474862788316189)
                      ·
                        rfl

theorem cell23_4108863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_4108863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108863 prefixEnd_4108863 := by exact prefixLift 4108863
  have htrace : WordTrace (prefixWord ++ tailWord_4108863) baseStart_4108863 baseEnd_4108863 := by
    simpa [prefixWord, tailWord_4108863, baseEnd_4108863] using wordTrace_append hprefix tailTrace_4108863
  have hstable : (prefixWord ++ tailWord_4108863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108863).length < 2 ^ (prefixWord ++ tailWord_4108863).sum := by decide
  have hdescent : baseEnd_4108863 < baseStart_4108863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108896 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_4108896 : Nat := 118140960795 + 4108896 * 2 ^ 59
def prefixEnd_4108896 : Nat := 4983230072969 + 3 ^ 40 * 4108896 * 2
def baseEnd_4108896 : Nat := 703279535778820386401179

theorem tailTrace_4108896 : CollatzResearch.WordTrace tailWord_4108896 prefixEnd_4108896 703279535778820386401179 := by
  unfold tailWord_4108896
  simp only [CollatzResearch.WordTrace]
  refine ⟨74931874461089505206625271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99909165948119340275500361 74931874461089505206625271)
  ·
    refine ⟨112397811691634257809937907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74931874461089505206625271 112397811691634257809937907)
    ·
      refine ⟨168596717537451386714906861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112397811691634257809937907 168596717537451386714906861)
      ·
        refine ⟨63223769076544270018090073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168596717537451386714906861 63223769076544270018090073)
        ·
          refine ⟨47417826807408202513567555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63223769076544270018090073 47417826807408202513567555)
          ·
            refine ⟨71126740211112303770351333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47417826807408202513567555 71126740211112303770351333)
            ·
              refine ⟨13336263789583556956940875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71126740211112303770351333 13336263789583556956940875)
              ·
                refine ⟨20004395684375335435411313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13336263789583556956940875 20004395684375335435411313)
                ·
                  refine ⟨15003296763281501576558485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20004395684375335435411313 15003296763281501576558485)
                  ·
                    refine ⟨703279535778820386401179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15003296763281501576558485 703279535778820386401179)
                    ·
                      rfl

theorem cell23_4108896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_4108896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108896 prefixEnd_4108896 := by exact prefixLift 4108896
  have htrace : WordTrace (prefixWord ++ tailWord_4108896) baseStart_4108896 baseEnd_4108896 := by
    simpa [prefixWord, tailWord_4108896, baseEnd_4108896] using wordTrace_append hprefix tailTrace_4108896
  have hstable : (prefixWord ++ tailWord_4108896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108896).length < 2 ^ (prefixWord ++ tailWord_4108896).sum := by decide
  have hdescent : baseEnd_4108896 < baseStart_4108896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108897 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_4108897 : Nat := 118140960795 + 4108897 * 2 ^ 59
def prefixEnd_4108897 : Nat := 4983230072969 + 3 ^ 40 * 4108897 * 2
def baseEnd_4108897 : Nat := 2109839120817115655291033

theorem tailTrace_4108897 : CollatzResearch.WordTrace tailWord_4108897 prefixEnd_4108897 2109839120817115655291033 := by
  unfold tailWord_4108897
  simp only [CollatzResearch.WordTrace]
  refine ⟨149863785395175387584036945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99909190263450258389357963 149863785395175387584036945)
  ·
    refine ⟨112397839046381540688027709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149863785395175387584036945 112397839046381540688027709)
    ·
      refine ⟨42149189642393077758010391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112397839046381540688027709 42149189642393077758010391)
      ·
        refine ⟨63223784463589616637015587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42149189642393077758010391 63223784463589616637015587)
        ·
          refine ⟨94835676695384424955523381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63223784463589616637015587 94835676695384424955523381)
          ·
            refine ⟨8890844690192289839580317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94835676695384424955523381 8890844690192289839580317)
            ·
              refine ⟨3334066758822108689842619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8890844690192289839580317 3334066758822108689842619)
              ·
                refine ⟨5001100138233163034763929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334066758822108689842619 5001100138233163034763929)
                ·
                  refine ⟨3750825103674872276072947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001100138233163034763929 3750825103674872276072947)
                  ·
                    refine ⟨5626237655512308414109421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3750825103674872276072947 5626237655512308414109421)
                    ·
                      refine ⟨2109839120817115655291033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5626237655512308414109421 2109839120817115655291033)
                      ·
                        rfl

theorem cell23_4108897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_4108897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108897 prefixEnd_4108897 := by exact prefixLift 4108897
  have htrace : WordTrace (prefixWord ++ tailWord_4108897) baseStart_4108897 baseEnd_4108897 := by
    simpa [prefixWord, tailWord_4108897, baseEnd_4108897] using wordTrace_append hprefix tailTrace_4108897
  have hstable : (prefixWord ++ tailWord_4108897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108897).length < 2 ^ (prefixWord ++ tailWord_4108897).sum := by decide
  have hdescent : baseEnd_4108897 < baseStart_4108897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4108963 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 4, 5, 2]
def baseStart_4108963 : Nat := 118140960795 + 4108963 * 2 ^ 59
def prefixEnd_4108963 : Nat := 4983230072969 + 3 ^ 40 * 4108963 * 2
def baseEnd_4108963 : Nat := 2109873010540312397065729

theorem tailTrace_4108963 : CollatzResearch.WordTrace tailWord_4108963 prefixEnd_4108963 2109873010540312397065729 := by
  unfold tailWord_4108963
  simp only [CollatzResearch.WordTrace]
  refine ⟨149866192612936280855939543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99910795075290853903959695 149866192612936280855939543)
  ·
    refine ⟨224799288919404421283909315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149866192612936280855939543 224799288919404421283909315)
    ·
      refine ⟨337198933379106631925863973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224799288919404421283909315 337198933379106631925863973)
      ·
        refine ⟨63224800008582493486099495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337198933379106631925863973 63224800008582493486099495)
        ·
          refine ⟨94837200012873740229149243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63224800008582493486099495 94837200012873740229149243)
          ·
            refine ⟨142255800019310610343723865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94837200012873740229149243 142255800019310610343723865)
            ·
              refine ⟨106691850014482957757792899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142255800019310610343723865 106691850014482957757792899)
              ·
                refine ⟨160037775021724436636689349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106691850014482957757792899 160037775021724436636689349)
                ·
                  refine ⟨30007082816573331869379253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160037775021724436636689349 30007082816573331869379253)
                  ·
                    refine ⟨2813164014053749862754305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30007082816573331869379253 2813164014053749862754305)
                    ·
                      refine ⟨2109873010540312397065729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813164014053749862754305 2109873010540312397065729)
                      ·
                        rfl

theorem cell23_4108963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_4108963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4108963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4108963 prefixEnd_4108963 := by exact prefixLift 4108963
  have htrace : WordTrace (prefixWord ++ tailWord_4108963) baseStart_4108963 baseEnd_4108963 := by
    simpa [prefixWord, tailWord_4108963, baseEnd_4108963] using wordTrace_append hprefix tailTrace_4108963
  have hstable : (prefixWord ++ tailWord_4108963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4108963).length < 2 ^ (prefixWord ++ tailWord_4108963).sum := by decide
  have hdescent : baseEnd_4108963 < baseStart_4108963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4108963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109027 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4109027 : Nat := 118140960795 + 4109027 * 2 ^ 59
def prefixEnd_4109027 : Nat := 4983230072969 + 3 ^ 40 * 4109027 * 2
def baseEnd_4109027 : Nat := 2109905873302200146665435

theorem tailTrace_4109027 : CollatzResearch.WordTrace tailWord_4109027 prefixEnd_4109027 2109905873302200146665435 := by
  unfold tailWord_4109027
  simp only [CollatzResearch.WordTrace]
  refine ⟨149868526884704419786269335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99912351256469613190846223 149868526884704419786269335)
  ·
    refine ⟨224802790327056629679404003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149868526884704419786269335 224802790327056629679404003)
    ·
      refine ⟨337204185490584944519106005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224802790327056629679404003 337204185490584944519106005)
      ·
        refine ⟨7903223097435584637166547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 337204185490584944519106005 7903223097435584637166547)
        ·
          refine ⟨11854834646153376955749821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903223097435584637166547 11854834646153376955749821)
          ·
            refine ⟨4445562992307516358406183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11854834646153376955749821 4445562992307516358406183)
            ·
              refine ⟨6668344488461274537609275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445562992307516358406183 6668344488461274537609275)
              ·
                refine ⟨10002516732691911806413913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6668344488461274537609275 10002516732691911806413913)
                ·
                  refine ⟨7501887549518933854810435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10002516732691911806413913 7501887549518933854810435)
                  ·
                    refine ⟨11252831324278400782215653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7501887549518933854810435 11252831324278400782215653)
                    ·
                      refine ⟨2109905873302200146665435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11252831324278400782215653 2109905873302200146665435)
                      ·
                        rfl

theorem cell23_4109027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4109027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109027 prefixEnd_4109027 := by exact prefixLift 4109027
  have htrace : WordTrace (prefixWord ++ tailWord_4109027) baseStart_4109027 baseEnd_4109027 := by
    simpa [prefixWord, tailWord_4109027, baseEnd_4109027] using wordTrace_append hprefix tailTrace_4109027
  have hstable : (prefixWord ++ tailWord_4109027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109027).length < 2 ^ (prefixWord ++ tailWord_4109027).sum := by decide
  have hdescent : baseEnd_4109027 < baseStart_4109027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109054 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_4109054 : Nat := 118140960795 + 4109054 * 2 ^ 59
def prefixEnd_4109054 : Nat := 4983230072969 + 3 ^ 40 * 4109054 * 2
def baseEnd_4109054 : Nat := 703306579093290513675937

theorem tailTrace_4109054 : CollatzResearch.WordTrace tailWord_4109054 prefixEnd_4109054 703306579093290513675937 := by
  unfold tailWord_4109054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18733688956950825424687777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99913007770404402265001477 18733688956950825424687777)
  ·
    refine ⟨14050266717713119068515833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18733688956950825424687777 14050266717713119068515833)
    ·
      refine ⟨10537700038284839301386875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14050266717713119068515833 10537700038284839301386875)
      ·
        refine ⟨15806550057427258952080313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537700038284839301386875 15806550057427258952080313)
        ·
          refine ⟨11854912543070444214060235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15806550057427258952080313 11854912543070444214060235)
          ·
            refine ⟨17782368814605666321090353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11854912543070444214060235 17782368814605666321090353)
            ·
              refine ⟨13336776610954249740817765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17782368814605666321090353 13336776610954249740817765)
              ·
                refine ⟨2500645614553921826403331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13336776610954249740817765 2500645614553921826403331)
                ·
                  refine ⟨3750968421830882739604997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500645614553921826403331 3750968421830882739604997)
                  ·
                    refine ⟨703306579093290513675937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3750968421830882739604997 703306579093290513675937)
                    ·
                      rfl

theorem cell23_4109054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_4109054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109054 prefixEnd_4109054 := by exact prefixLift 4109054
  have htrace : WordTrace (prefixWord ++ tailWord_4109054) baseStart_4109054 baseEnd_4109054 := by
    simpa [prefixWord, tailWord_4109054, baseEnd_4109054] using wordTrace_append hprefix tailTrace_4109054
  have hstable : (prefixWord ++ tailWord_4109054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109054).length < 2 ^ (prefixWord ++ tailWord_4109054).sum := by decide
  have hdescent : baseEnd_4109054 < baseStart_4109054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109093 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_4109093 : Nat := 118140960795 + 4109093 * 2 ^ 59
def prefixEnd_4109093 : Nat := 4983230072969 + 3 ^ 40 * 4109093 * 2
def baseEnd_4109093 : Nat := 703313254341798962813377

theorem tailTrace_4109093 : CollatzResearch.WordTrace tailWord_4109093 prefixEnd_4109093 703313254341798962813377 := by
  unfold tailWord_4109093
  simp only [CollatzResearch.WordTrace]
  refine ⟨149870934102465313058171933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99913956068310208705447955 149870934102465313058171933)
  ·
    refine ⟨56201600288424492396814475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149870934102465313058171933 56201600288424492396814475)
    ·
      refine ⟨84302400432636738595221713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56201600288424492396814475 84302400432636738595221713)
      ·
        refine ⟨63226800324477553946416285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84302400432636738595221713 63226800324477553946416285)
        ·
          refine ⟨23710050121679082729906107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63226800324477553946416285 23710050121679082729906107)
          ·
            refine ⟨35565075182518624094859161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23710050121679082729906107 35565075182518624094859161)
            ·
              refine ⟨26673806386888968071144371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35565075182518624094859161 26673806386888968071144371)
              ·
                refine ⟨40010709580333452106716557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26673806386888968071144371 40010709580333452106716557)
                ·
                  refine ⟨15004016092625044540018709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40010709580333452106716557 15004016092625044540018709)
                  ·
                    refine ⟨703313254341798962813377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15004016092625044540018709 703313254341798962813377)
                    ·
                      rfl

theorem cell23_4109093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_4109093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109093 prefixEnd_4109093 := by exact prefixLift 4109093
  have htrace : WordTrace (prefixWord ++ tailWord_4109093) baseStart_4109093 baseEnd_4109093 := by
    simpa [prefixWord, tailWord_4109093, baseEnd_4109093] using wordTrace_append hprefix tailTrace_4109093
  have hstable : (prefixWord ++ tailWord_4109093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109093).length < 2 ^ (prefixWord ++ tailWord_4109093).sum := by decide
  have hdescent : baseEnd_4109093 < baseStart_4109093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109100 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_4109100 : Nat := 118140960795 + 4109100 * 2 ^ 59
def prefixEnd_4109100 : Nat := 4983230072969 + 3 ^ 40 * 4109100 * 2
def baseEnd_4109100 : Nat := 2109943357389978361052599

theorem tailTrace_4109100 : CollatzResearch.WordTrace tailWord_4109100 prefixEnd_4109100 2109943357389978361052599 := by
  unfold tailWord_4109100
  simp only [CollatzResearch.WordTrace]
  refine ⟨74935594706719976626838377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99914126275626635502451169 74935594706719976626838377)
  ·
    refine ⟨56201696030039982470128783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74935594706719976626838377 56201696030039982470128783)
    ·
      refine ⟨84302544045059973705193175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56201696030039982470128783 84302544045059973705193175)
      ·
        refine ⟨126453816067589960557789763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84302544045059973705193175 126453816067589960557789763)
        ·
          refine ⟨189680724101384940836684645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126453816067589960557789763 189680724101384940836684645)
          ·
            refine ⟨35565135769009676406878371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189680724101384940836684645 35565135769009676406878371)
            ·
              refine ⟨53347703653514514610317557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35565135769009676406878371 53347703653514514610317557)
              ·
                refine ⟨5001347217516985744717271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53347703653514514610317557 5001347217516985744717271)
                ·
                  refine ⟨7502020826275478617075907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001347217516985744717271 7502020826275478617075907)
                  ·
                    refine ⟨11253031239413217925613861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502020826275478617075907 11253031239413217925613861)
                    ·
                      refine ⟨2109943357389978361052599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11253031239413217925613861 2109943357389978361052599)
                      ·
                        rfl

theorem cell23_4109100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_4109100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109100 prefixEnd_4109100 := by exact prefixLift 4109100
  have htrace : WordTrace (prefixWord ++ tailWord_4109100) baseStart_4109100 baseEnd_4109100 := by
    simpa [prefixWord, tailWord_4109100, baseEnd_4109100] using wordTrace_append hprefix tailTrace_4109100
  have hstable : (prefixWord ++ tailWord_4109100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109100).length < 2 ^ (prefixWord ++ tailWord_4109100).sum := by decide
  have hdescent : baseEnd_4109100 < baseStart_4109100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109123 : List Nat := [1, 1, 1, 3, 1, 4, 4, 8]
def baseStart_4109123 : Nat := 118140960795 + 4109123 * 2 ^ 59
def prefixEnd_4109123 : Nat := 4983230072969 + 3 ^ 40 * 4109123 * 2
def baseEnd_4109123 : Nat := 78146487683149324854259

theorem tailTrace_4109123 : CollatzResearch.WordTrace tailWord_4109123 prefixEnd_4109123 78146487683149324854259 := by
  unfold tailWord_4109123
  simp only [CollatzResearch.WordTrace]
  refine ⟨149872028292356628181764023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99914685528237752121176015 149872028292356628181764023)
  ·
    refine ⟨224808042438534942272646035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149872028292356628181764023 224808042438534942272646035)
    ·
      refine ⟨337212063657802413408969053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224808042438534942272646035 337212063657802413408969053)
      ·
        refine ⟨126454523871675905028363395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337212063657802413408969053 126454523871675905028363395)
        ·
          refine ⟨189681785807513857542545093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126454523871675905028363395 189681785807513857542545093)
          ·
            refine ⟨35565334838908848289227205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189681785807513857542545093 35565334838908848289227205)
            ·
              refine ⟨6668500282295409054230101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35565334838908848289227205 6668500282295409054230101)
              ·
                refine ⟨78146487683149324854259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6668500282295409054230101 78146487683149324854259)
                ·
                  rfl

theorem cell23_4109123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 8].length) (baseStart_4109123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109123 prefixEnd_4109123 := by exact prefixLift 4109123
  have htrace : WordTrace (prefixWord ++ tailWord_4109123) baseStart_4109123 baseEnd_4109123 := by
    simpa [prefixWord, tailWord_4109123, baseEnd_4109123] using wordTrace_append hprefix tailTrace_4109123
  have hstable : (prefixWord ++ tailWord_4109123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109123).length < 2 ^ (prefixWord ++ tailWord_4109123).sum := by decide
  have hdescent : baseEnd_4109123 < baseStart_4109123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109137 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_4109137 : Nat := 118140960795 + 4109137 * 2 ^ 59
def prefixEnd_4109137 : Nat := 4983230072969 + 3 ^ 40 * 4109137 * 2
def baseEnd_4109137 : Nat := 2109962356174194716289929

theorem tailTrace_4109137 : CollatzResearch.WordTrace tailWord_4109137 prefixEnd_4109137 2109962356174194716289929 := by
  unfold tailWord_4109137
  simp only [CollatzResearch.WordTrace]
  refine ⟨149872538914305908572773665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99915025942870605715182443 149872538914305908572773665)
  ·
    refine ⟨112404404185729431429580249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149872538914305908572773665 112404404185729431429580249)
    ·
      refine ⟨84303303139297073572185187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112404404185729431429580249 84303303139297073572185187)
      ·
        refine ⟨126454954708945610358277781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84303303139297073572185187 126454954708945610358277781)
        ·
          refine ⟨5927576001981825485544271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126454954708945610358277781 5927576001981825485544271)
          ·
            refine ⟨8891364002972738228316407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5927576001981825485544271 8891364002972738228316407)
            ·
              refine ⟨13337046004459107342474611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891364002972738228316407 13337046004459107342474611)
              ·
                refine ⟨20005569006688661013711917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13337046004459107342474611 20005569006688661013711917)
                ·
                  refine ⟨7502088377508247880141969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20005569006688661013711917 7502088377508247880141969)
                  ·
                    refine ⟨5626566283131185910106477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502088377508247880141969 5626566283131185910106477)
                    ·
                      refine ⟨2109962356174194716289929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5626566283131185910106477 2109962356174194716289929)
                      ·
                        rfl

theorem cell23_4109137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_4109137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109137 prefixEnd_4109137 := by exact prefixLift 4109137
  have htrace : WordTrace (prefixWord ++ tailWord_4109137) baseStart_4109137 baseEnd_4109137 := by
    simpa [prefixWord, tailWord_4109137, baseEnd_4109137] using wordTrace_append hprefix tailTrace_4109137
  have hstable : (prefixWord ++ tailWord_4109137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109137).length < 2 ^ (prefixWord ++ tailWord_4109137).sum := by decide
  have hdescent : baseEnd_4109137 < baseStart_4109137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109154 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4109154 : Nat := 118140960795 + 4109154 * 2 ^ 59
def prefixEnd_4109154 : Nat := 4983230072969 + 3 ^ 40 * 4109154 * 2
def baseEnd_4109154 : Nat := 2109971085345321149777351

theorem tailTrace_4109154 : CollatzResearch.WordTrace tailWord_4109154 prefixEnd_4109154 2109971085345321149777351 := by
  unfold tailWord_4109154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37468289738811080119035629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99915439303496213650761677 37468289738811080119035629)
  ·
    refine ⟨14050608652054155044638361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37468289738811080119035629 14050608652054155044638361)
    ·
      refine ⟨10537956489040616283478771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14050608652054155044638361 10537956489040616283478771)
      ·
        refine ⟨15806934733560924425218157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537956489040616283478771 15806934733560924425218157)
        ·
          refine ⟨5927600525085346659456809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15806934733560924425218157 5927600525085346659456809)
          ·
            refine ⟨4445700393814009994592607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5927600525085346659456809 4445700393814009994592607)
            ·
              refine ⟨6668550590721014991888911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445700393814009994592607 6668550590721014991888911)
              ·
                refine ⟨10002825886081522487833367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6668550590721014991888911 10002825886081522487833367)
                ·
                  refine ⟨15004238829122283731750051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10002825886081522487833367 15004238829122283731750051)
                  ·
                    refine ⟨22506358243683425597625077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15004238829122283731750051 22506358243683425597625077)
                    ·
                      refine ⟨2109971085345321149777351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22506358243683425597625077 2109971085345321149777351)
                      ·
                        rfl

theorem cell23_4109154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4109154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109154 prefixEnd_4109154 := by exact prefixLift 4109154
  have htrace : WordTrace (prefixWord ++ tailWord_4109154) baseStart_4109154 baseEnd_4109154 := by
    simpa [prefixWord, tailWord_4109154, baseEnd_4109154] using wordTrace_append hprefix tailTrace_4109154
  have hstable : (prefixWord ++ tailWord_4109154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109154).length < 2 ^ (prefixWord ++ tailWord_4109154).sum := by decide
  have hdescent : baseEnd_4109154 < baseStart_4109154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109163 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5]
def baseStart_4109163 : Nat := 118140960795 + 4109163 * 2 ^ 59
def prefixEnd_4109163 : Nat := 4983230072969 + 3 ^ 40 * 4109163 * 2
def baseEnd_4109163 : Nat := 2109975706671211614564809

theorem tailTrace_4109163 : CollatzResearch.WordTrace tailWord_4109163 prefixEnd_4109163 2109975706671211614564809 := by
  unfold tailWord_4109163
  simp only [CollatzResearch.WordTrace]
  refine ⟨149873487212211715013220143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99915658141474476675480095 149873487212211715013220143)
  ·
    refine ⟨224810230818317572519830215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149873487212211715013220143 224810230818317572519830215)
    ·
      refine ⟨337215346227476358779745323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224810230818317572519830215 337215346227476358779745323)
      ·
        refine ⟨505823019341214538169617985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337215346227476358779745323 505823019341214538169617985)
        ·
          refine ⟨379367264505910903627213489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505823019341214538169617985 379367264505910903627213489)
          ·
            refine ⟨284525448379433177720410117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379367264505910903627213489 284525448379433177720410117)
            ·
              refine ⟨53348521571143720822576897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284525448379433177720410117 53348521571143720822576897)
              ·
                refine ⟨40011391178357790616932673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53348521571143720822576897 40011391178357790616932673)
                ·
                  refine ⟨30008543383768342962699505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40011391178357790616932673 30008543383768342962699505)
                  ·
                    refine ⟨22506407537826257222024629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30008543383768342962699505 22506407537826257222024629)
                    ·
                      refine ⟨2109975706671211614564809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22506407537826257222024629 2109975706671211614564809)
                      ·
                        rfl

theorem cell23_4109163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_4109163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109163 prefixEnd_4109163 := by exact prefixLift 4109163
  have htrace : WordTrace (prefixWord ++ tailWord_4109163) baseStart_4109163 baseEnd_4109163 := by
    simpa [prefixWord, tailWord_4109163, baseEnd_4109163] using wordTrace_append hprefix tailTrace_4109163
  have hstable : (prefixWord ++ tailWord_4109163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109163).length < 2 ^ (prefixWord ++ tailWord_4109163).sum := by decide
  have hdescent : baseEnd_4109163 < baseStart_4109163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109177 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 3, 3, 2]
def baseStart_4109177 : Nat := 118140960795 + 4109177 * 2 ^ 59
def prefixEnd_4109177 : Nat := 4983230072969 + 3 ^ 40 * 4109177 * 2
def baseEnd_4109177 : Nat := 2109982895400374559789745

theorem tailTrace_4109177 : CollatzResearch.WordTrace tailWord_4109177 prefixEnd_4109177 2109982895400374559789745 := by
  unfold tailWord_4109177
  simp only [CollatzResearch.WordTrace]
  refine ⟨149873997834160995404229785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99915998556107330269486523 149873997834160995404229785)
  ·
    refine ⟨112405498375620746553172339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149873997834160995404229785 112405498375620746553172339)
    ·
      refine ⟨168608247563431119829758509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112405498375620746553172339 168608247563431119829758509)
      ·
        refine ⟨63228092836286669936159441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168608247563431119829758509 63228092836286669936159441)
        ·
          refine ⟨47421069627215002452119581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63228092836286669936159441 47421069627215002452119581)
          ·
            refine ⟨17782901110205625919544843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47421069627215002452119581 17782901110205625919544843)
            ·
              refine ⟨26674351665308438879317265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17782901110205625919544843 26674351665308438879317265)
              ·
                refine ⟨20005763748981329159487949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26674351665308438879317265 20005763748981329159487949)
                ·
                  refine ⟨7502161405867998434807981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20005763748981329159487949 7502161405867998434807981)
                  ·
                    refine ⟨2813310527200499413052993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7502161405867998434807981 2813310527200499413052993)
                    ·
                      refine ⟨2109982895400374559789745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813310527200499413052993 2109982895400374559789745)
                      ·
                        rfl

theorem cell23_4109177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_4109177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109177 prefixEnd_4109177 := by exact prefixLift 4109177
  have htrace : WordTrace (prefixWord ++ tailWord_4109177) baseStart_4109177 baseEnd_4109177 := by
    simpa [prefixWord, tailWord_4109177, baseEnd_4109177] using wordTrace_append hprefix tailTrace_4109177
  have hstable : (prefixWord ++ tailWord_4109177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109177).length < 2 ^ (prefixWord ++ tailWord_4109177).sum := by decide
  have hdescent : baseEnd_4109177 < baseStart_4109177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109183 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 1, 8]
def baseStart_4109183 : Nat := 118140960795 + 4109183 * 2 ^ 59
def prefixEnd_4109183 : Nat := 4983230072969 + 3 ^ 40 * 4109183 * 2
def baseEnd_4109183 : Nat := 703328658761433845438239

theorem tailTrace_4109183 : CollatzResearch.WordTrace tailWord_4109183 prefixEnd_4109183 703328658761433845438239 := by
  unfold tailWord_4109183
  simp only [CollatzResearch.WordTrace]
  refine ⟨149874216672139258428948203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99916144448092838952632135 149874216672139258428948203)
  ·
    refine ⟨224811325008208887643422305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149874216672139258428948203 224811325008208887643422305)
    ·
      refine ⟨168608493756156665732566729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224811325008208887643422305 168608493756156665732566729)
      ·
        refine ⟨126456370317117499299425047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168608493756156665732566729 126456370317117499299425047)
        ·
          refine ⟨189684555475676248949137571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126456370317117499299425047 189684555475676248949137571)
          ·
            refine ⟨284526833213514373423706357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189684555475676248949137571 284526833213514373423706357)
            ·
              refine ⟨26674390613766972508472471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284526833213514373423706357 26674390613766972508472471)
              ·
                refine ⟨40011585920650458762708707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26674390613766972508472471 40011585920650458762708707)
                ·
                  refine ⟨60017378880975688144063061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40011585920650458762708707 60017378880975688144063061)
                  ·
                    refine ⟨703328658761433845438239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60017378880975688144063061 703328658761433845438239)
                    ·
                      rfl

theorem cell23_4109183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 8].length) (baseStart_4109183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109183 prefixEnd_4109183 := by exact prefixLift 4109183
  have htrace : WordTrace (prefixWord ++ tailWord_4109183) baseStart_4109183 baseEnd_4109183 := by
    simpa [prefixWord, tailWord_4109183, baseEnd_4109183] using wordTrace_append hprefix tailTrace_4109183
  have hstable : (prefixWord ++ tailWord_4109183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109183).length < 2 ^ (prefixWord ++ tailWord_4109183).sum := by decide
  have hdescent : baseEnd_4109183 < baseStart_4109183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109194 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4109194 : Nat := 118140960795 + 4109194 * 2 ^ 59
def prefixEnd_4109194 : Nat := 4983230072969 + 3 ^ 40 * 4109194 * 2
def baseEnd_4109194 : Nat := 2109991624571500993277167

theorem tailTrace_4109194 : CollatzResearch.WordTrace tailWord_4109194 prefixEnd_4109194 2109991624571500993277167 := by
  unfold tailWord_4109194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37468654468774851826899659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99916411916732938205065757 37468654468774851826899659)
  ·
    refine ⟨56202981703162277740349489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37468654468774851826899659 56202981703162277740349489)
    ·
      refine ⟨42152236277371708305262117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56202981703162277740349489 42152236277371708305262117)
      ·
        refine ⟨7903544302007195307236647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42152236277371708305262117 7903544302007195307236647)
        ·
          refine ⟨11855316453010792960854971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7903544302007195307236647 11855316453010792960854971)
          ·
            refine ⟨17782974679516189441282457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855316453010792960854971 17782974679516189441282457)
            ·
              refine ⟨13337231009637142080961843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17782974679516189441282457 13337231009637142080961843)
              ·
                refine ⟨20005846514455713121442765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13337231009637142080961843 20005846514455713121442765)
                ·
                  refine ⟨7502192442920892420541037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20005846514455713121442765 7502192442920892420541037)
                  ·
                    refine ⟨2813322166095334657702889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7502192442920892420541037 2813322166095334657702889)
                    ·
                      refine ⟨2109991624571500993277167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813322166095334657702889 2109991624571500993277167)
                      ·
                        rfl

theorem cell23_4109194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4109194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109194 prefixEnd_4109194 := by exact prefixLift 4109194
  have htrace : WordTrace (prefixWord ++ tailWord_4109194) baseStart_4109194 baseEnd_4109194 := by
    simpa [prefixWord, tailWord_4109194, baseEnd_4109194] using wordTrace_append hprefix tailTrace_4109194
  have hstable : (prefixWord ++ tailWord_4109194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109194).length < 2 ^ (prefixWord ++ tailWord_4109194).sum := by decide
  have hdescent : baseEnd_4109194 < baseStart_4109194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109207 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 1, 4, 2]
def baseStart_4109207 : Nat := 118140960795 + 4109207 * 2 ^ 59
def prefixEnd_4109207 : Nat := 4983230072969 + 3 ^ 40 * 4109207 * 2
def baseEnd_4109207 : Nat := 2109998299820009442414607

theorem tailTrace_4109207 : CollatzResearch.WordTrace tailWord_4109207 prefixEnd_4109207 2109998299820009442414607 := by
  unfold tailWord_4109207
  simp only [CollatzResearch.WordTrace]
  refine ⟨149875092024052310527821875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99916728016034873685214583 149875092024052310527821875)
  ·
    refine ⟨224812638036078465791732813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149875092024052310527821875 224812638036078465791732813)
    ·
      refine ⟨84304739263529424671899805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224812638036078465791732813 84304739263529424671899805)
      ·
        refine ⟨31614277223823534251962427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84304739263529424671899805 31614277223823534251962427)
        ·
          refine ⟨47421415835735301377943641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31614277223823534251962427 47421415835735301377943641)
          ·
            refine ⟨35566061876801476033457731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47421415835735301377943641 35566061876801476033457731)
            ·
              refine ⟨53349092815202214050186597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35566061876801476033457731 53349092815202214050186597)
              ·
                refine ⟨10002954902850415134409987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53349092815202214050186597 10002954902850415134409987)
                ·
                  refine ⟨15004432354275622701614981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10002954902850415134409987 15004432354275622701614981)
                  ·
                    refine ⟨2813331066426679256552809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15004432354275622701614981 2813331066426679256552809)
                    ·
                      refine ⟨2109998299820009442414607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813331066426679256552809 2109998299820009442414607)
                      ·
                        rfl

theorem cell23_4109207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_4109207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109207 prefixEnd_4109207 := by exact prefixLift 4109207
  have htrace : WordTrace (prefixWord ++ tailWord_4109207) baseStart_4109207 baseEnd_4109207 := by
    simpa [prefixWord, tailWord_4109207, baseEnd_4109207] using wordTrace_append hprefix tailTrace_4109207
  have hstable : (prefixWord ++ tailWord_4109207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109207).length < 2 ^ (prefixWord ++ tailWord_4109207).sum := by decide
  have hdescent : baseEnd_4109207 < baseStart_4109207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109220 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_4109220 : Nat := 118140960795 + 4109220 * 2 ^ 59
def prefixEnd_4109220 : Nat := 4983230072969 + 3 ^ 40 * 4109220 * 2
def baseEnd_4109220 : Nat := 2110004975068517891552047

theorem tailTrace_4109220 : CollatzResearch.WordTrace tailWord_4109220 prefixEnd_4109220 2110004975068517891552047 := by
  unfold tailWord_4109220
  simp only [CollatzResearch.WordTrace]
  refine ⟨74937783086502606874022557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99917044115336809165363409 74937783086502606874022557)
  ·
    refine ⟨28101668657438477577758459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74937783086502606874022557 28101668657438477577758459)
    ·
      refine ⟨42152502986157716366637689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28101668657438477577758459 42152502986157716366637689)
      ·
        refine ⟨31614377239618287274978267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42152502986157716366637689 31614377239618287274978267)
        ·
          refine ⟨47421565859427430912467401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31614377239618287274978267 47421565859427430912467401)
          ·
            refine ⟨35566174394570573184350551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47421565859427430912467401 35566174394570573184350551)
            ·
              refine ⟨53349261591855859776525827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35566174394570573184350551 53349261591855859776525827)
              ·
                refine ⟨80023892387783789664788741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53349261591855859776525827 80023892387783789664788741)
                ·
                  refine ⟨15004479822709460562147889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80023892387783789664788741 15004479822709460562147889)
                  ·
                    refine ⟨11253359867032095421610917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15004479822709460562147889 11253359867032095421610917)
                    ·
                      refine ⟨2110004975068517891552047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11253359867032095421610917 2110004975068517891552047)
                      ·
                        rfl

theorem cell23_4109220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_4109220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109220 prefixEnd_4109220 := by exact prefixLift 4109220
  have htrace : WordTrace (prefixWord ++ tailWord_4109220) baseStart_4109220 baseEnd_4109220 := by
    simpa [prefixWord, tailWord_4109220, baseEnd_4109220] using wordTrace_append hprefix tailTrace_4109220
  have hstable : (prefixWord ++ tailWord_4109220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109220).length < 2 ^ (prefixWord ++ tailWord_4109220).sum := by decide
  have hdescent : baseEnd_4109220 < baseStart_4109220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109260 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_4109260 : Nat := 118140960795 + 4109260 * 2 ^ 59
def prefixEnd_4109260 : Nat := 4983230072969 + 3 ^ 40 * 4109260 * 2
def baseEnd_4109260 : Nat := 703341838098232578350621

theorem tailTrace_4109260 : CollatzResearch.WordTrace tailWord_4109260 prefixEnd_4109260 703341838098232578350621 := by
  unfold tailWord_4109260
  simp only [CollatzResearch.WordTrace]
  refine ⟨74938512546430150289750617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99918016728573533719667489 74938512546430150289750617)
  ·
    refine ⟨56203884409822612717312963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74938512546430150289750617 56203884409822612717312963)
    ·
      refine ⟨84305826614733919075969445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56203884409822612717312963 84305826614733919075969445)
      ·
        refine ⟨15807342490262609826744271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84305826614733919075969445 15807342490262609826744271)
        ·
          refine ⟨23711013735393914740116407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15807342490262609826744271 23711013735393914740116407)
          ·
            refine ⟨35566520603090872110174611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23711013735393914740116407 35566520603090872110174611)
            ·
              refine ⟨53349780904636308165261917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35566520603090872110174611 53349780904636308165261917)
              ·
                refine ⟨20006167839238615561973219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53349780904636308165261917 20006167839238615561973219)
                ·
                  refine ⟨30009251758857923342959829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20006167839238615561973219 30009251758857923342959829)
                  ·
                    refine ⟨703341838098232578350621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30009251758857923342959829 703341838098232578350621)
                    ·
                      rfl

theorem cell23_4109260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_4109260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109260 prefixEnd_4109260 := by exact prefixLift 4109260
  have htrace : WordTrace (prefixWord ++ tailWord_4109260) baseStart_4109260 baseEnd_4109260 := by
    simpa [prefixWord, tailWord_4109260, baseEnd_4109260] using wordTrace_append hprefix tailTrace_4109260
  have hstable : (prefixWord ++ tailWord_4109260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109260).length < 2 ^ (prefixWord ++ tailWord_4109260).sum := by decide
  have hdescent : baseEnd_4109260 < baseStart_4109260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109277 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4109277 : Nat := 118140960795 + 4109277 * 2 ^ 59
def prefixEnd_4109277 : Nat := 4983230072969 + 3 ^ 40 * 4109277 * 2
def baseEnd_4109277 : Nat := 703344747821941389513095

theorem tailTrace_4109277 : CollatzResearch.WordTrace tailWord_4109277 prefixEnd_4109277 703344747821941389513095 := by
  unfold tailWord_4109277
  simp only [CollatzResearch.WordTrace]
  refine ⟨149877645133798712482870085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99918430089199141655246723 149877645133798712482870085)
  ·
    refine ⟨28102058462587258590538141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149877645133798712482870085 28102058462587258590538141)
    ·
      refine ⟨10538271923470221971451803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28102058462587258590538141 10538271923470221971451803)
      ·
        refine ⟨15807407885205332957177705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10538271923470221971451803 15807407885205332957177705)
        ·
          refine ⟨11855555913903999717883279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15807407885205332957177705 11855555913903999717883279)
          ·
            refine ⟨17783333870855999576824919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855555913903999717883279 17783333870855999576824919)
            ·
              refine ⟨26675000806283999365237379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17783333870855999576824919 26675000806283999365237379)
              ·
                refine ⟨40012501209425999047856069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26675000806283999365237379 40012501209425999047856069)
                ·
                  refine ⟨7502343976767374821473013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40012501209425999047856069 7502343976767374821473013)
                  ·
                    refine ⟨703344747821941389513095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7502343976767374821473013 703344747821941389513095)
                    ·
                      rfl

theorem cell23_4109277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4109277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109277 prefixEnd_4109277 := by exact prefixLift 4109277
  have htrace : WordTrace (prefixWord ++ tailWord_4109277) baseStart_4109277 baseEnd_4109277 := by
    simpa [prefixWord, tailWord_4109277, baseEnd_4109277] using wordTrace_append hprefix tailTrace_4109277
  have hstable : (prefixWord ++ tailWord_4109277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109277).length < 2 ^ (prefixWord ++ tailWord_4109277).sum := by decide
  have hdescent : baseEnd_4109277 < baseStart_4109277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109287 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4109287 : Nat := 118140960795 + 4109287 * 2 ^ 59
def prefixEnd_4109287 : Nat := 4983230072969 + 3 ^ 40 * 4109287 * 2
def baseEnd_4109287 : Nat := 2110039378272369129414239

theorem tailTrace_4109287 : CollatzResearch.WordTrace tailWord_4109287 prefixEnd_4109287 2110039378272369129414239 := by
  unfold tailWord_4109287
  simp only [CollatzResearch.WordTrace]
  refine ⟨149878009863762484190734115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99918673242508322793822743 149878009863762484190734115)
  ·
    refine ⟨224817014795643726286101173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149878009863762484190734115 224817014795643726286101173)
    ·
      refine ⟨21076595137091599339321985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224817014795643726286101173 21076595137091599339321985)
      ·
        refine ⟨15807446352818699504491489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21076595137091599339321985 15807446352818699504491489)
        ·
          refine ⟨11855584764614024628368617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15807446352818699504491489 11855584764614024628368617)
          ·
            refine ⟨8891688573460518471276463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11855584764614024628368617 8891688573460518471276463)
            ·
              refine ⟨13337532860190777706914695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891688573460518471276463 13337532860190777706914695)
              ·
                refine ⟨20006299290286166560372043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13337532860190777706914695 20006299290286166560372043)
                ·
                  refine ⟨30009448935429249840558065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20006299290286166560372043 30009448935429249840558065)
                  ·
                    refine ⟨22507086701571937380418549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30009448935429249840558065 22507086701571937380418549)
                    ·
                      refine ⟨2110039378272369129414239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22507086701571937380418549 2110039378272369129414239)
                      ·
                        rfl

theorem cell23_4109287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4109287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109287 prefixEnd_4109287 := by exact prefixLift 4109287
  have htrace : WordTrace (prefixWord ++ tailWord_4109287) baseStart_4109287 baseEnd_4109287 := by
    simpa [prefixWord, tailWord_4109287, baseEnd_4109287] using wordTrace_append hprefix tailTrace_4109287
  have hstable : (prefixWord ++ tailWord_4109287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109287).length < 2 ^ (prefixWord ++ tailWord_4109287).sum := by decide
  have hdescent : baseEnd_4109287 < baseStart_4109287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109360 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_4109360 : Nat := 118140960795 + 4109360 * 2 ^ 59
def prefixEnd_4109360 : Nat := 4983230072969 + 3 ^ 40 * 4109360 * 2
def baseEnd_4109360 : Nat := 2110076862360147343801403

theorem tailTrace_4109360 : CollatzResearch.WordTrace tailWord_4109360 prefixEnd_4109360 2110076862360147343801403 := by
  unfold tailWord_4109360
  simp only [CollatzResearch.WordTrace]
  refine ⟨74940336196249008829070767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99920448261665345105427689 74940336196249008829070767)
  ·
    refine ⟨112410504294373513243606151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74940336196249008829070767 112410504294373513243606151)
    ·
      refine ⟨168615756441560269865409227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112410504294373513243606151 168615756441560269865409227)
      ·
        refine ⟨252923634662340404798113841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168615756441560269865409227 252923634662340404798113841)
        ·
          refine ⟨189692725996755303598585381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252923634662340404798113841 189692725996755303598585381)
          ·
            refine ⟨35567386124391619424734759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189692725996755303598585381 35567386124391619424734759)
            ·
              refine ⟨53351079186587429137102139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35567386124391619424734759 53351079186587429137102139)
              ·
                refine ⟨80026618779881143705653209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53351079186587429137102139 80026618779881143705653209)
                ·
                  refine ⟨60019964084910857779239907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80026618779881143705653209 60019964084910857779239907)
                  ·
                    refine ⟨90029946127366286668859861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60019964084910857779239907 90029946127366286668859861)
                    ·
                      refine ⟨2110076862360147343801403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90029946127366286668859861 2110076862360147343801403)
                      ·
                        rfl

theorem cell23_4109360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_4109360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109360 prefixEnd_4109360 := by exact prefixLift 4109360
  have htrace : WordTrace (prefixWord ++ tailWord_4109360) baseStart_4109360 baseEnd_4109360 := by
    simpa [prefixWord, tailWord_4109360, baseEnd_4109360] using wordTrace_append hprefix tailTrace_4109360
  have hstable : (prefixWord ++ tailWord_4109360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109360).length < 2 ^ (prefixWord ++ tailWord_4109360).sum := by decide
  have hdescent : baseEnd_4109360 < baseStart_4109360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109367 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 1, 5]
def baseStart_4109367 : Nat := 118140960795 + 4109367 * 2 ^ 59
def prefixEnd_4109367 : Nat := 4983230072969 + 3 ^ 40 * 4109367 * 2
def baseEnd_4109367 : Nat := 703360152241576272137957

theorem tailTrace_4109367 : CollatzResearch.WordTrace tailWord_4109367 prefixEnd_4109367 703360152241576272137957 := by
  unfold tailWord_4109367
  simp only [CollatzResearch.WordTrace]
  refine ⟨149880927703472657853646355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99920618468981771902430903 149880927703472657853646355)
  ·
    refine ⟨224821391555208986780469533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149880927703472657853646355 224821391555208986780469533)
    ·
      refine ⟨84308021833203370042676075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224821391555208986780469533 84308021833203370042676075)
      ·
        refine ⟨126462032749805055064014113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84308021833203370042676075 126462032749805055064014113)
        ·
          refine ⟨94846524562353791298010585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126462032749805055064014113 94846524562353791298010585)
          ·
            refine ⟨71134893421765343473507939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94846524562353791298010585 71134893421765343473507939)
            ·
              refine ⟨106702340132648015210261909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71134893421765343473507939 106702340132648015210261909)
              ·
                refine ⟨5001672193717875712981027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106702340132648015210261909 5001672193717875712981027)
                ·
                  refine ⟨7502508290576813569471541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001672193717875712981027 7502508290576813569471541)
                  ·
                    refine ⟨703360152241576272137957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7502508290576813569471541 703360152241576272137957)
                    ·
                      rfl

theorem cell23_4109367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_4109367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109367 prefixEnd_4109367 := by exact prefixLift 4109367
  have htrace : WordTrace (prefixWord ++ tailWord_4109367) baseStart_4109367 baseEnd_4109367 := by
    simpa [prefixWord, tailWord_4109367, baseEnd_4109367] using wordTrace_append hprefix tailTrace_4109367
  have hstable : (prefixWord ++ tailWord_4109367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109367).length < 2 ^ (prefixWord ++ tailWord_4109367).sum := by decide
  have hdescent : baseEnd_4109367 < baseStart_4109367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109381 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 1, 1, 3]
def baseStart_4109381 : Nat := 118140960795 + 4109381 * 2 ^ 59
def prefixEnd_4109381 : Nat := 4983230072969 + 3 ^ 40 * 4109381 * 2
def baseEnd_4109381 : Nat := 2110087645453891761638807

theorem tailTrace_4109381 : CollatzResearch.WordTrace tailWord_4109381 prefixEnd_4109381 2110087645453891761638807 := by
  unfold tailWord_4109381
  simp only [CollatzResearch.WordTrace]
  refine ⟨149881438325421938244655997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99920958883614625496437331 149881438325421938244655997)
  ·
    refine ⟨56205539372033226841745999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149881438325421938244655997 56205539372033226841745999)
    ·
      refine ⟨84308309058049840262618999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56205539372033226841745999 84308309058049840262618999)
      ·
        refine ⟨126462463587074760393928499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84308309058049840262618999 126462463587074760393928499)
        ·
          refine ⟨189693695380612140590892749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126462463587074760393928499 189693695380612140590892749)
          ·
            refine ⟨71135135767729552721584781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189693695380612140590892749 71135135767729552721584781)
            ·
              refine ⟨26675675912898582270594293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71135135767729552721584781 26675675912898582270594293)
              ·
                refine ⟨2500844616834242087868215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26675675912898582270594293 2500844616834242087868215)
                ·
                  refine ⟨3751266925251363131802323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2500844616834242087868215 3751266925251363131802323)
                  ·
                    refine ⟨5626900387877044697703485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3751266925251363131802323 5626900387877044697703485)
                    ·
                      refine ⟨2110087645453891761638807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5626900387877044697703485 2110087645453891761638807)
                      ·
                        rfl

theorem cell23_4109381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 1, 3].length) (baseStart_4109381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109381 prefixEnd_4109381 := by exact prefixLift 4109381
  have htrace : WordTrace (prefixWord ++ tailWord_4109381) baseStart_4109381 baseEnd_4109381 := by
    simpa [prefixWord, tailWord_4109381, baseEnd_4109381] using wordTrace_append hprefix tailTrace_4109381
  have hstable : (prefixWord ++ tailWord_4109381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109381).length < 2 ^ (prefixWord ++ tailWord_4109381).sum := by decide
  have hdescent : baseEnd_4109381 < baseStart_4109381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109407 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 5]
def baseStart_4109407 : Nat := 118140960795 + 4109407 * 2 ^ 59
def prefixEnd_4109407 : Nat := 4983230072969 + 3 ^ 40 * 4109407 * 2
def baseEnd_4109407 : Nat := 2110100995950908659913687

theorem tailTrace_4109407 : CollatzResearch.WordTrace tailWord_4109407 prefixEnd_4109407 2110100995950908659913687 := by
  unfold tailWord_4109407
  simp only [CollatzResearch.WordTrace]
  refine ⟨149882386623327744685102475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99921591082218496456734983 149882386623327744685102475)
  ·
    refine ⟨224823579934991617027653713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149882386623327744685102475 224823579934991617027653713)
    ·
      refine ⟨168617684951243712770740285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224823579934991617027653713 168617684951243712770740285)
      ·
        refine ⟨63231631856716392289027607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168617684951243712770740285 63231631856716392289027607)
        ·
          refine ⟨94847447785074588433541411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63231631856716392289027607 94847447785074588433541411)
          ·
            refine ⟨142271171677611882650312117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94847447785074588433541411 142271171677611882650312117)
            ·
              refine ⟨13337922344776113998466761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142271171677611882650312117 13337922344776113998466761)
              ·
                refine ⟨10003441758582085498850071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13337922344776113998466761 10003441758582085498850071)
                ·
                  refine ⟨15005162637873128248275107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003441758582085498850071 15005162637873128248275107)
                  ·
                    refine ⟨22507743956809692372412661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15005162637873128248275107 22507743956809692372412661)
                    ·
                      refine ⟨2110100995950908659913687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22507743956809692372412661 2110100995950908659913687)
                      ·
                        rfl

theorem cell23_4109407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_4109407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109407 prefixEnd_4109407 := by exact prefixLift 4109407
  have htrace : WordTrace (prefixWord ++ tailWord_4109407) baseStart_4109407 baseEnd_4109407 := by
    simpa [prefixWord, tailWord_4109407, baseEnd_4109407] using wordTrace_append hprefix tailTrace_4109407
  have hstable : (prefixWord ++ tailWord_4109407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109407).length < 2 ^ (prefixWord ++ tailWord_4109407).sum := by decide
  have hdescent : baseEnd_4109407 < baseStart_4109407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109417 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_4109417 : Nat := 118140960795 + 4109417 * 2 ^ 59
def prefixEnd_4109417 : Nat := 4983230072969 + 3 ^ 40 * 4109417 * 2
def baseEnd_4109417 : Nat := 2110106130757453620788641

theorem tailTrace_4109417 : CollatzResearch.WordTrace tailWord_4109417 prefixEnd_4109417 2110106130757453620788641 := by
  unfold tailWord_4109417
  simp only [CollatzResearch.WordTrace]
  refine ⟨149882751353291516392966505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99921834235527677595311003 149882751353291516392966505)
  ·
    refine ⟨112412063514968637294724879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149882751353291516392966505 112412063514968637294724879)
    ·
      refine ⟨168618095272452955942087319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112412063514968637294724879 168618095272452955942087319)
      ·
        refine ⟨252927142908679433913130979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168618095272452955942087319 252927142908679433913130979)
        ·
          refine ⟨379390714363019150869696469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252927142908679433913130979 379390714363019150869696469)
          ·
            refine ⟨8891969867883261348508511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 379390714363019150869696469 8891969867883261348508511)
            ·
              refine ⟨13337954801824892022762767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891969867883261348508511 13337954801824892022762767)
              ·
                refine ⟨20006932202737338034144151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13337954801824892022762767 20006932202737338034144151)
                ·
                  refine ⟨30010398304106007051216227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20006932202737338034144151 30010398304106007051216227)
                  ·
                    refine ⟨45015597456159010576824341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30010398304106007051216227 45015597456159010576824341)
                    ·
                      refine ⟨2110106130757453620788641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45015597456159010576824341 2110106130757453620788641)
                      ·
                        rfl

theorem cell23_4109417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_4109417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109417 prefixEnd_4109417 := by exact prefixLift 4109417
  have htrace : WordTrace (prefixWord ++ tailWord_4109417) baseStart_4109417 baseEnd_4109417 := by
    simpa [prefixWord, tailWord_4109417, baseEnd_4109417] using wordTrace_append hprefix tailTrace_4109417
  have hstable : (prefixWord ++ tailWord_4109417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109417).length < 2 ^ (prefixWord ++ tailWord_4109417).sum := by decide
  have hdescent : baseEnd_4109417 < baseStart_4109417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109421 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_4109421 : Nat := 118140960795 + 4109421 * 2 ^ 59
def prefixEnd_4109421 : Nat := 4983230072969 + 3 ^ 40 * 4109421 * 2
def baseEnd_4109421 : Nat := 2110108184680071605138623

theorem tailTrace_4109421 : CollatzResearch.WordTrace tailWord_4109421 prefixEnd_4109421 2110108184680071605138623 := by
  unfold tailWord_4109421
  simp only [CollatzResearch.WordTrace]
  refine ⟨149882897245277025076112117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99921931496851350050741411 149882897245277025076112117)
  ·
    refine ⟨14051521616744721100885511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149882897245277025076112117 14051521616744721100885511)
    ·
      refine ⟨21077282425117081651328267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14051521616744721100885511 21077282425117081651328267)
      ·
        refine ⟨31615923637675622476992401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21077282425117081651328267 31615923637675622476992401)
        ·
          refine ⟨23711942728256716857744301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31615923637675622476992401 23711942728256716857744301)
          ·
            refine ⟨8891978523096268821654113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23711942728256716857744301 8891978523096268821654113)
            ·
              refine ⟨6668983892322201616240585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8891978523096268821654113 6668983892322201616240585)
              ·
                refine ⟨5001737919241651212180439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6668983892322201616240585 5001737919241651212180439)
                ·
                  refine ⟨7502606878862476818270659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001737919241651212180439 7502606878862476818270659)
                  ·
                    refine ⟨11253910318293715227405989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7502606878862476818270659 11253910318293715227405989)
                    ·
                      refine ⟨2110108184680071605138623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11253910318293715227405989 2110108184680071605138623)
                      ·
                        rfl

theorem cell23_4109421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_4109421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109421 prefixEnd_4109421 := by exact prefixLift 4109421
  have htrace : WordTrace (prefixWord ++ tailWord_4109421) baseStart_4109421 baseEnd_4109421 := by
    simpa [prefixWord, tailWord_4109421, baseEnd_4109421] using wordTrace_append hprefix tailTrace_4109421
  have hstable : (prefixWord ++ tailWord_4109421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109421).length < 2 ^ (prefixWord ++ tailWord_4109421).sum := by decide
  have hdescent : baseEnd_4109421 < baseStart_4109421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109441 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_4109441 : Nat := 118140960795 + 4109441 * 2 ^ 59
def prefixEnd_4109441 : Nat := 4983230072969 + 3 ^ 40 * 4109441 * 2
def baseEnd_4109441 : Nat := 2110118454293161526888531

theorem tailTrace_4109441 : CollatzResearch.WordTrace tailWord_4109441 prefixEnd_4109441 2110118454293161526888531 := by
  unfold tailWord_4109441
  simp only [CollatzResearch.WordTrace]
  refine ⟨149883626705204568491840177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99922417803469712327893451 149883626705204568491840177)
  ·
    refine ⟨112412720028903426368880133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149883626705204568491840177 112412720028903426368880133)
    ·
      refine ⟨21077385005419392444165025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112412720028903426368880133 21077385005419392444165025)
      ·
        refine ⟨15808038754064544333123769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21077385005419392444165025 15808038754064544333123769)
        ·
          refine ⟨11856029065548408249842827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15808038754064544333123769 11856029065548408249842827)
          ·
            refine ⟨17784043598322612374764241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11856029065548408249842827 17784043598322612374764241)
            ·
              refine ⟨13338032698741959281073181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17784043598322612374764241 13338032698741959281073181)
              ·
                refine ⟨5001762262028234730402443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13338032698741959281073181 5001762262028234730402443)
                ·
                  refine ⟨7502643393042352095603665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5001762262028234730402443 7502643393042352095603665)
                  ·
                    refine ⟨5626982544781764071702749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502643393042352095603665 5626982544781764071702749)
                    ·
                      refine ⟨2110118454293161526888531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5626982544781764071702749 2110118454293161526888531)
                      ·
                        rfl

theorem cell23_4109441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_4109441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109441 prefixEnd_4109441 := by exact prefixLift 4109441
  have htrace : WordTrace (prefixWord ++ tailWord_4109441) baseStart_4109441 baseEnd_4109441 := by
    simpa [prefixWord, tailWord_4109441, baseEnd_4109441] using wordTrace_append hprefix tailTrace_4109441
  have hstable : (prefixWord ++ tailWord_4109441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109441).length < 2 ^ (prefixWord ++ tailWord_4109441).sum := by decide
  have hdescent : baseEnd_4109441 < baseStart_4109441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109505 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4109505 : Nat := 118140960795 + 4109505 * 2 ^ 59
def prefixEnd_4109505 : Nat := 4983230072969 + 3 ^ 40 * 4109505 * 2
def baseEnd_4109505 : Nat := 2110151317055049276488237

theorem tailTrace_4109505 : CollatzResearch.WordTrace tailWord_4109505 prefixEnd_4109505 2110151317055049276488237 := by
  unfold tailWord_4109505
  simp only [CollatzResearch.WordTrace]
  refine ⟨149885960976972707422169969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99923973984648471614779979 149885960976972707422169969)
  ·
    refine ⟨112414470732729530566627477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149885960976972707422169969 112414470732729530566627477)
    ·
      refine ⟨5269428315596696745310663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112414470732729530566627477 5269428315596696745310663)
      ·
        refine ⟨7904142473395045117965995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5269428315596696745310663 7904142473395045117965995)
        ·
          refine ⟨11856213710092567676948993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7904142473395045117965995 11856213710092567676948993)
          ·
            refine ⟨8892160282569425757711745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11856213710092567676948993 8892160282569425757711745)
            ·
              refine ⟨6669120211927069318283809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892160282569425757711745 6669120211927069318283809)
              ·
                refine ⟨5001840158945301988712857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669120211927069318283809 5001840158945301988712857)
                ·
                  refine ⟨3751380119208976491534643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001840158945301988712857 3751380119208976491534643)
                  ·
                    refine ⟨5627070178813464737301965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3751380119208976491534643 5627070178813464737301965)
                    ·
                      refine ⟨2110151317055049276488237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627070178813464737301965 2110151317055049276488237)
                      ·
                        rfl

theorem cell23_4109505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4109505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109505 prefixEnd_4109505 := by exact prefixLift 4109505
  have htrace : WordTrace (prefixWord ++ tailWord_4109505) baseStart_4109505 baseEnd_4109505 := by
    simpa [prefixWord, tailWord_4109505, baseEnd_4109505] using wordTrace_append hprefix tailTrace_4109505
  have hstable : (prefixWord ++ tailWord_4109505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109505).length < 2 ^ (prefixWord ++ tailWord_4109505).sum := by decide
  have hdescent : baseEnd_4109505 < baseStart_4109505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109511 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_4109511 : Nat := 118140960795 + 4109511 * 2 ^ 59
def prefixEnd_4109511 : Nat := 4983230072969 + 3 ^ 40 * 4109511 * 2
def baseEnd_4109511 : Nat := 2110154397938976253013209

theorem tailTrace_4109511 : CollatzResearch.WordTrace tailWord_4109511 prefixEnd_4109511 2110154397938976253013209 := by
  unfold tailWord_4109511
  simp only [CollatzResearch.WordTrace]
  refine ⟨149886179814950970446888387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99924119876633980297925591 149886179814950970446888387)
  ·
    refine ⟨224829269722426455670332581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149886179814950970446888387 224829269722426455670332581)
    ·
      refine ⟨42155488072954960438187359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224829269722426455670332581 42155488072954960438187359)
      ·
        refine ⟨63233232109432440657281039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42155488072954960438187359 63233232109432440657281039)
        ·
          refine ⟨94849848164148660985921559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63233232109432440657281039 94849848164148660985921559)
          ·
            refine ⟨142274772246222991478882339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94849848164148660985921559 142274772246222991478882339)
            ·
              refine ⟨213412158369334487218323509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142274772246222991478882339 213412158369334487218323509)
              ·
                refine ⟨20007389847125108176717829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213412158369334487218323509 20007389847125108176717829)
                ·
                  refine ⟨3751385596335957783134593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20007389847125108176717829 3751385596335957783134593)
                  ·
                    refine ⟨2813539197251968337350945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3751385596335957783134593 2813539197251968337350945)
                    ·
                      refine ⟨2110154397938976253013209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813539197251968337350945 2110154397938976253013209)
                      ·
                        rfl

theorem cell23_4109511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_4109511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109511 prefixEnd_4109511 := by exact prefixLift 4109511
  have htrace : WordTrace (prefixWord ++ tailWord_4109511) baseStart_4109511 baseEnd_4109511 := by
    simpa [prefixWord, tailWord_4109511, baseEnd_4109511] using wordTrace_append hprefix tailTrace_4109511
  have hstable : (prefixWord ++ tailWord_4109511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109511).length < 2 ^ (prefixWord ++ tailWord_4109511).sum := by decide
  have hdescent : baseEnd_4109511 < baseStart_4109511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109514 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_4109514 : Nat := 118140960795 + 4109514 * 2 ^ 59
def prefixEnd_4109514 : Nat := 4983230072969 + 3 ^ 40 * 4109514 * 2
def baseEnd_4109514 : Nat := 2110155938380939741275695

theorem tailTrace_4109514 : CollatzResearch.WordTrace tailWord_4109514 prefixEnd_4109514 2110155938380939741275695 := by
  unfold tailWord_4109514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471572308485025489811899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99924192822626734639498397 37471572308485025489811899)
  ·
    refine ⟨56207358462727538234717849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37471572308485025489811899 56207358462727538234717849)
    ·
      refine ⟨42155518847045653676038387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56207358462727538234717849 42155518847045653676038387)
      ·
        refine ⟨63233278270568480514057581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42155518847045653676038387 63233278270568480514057581)
        ·
          refine ⟨23712479351463180192771593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63233278270568480514057581 23712479351463180192771593)
          ·
            refine ⟨17784359513597385144578695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23712479351463180192771593 17784359513597385144578695)
            ·
              refine ⟨26676539270396077716868043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17784359513597385144578695 26676539270396077716868043)
              ·
                refine ⟨40014808905594116575302065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26676539270396077716868043 40014808905594116575302065)
                ·
                  refine ⟨30011106679195587431476549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40014808905594116575302065 30011106679195587431476549)
                  ·
                    refine ⟨5627082502349172643401853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30011106679195587431476549 5627082502349172643401853)
                    ·
                      refine ⟨2110155938380939741275695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627082502349172643401853 2110155938380939741275695)
                      ·
                        rfl

theorem cell23_4109514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_4109514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109514 prefixEnd_4109514 := by exact prefixLift 4109514
  have htrace : WordTrace (prefixWord ++ tailWord_4109514) baseStart_4109514 baseEnd_4109514 := by
    simpa [prefixWord, tailWord_4109514, baseEnd_4109514] using wordTrace_append hprefix tailTrace_4109514
  have hstable : (prefixWord ++ tailWord_4109514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109514).length < 2 ^ (prefixWord ++ tailWord_4109514).sum := by decide
  have hdescent : baseEnd_4109514 < baseStart_4109514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109528 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 1, 4, 2]
def baseStart_4109528 : Nat := 118140960795 + 4109528 * 2 ^ 59
def prefixEnd_4109528 : Nat := 4983230072969 + 3 ^ 40 * 4109528 * 2
def baseEnd_4109528 : Nat := 2110163127110102686500631

theorem tailTrace_4109528 : CollatzResearch.WordTrace tailWord_4109528 prefixEnd_4109528 2110163127110102686500631 := by
  unfold tailWord_4109528
  simp only [CollatzResearch.WordTrace]
  refine ⟨74943399927944691175128619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99924533237259588233504825 74943399927944691175128619)
  ·
    refine ⟨112415099891917036762692929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74943399927944691175128619 112415099891917036762692929)
    ·
      refine ⟨84311324918937777572019697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112415099891917036762692929 84311324918937777572019697)
      ·
        refine ⟨63233493689203333179014773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84311324918937777572019697 63233493689203333179014773)
        ·
          refine ⟨5928140033362812485532635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63233493689203333179014773 5928140033362812485532635)
          ·
            refine ⟨8892210050044218728298953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5928140033362812485532635 8892210050044218728298953)
            ·
              refine ⟨6669157537533164046224215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892210050044218728298953 6669157537533164046224215)
              ·
                refine ⟨10003736306299746069336323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669157537533164046224215 10003736306299746069336323)
                ·
                  refine ⟨15005604459449619104004485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10003736306299746069336323 15005604459449619104004485)
                  ·
                    refine ⟨2813550836146803582000841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15005604459449619104004485 2813550836146803582000841)
                    ·
                      refine ⟨2110163127110102686500631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813550836146803582000841 2110163127110102686500631)
                      ·
                        rfl

theorem cell23_4109528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_4109528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109528 prefixEnd_4109528 := by exact prefixLift 4109528
  have htrace : WordTrace (prefixWord ++ tailWord_4109528) baseStart_4109528 baseEnd_4109528 := by
    simpa [prefixWord, tailWord_4109528, baseEnd_4109528] using wordTrace_append hprefix tailTrace_4109528
  have hstable : (prefixWord ++ tailWord_4109528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109528).length < 2 ^ (prefixWord ++ tailWord_4109528).sum := by decide
  have hdescent : baseEnd_4109528 < baseStart_4109528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109544 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4109544 : Nat := 118140960795 + 4109544 * 2 ^ 59
def prefixEnd_4109544 : Nat := 4983230072969 + 3 ^ 40 * 4109544 * 2
def baseEnd_4109544 : Nat := 2110171342800574623900557

theorem tailTrace_4109544 : CollatzResearch.WordTrace tailWord_4109544 prefixEnd_4109544 2110171342800574623900557 := by
  unfold tailWord_4109544
  simp only [CollatzResearch.WordTrace]
  refine ⟨74943691711915708541419843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99924922282554278055226457 74943691711915708541419843)
  ·
    refine ⟨112415537567873562812129765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74943691711915708541419843 112415537567873562812129765)
    ·
      refine ⟨21077913293976293027274331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112415537567873562812129765 21077913293976293027274331)
      ·
        refine ⟨31616869940964439540911497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21077913293976293027274331 31616869940964439540911497)
        ·
          refine ⟨23712652455723329655683623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31616869940964439540911497 23712652455723329655683623)
          ·
            refine ⟨35568978683584994483525435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23712652455723329655683623 35568978683584994483525435)
            ·
              refine ⟨53353468025377491725288153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35568978683584994483525435 53353468025377491725288153)
              ·
                refine ⟨40015101019033118793966115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53353468025377491725288153 40015101019033118793966115)
                ·
                  refine ⟨60022651528549678190949173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40015101019033118793966115 60022651528549678190949173)
                  ·
                    refine ⟨5627123580801532330401485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60022651528549678190949173 5627123580801532330401485)
                    ·
                      refine ⟨2110171342800574623900557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627123580801532330401485 2110171342800574623900557)
                      ·
                        rfl

theorem cell23_4109544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4109544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109544 prefixEnd_4109544 := by exact prefixLift 4109544
  have htrace : WordTrace (prefixWord ++ tailWord_4109544) baseStart_4109544 baseEnd_4109544 := by
    simpa [prefixWord, tailWord_4109544, baseEnd_4109544] using wordTrace_append hprefix tailTrace_4109544
  have hstable : (prefixWord ++ tailWord_4109544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109544).length < 2 ^ (prefixWord ++ tailWord_4109544).sum := by decide
  have hdescent : baseEnd_4109544 < baseStart_4109544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109556 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4109556 : Nat := 118140960795 + 4109556 * 2 ^ 59
def prefixEnd_4109556 : Nat := 4983230072969 + 3 ^ 40 * 4109556 * 2
def baseEnd_4109556 : Nat := 2110177504568428576950503

theorem tailTrace_4109556 : CollatzResearch.WordTrace tailWord_4109556 prefixEnd_4109556 2110177504568428576950503 := by
  unfold tailWord_4109556
  simp only [CollatzResearch.WordTrace]
  refine ⟨74943910549893971566138261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99925214066525295421517681 74943910549893971566138261)
  ·
    refine ⟨3512995807026279917162731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74943910549893971566138261 3512995807026279917162731)
    ·
      refine ⟨5269493710539419875744097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3512995807026279917162731 5269493710539419875744097)
      ·
        refine ⟨3952120282904564906808073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5269493710539419875744097 3952120282904564906808073)
        ·
          refine ⟨2964090212178423680106055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3952120282904564906808073 2964090212178423680106055)
          ·
            refine ⟨4446135318267635520159083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964090212178423680106055 4446135318267635520159083)
            ·
              refine ⟨6669202977401453280238625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446135318267635520159083 6669202977401453280238625)
              ·
                refine ⟨5001902233051089960178969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6669202977401453280238625 5001902233051089960178969)
                ·
                  refine ⟨3751426674788317470134227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5001902233051089960178969 3751426674788317470134227)
                  ·
                    refine ⟨5627140012182476205201341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3751426674788317470134227 5627140012182476205201341)
                    ·
                      refine ⟨2110177504568428576950503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627140012182476205201341 2110177504568428576950503)
                      ·
                        rfl

theorem cell23_4109556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4109556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109556 prefixEnd_4109556 := by exact prefixLift 4109556
  have htrace : WordTrace (prefixWord ++ tailWord_4109556) baseStart_4109556 baseEnd_4109556 := by
    simpa [prefixWord, tailWord_4109556, baseEnd_4109556] using wordTrace_append hprefix tailTrace_4109556
  have hstable : (prefixWord ++ tailWord_4109556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109556).length < 2 ^ (prefixWord ++ tailWord_4109556).sum := by decide
  have hdescent : baseEnd_4109556 < baseStart_4109556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109621 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_4109621 : Nat := 118140960795 + 4109621 * 2 ^ 59
def prefixEnd_4109621 : Nat := 4983230072969 + 3 ^ 40 * 4109621 * 2
def baseEnd_4109621 : Nat := 2110210880810970822637703

theorem tailTrace_4109621 : CollatzResearch.WordTrace tailWord_4109621 prefixEnd_4109621 2110210880810970822637703 := by
  unfold tailWord_4109621
  simp only [CollatzResearch.WordTrace]
  refine ⟨149890191844552459233392717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99926794563034972822261811 149890191844552459233392717)
  ·
    refine ⟨56208821941707172212522269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149890191844552459233392717 56208821941707172212522269)
    ·
      refine ⟨21078308228140189579695851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56208821941707172212522269 21078308228140189579695851)
      ·
        refine ⟨31617462342210284369543777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21078308228140189579695851 31617462342210284369543777)
        ·
          refine ⟨23713096756657713277157833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31617462342210284369543777 23713096756657713277157833)
          ·
            refine ⟨17784822567493284957868375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23713096756657713277157833 17784822567493284957868375)
            ·
              refine ⟨26677233851239927436802563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17784822567493284957868375 26677233851239927436802563)
              ·
                refine ⟨40015850776859891155203845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26677233851239927436802563 40015850776859891155203845)
                ·
                  refine ⟨7502972020661229591600721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40015850776859891155203845 7502972020661229591600721)
                  ·
                    refine ⟨5627229015495922193700541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7502972020661229591600721 5627229015495922193700541)
                    ·
                      refine ⟨2110210880810970822637703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627229015495922193700541 2110210880810970822637703)
                      ·
                        rfl

theorem cell23_4109621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_4109621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109621 prefixEnd_4109621 := by exact prefixLift 4109621
  have htrace : WordTrace (prefixWord ++ tailWord_4109621) baseStart_4109621 baseEnd_4109621 := by
    simpa [prefixWord, tailWord_4109621, baseEnd_4109621] using wordTrace_append hprefix tailTrace_4109621
  have hstable : (prefixWord ++ tailWord_4109621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109621).length < 2 ^ (prefixWord ++ tailWord_4109621).sum := by decide
  have hdescent : baseEnd_4109621 < baseStart_4109621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109624 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 6]
def baseStart_4109624 : Nat := 118140960795 + 4109624 * 2 ^ 59
def prefixEnd_4109624 : Nat := 4983230072969 + 3 ^ 40 * 4109624 * 2
def baseEnd_4109624 : Nat := 234468046805881590100021

theorem tailTrace_4109624 : CollatzResearch.WordTrace tailWord_4109624 prefixEnd_4109624 234468046805881590100021 := by
  unfold tailWord_4109624
  simp only [CollatzResearch.WordTrace]
  refine ⟨74945150631770795372875963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99926867509027727163834617 74945150631770795372875963)
  ·
    refine ⟨112417725947656193059313945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74945150631770795372875963 112417725947656193059313945)
    ·
      refine ⟨84313294460742144794485459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112417725947656193059313945 84313294460742144794485459)
      ·
        refine ⟨126469941691113217191728189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84313294460742144794485459 126469941691113217191728189)
        ·
          refine ⟨47426228134167456446898071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126469941691113217191728189 47426228134167456446898071)
          ·
            refine ⟨71139342201251184670347107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47426228134167456446898071 71139342201251184670347107)
            ·
              refine ⟨106709013301876777005520661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71139342201251184670347107 106709013301876777005520661)
              ·
                refine ⟨5001984998525473922133781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106709013301876777005520661 5001984998525473922133781)
                ·
                  refine ⟨234468046805881590100021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5001984998525473922133781 234468046805881590100021)
                  ·
                    rfl

theorem cell23_4109624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 6].length) (baseStart_4109624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109624 prefixEnd_4109624 := by exact prefixLift 4109624
  have htrace : WordTrace (prefixWord ++ tailWord_4109624) baseStart_4109624 baseEnd_4109624 := by
    simpa [prefixWord, tailWord_4109624, baseEnd_4109624] using wordTrace_append hprefix tailTrace_4109624
  have hstable : (prefixWord ++ tailWord_4109624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109624).length < 2 ^ (prefixWord ++ tailWord_4109624).sum := by decide
  have hdescent : baseEnd_4109624 < baseStart_4109624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109628 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_4109628 : Nat := 118140960795 + 4109628 * 2 ^ 59
def prefixEnd_4109628 : Nat := 4983230072969 + 3 ^ 40 * 4109628 * 2
def baseEnd_4109628 : Nat := 703404825058517431750057

theorem tailTrace_4109628 : CollatzResearch.WordTrace tailWord_4109628 prefixEnd_4109628 703404825058517431750057 := by
  unfold tailWord_4109628
  simp only [CollatzResearch.WordTrace]
  refine ⟨74945223577763549714448769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99926964770351399619265025 74945223577763549714448769)
  ·
    refine ⟨56208917683322662285836577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74945223577763549714448769 56208917683322662285836577)
    ·
      refine ⟨42156688262491996714377433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56208917683322662285836577 42156688262491996714377433)
      ·
        refine ⟨31617516196868997535783075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42156688262491996714377433 31617516196868997535783075)
        ·
          refine ⟨47426274295303496303674613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31617516196868997535783075 47426274295303496303674613)
          ·
            refine ⟨4446213215184702778469495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47426274295303496303674613 4446213215184702778469495)
            ·
              refine ⟨6669319822777054167704243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446213215184702778469495 6669319822777054167704243)
              ·
                refine ⟨10003979734165581251556365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669319822777054167704243 10003979734165581251556365)
                ·
                  refine ⟨3751492400312092969333637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10003979734165581251556365 3751492400312092969333637)
                  ·
                    refine ⟨703404825058517431750057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3751492400312092969333637 703404825058517431750057)
                    ·
                      rfl

theorem cell23_4109628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_4109628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109628 prefixEnd_4109628 := by exact prefixLift 4109628
  have htrace : WordTrace (prefixWord ++ tailWord_4109628) baseStart_4109628 baseEnd_4109628 := by
    simpa [prefixWord, tailWord_4109628, baseEnd_4109628] using wordTrace_append hprefix tailTrace_4109628
  have hstable : (prefixWord ++ tailWord_4109628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109628).length < 2 ^ (prefixWord ++ tailWord_4109628).sum := by decide
  have hdescent : baseEnd_4109628 < baseStart_4109628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109641 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 6]
def baseStart_4109641 : Nat := 118140960795 + 4109641 * 2 ^ 59
def prefixEnd_4109641 : Nat := 4983230072969 + 3 ^ 40 * 4109641 * 2
def baseEnd_4109641 : Nat := 234469016713784527154179

theorem tailTrace_4109641 : CollatzResearch.WordTrace tailWord_4109641 prefixEnd_4109641 234469016713784527154179 := by
  unfold tailWord_4109641
  simp only [CollatzResearch.WordTrace]
  refine ⟨149890921304480002649120777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99927280869653335099413851 149890921304480002649120777)
  ·
    refine ⟨112418190978360001986840583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149890921304480002649120777 112418190978360001986840583)
    ·
      refine ⟨168627286467540002980260875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112418190978360001986840583 168627286467540002980260875)
      ·
        refine ⟨252940929701310004470391313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168627286467540002980260875 252940929701310004470391313)
        ·
          refine ⟨189705697275982503352793485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252940929701310004470391313 189705697275982503352793485)
          ·
            refine ⟨71139636478493438757297557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189705697275982503352793485 71139636478493438757297557)
            ·
              refine ⟨3334670459929379941748323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71139636478493438757297557 3334670459929379941748323)
              ·
                refine ⟨5002005689894069912622485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334670459929379941748323 5002005689894069912622485)
                ·
                  refine ⟨234469016713784527154179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5002005689894069912622485 234469016713784527154179)
                  ·
                    rfl

theorem cell23_4109641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 6].length) (baseStart_4109641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109641 prefixEnd_4109641 := by exact prefixLift 4109641
  have htrace : WordTrace (prefixWord ++ tailWord_4109641) baseStart_4109641 baseEnd_4109641 := by
    simpa [prefixWord, tailWord_4109641, baseEnd_4109641] using wordTrace_append hprefix tailTrace_4109641
  have hstable : (prefixWord ++ tailWord_4109641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109641).length < 2 ^ (prefixWord ++ tailWord_4109641).sum := by decide
  have hdescent : baseEnd_4109641 < baseStart_4109641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109651 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 3]
def baseStart_4109651 : Nat := 118140960795 + 4109651 * 2 ^ 59
def prefixEnd_4109651 : Nat := 4983230072969 + 3 ^ 40 * 4109651 * 2
def baseEnd_4109651 : Nat := 2110226285230605705262565

theorem tailTrace_4109651 : CollatzResearch.WordTrace tailWord_4109651 prefixEnd_4109651 2110226285230605705262565 := by
  unfold tailWord_4109651
  simp only [CollatzResearch.WordTrace]
  refine ⟨149891286034443774356984807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99927524022962516237989871 149891286034443774356984807)
  ·
    refine ⟨224836929051665661535477211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149891286034443774356984807 224836929051665661535477211)
    ·
      refine ⟨337255393577498492303215817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224836929051665661535477211 337255393577498492303215817)
      ·
        refine ⟨252941545183123869227411863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337255393577498492303215817 252941545183123869227411863)
        ·
          refine ⟨379412317774685803841117795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252941545183123869227411863 379412317774685803841117795)
          ·
            refine ⟨569118476662028705761676693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379412317774685803841117795 569118476662028705761676693)
            ·
              refine ⟨26677428593532595582578595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 569118476662028705761676693 26677428593532595582578595)
              ·
                refine ⟨40016142890298893373867893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26677428593532595582578595 40016142890298893373867893)
                ·
                  refine ⟨3751513395965521253800115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40016142890298893373867893 3751513395965521253800115)
                  ·
                    refine ⟨5627270093948281880700173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3751513395965521253800115 5627270093948281880700173)
                    ·
                      refine ⟨2110226285230605705262565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627270093948281880700173 2110226285230605705262565)
                      ·
                        rfl

theorem cell23_4109651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_4109651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109651 prefixEnd_4109651 := by exact prefixLift 4109651
  have htrace : WordTrace (prefixWord ++ tailWord_4109651) baseStart_4109651 baseEnd_4109651 := by
    simpa [prefixWord, tailWord_4109651, baseEnd_4109651] using wordTrace_append hprefix tailTrace_4109651
  have hstable : (prefixWord ++ tailWord_4109651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109651).length < 2 ^ (prefixWord ++ tailWord_4109651).sum := by decide
  have hdescent : baseEnd_4109651 < baseStart_4109651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109721 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_4109721 : Nat := 118140960795 + 4109721 * 2 ^ 59
def prefixEnd_4109721 : Nat := 4983230072969 + 3 ^ 40 * 4109721 * 2
def baseEnd_4109721 : Nat := 2110262228876420431387243

theorem tailTrace_4109721 : CollatzResearch.WordTrace tailWord_4109721 prefixEnd_4109721 2110262228876420431387243 := by
  unfold tailWord_4109721
  simp only [CollatzResearch.WordTrace]
  refine ⟨149893839144190176312033017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99929226096126784208022011 149893839144190176312033017)
  ·
    refine ⟨112420379358142632234024763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149893839144190176312033017 112420379358142632234024763)
    ·
      refine ⟨168630569037213948351037145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112420379358142632234024763 168630569037213948351037145)
      ·
        refine ⟨126472926777910461263277859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168630569037213948351037145 126472926777910461263277859)
        ·
          refine ⟨189709390166865691894916789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126472926777910461263277859 189709390166865691894916789)
          ·
            refine ⟨17785255328143658615148449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189709390166865691894916789 17785255328143658615148449)
            ·
              refine ⟨13338941496107743961361337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17785255328143658615148449 13338941496107743961361337)
              ·
                refine ⟨10004206122080807971021003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13338941496107743961361337 10004206122080807971021003)
                ·
                  refine ⟨15006309183121211956531505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10004206122080807971021003 15006309183121211956531505)
                  ·
                    refine ⟨11254731887340908967398629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15006309183121211956531505 11254731887340908967398629)
                    ·
                      refine ⟨2110262228876420431387243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11254731887340908967398629 2110262228876420431387243)
                      ·
                        rfl

theorem cell23_4109721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_4109721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109721 prefixEnd_4109721 := by exact prefixLift 4109721
  have htrace : WordTrace (prefixWord ++ tailWord_4109721) baseStart_4109721 baseEnd_4109721 := by
    simpa [prefixWord, tailWord_4109721, baseEnd_4109721] using wordTrace_append hprefix tailTrace_4109721
  have hstable : (prefixWord ++ tailWord_4109721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109721).length < 2 ^ (prefixWord ++ tailWord_4109721).sum := by decide
  have hdescent : baseEnd_4109721 < baseStart_4109721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109725 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_4109725 : Nat := 118140960795 + 4109725 * 2 ^ 59
def prefixEnd_4109725 : Nat := 4983230072969 + 3 ^ 40 * 4109725 * 2
def baseEnd_4109725 : Nat := 2110264282799038415737225

theorem tailTrace_4109725 : CollatzResearch.WordTrace tailWord_4109725 prefixEnd_4109725 2110264282799038415737225 := by
  unfold tailWord_4109725
  simp only [CollatzResearch.WordTrace]
  refine ⟨149893985036175684995178629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99929323357450456663452419 149893985036175684995178629)
  ·
    refine ⟨28105122194282940936595993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149893985036175684995178629 28105122194282940936595993)
    ·
      refine ⟨21078841645712205702446995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28105122194282940936595993 21078841645712205702446995)
      ·
        refine ⟨31618262468568308553670493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21078841645712205702446995 31618262468568308553670493)
        ·
          refine ⟨11856848425713115707626435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31618262468568308553670493 11856848425713115707626435)
          ·
            refine ⟨17785272638569673561439653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11856848425713115707626435 17785272638569673561439653)
            ·
              refine ⟨3334738619731813792769935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17785272638569673561439653 3334738619731813792769935)
              ·
                refine ⟨5002107929597720689154903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3334738619731813792769935 5002107929597720689154903)
                ·
                  refine ⟨7503161894396581033732355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002107929597720689154903 7503161894396581033732355)
                  ·
                    refine ⟨11254742841594871550598533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7503161894396581033732355 11254742841594871550598533)
                    ·
                      refine ⟨2110264282799038415737225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11254742841594871550598533 2110264282799038415737225)
                      ·
                        rfl

theorem cell23_4109725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_4109725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109725 prefixEnd_4109725 := by exact prefixLift 4109725
  have htrace : WordTrace (prefixWord ++ tailWord_4109725) baseStart_4109725 baseEnd_4109725 := by
    simpa [prefixWord, tailWord_4109725, baseEnd_4109725] using wordTrace_append hprefix tailTrace_4109725
  have hstable : (prefixWord ++ tailWord_4109725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109725).length < 2 ^ (prefixWord ++ tailWord_4109725).sum := by decide
  have hdescent : baseEnd_4109725 < baseStart_4109725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109728 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3]
def baseStart_4109728 : Nat := 118140960795 + 4109728 * 2 ^ 59
def prefixEnd_4109728 : Nat := 4983230072969 + 3 ^ 40 * 4109728 * 2
def baseEnd_4109728 : Nat := 2110265823241001903999711

theorem tailTrace_4109728 : CollatzResearch.WordTrace tailWord_4109728 prefixEnd_4109728 2110265823241001903999711 := by
  unfold tailWord_4109728
  simp only [CollatzResearch.WordTrace]
  refine ⟨74947047227582408253768919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99929396303443211005025225 74947047227582408253768919)
  ·
    refine ⟨112420570841373612380653379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74947047227582408253768919 112420570841373612380653379)
    ·
      refine ⟨168630856262060418570980069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112420570841373612380653379 168630856262060418570980069)
      ·
        refine ⟨31618285549136328482058763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168630856262060418570980069 31618285549136328482058763)
        ·
          refine ⟨47427428323704492723088145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31618285549136328482058763 47427428323704492723088145)
          ·
            refine ⟨35570571242778369542316109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47427428323704492723088145 35570571242778369542316109)
            ·
              refine ⟨13338964216041888578368541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35570571242778369542316109 13338964216041888578368541)
              ·
                refine ⟨5002111581015708216888203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13338964216041888578368541 5002111581015708216888203)
                ·
                  refine ⟨7503167371523562325332305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002111581015708216888203 7503167371523562325332305)
                  ·
                    refine ⟨5627375528642671743999229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7503167371523562325332305 5627375528642671743999229)
                    ·
                      refine ⟨2110265823241001903999711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627375528642671743999229 2110265823241001903999711)
                      ·
                        rfl

theorem cell23_4109728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_4109728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109728 prefixEnd_4109728 := by exact prefixLift 4109728
  have htrace : WordTrace (prefixWord ++ tailWord_4109728) baseStart_4109728 baseEnd_4109728 := by
    simpa [prefixWord, tailWord_4109728, baseEnd_4109728] using wordTrace_append hprefix tailTrace_4109728
  have hstable : (prefixWord ++ tailWord_4109728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109728).length < 2 ^ (prefixWord ++ tailWord_4109728).sum := by decide
  have hdescent : baseEnd_4109728 < baseStart_4109728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109744 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_4109744 : Nat := 118140960795 + 4109744 * 2 ^ 59
def prefixEnd_4109744 : Nat := 4983230072969 + 3 ^ 40 * 4109744 * 2
def baseEnd_4109744 : Nat := 703424679643824613799879

theorem tailTrace_4109744 : CollatzResearch.WordTrace tailWord_4109744 prefixEnd_4109744 703424679643824613799879 := by
  unfold tailWord_4109744
  simp only [CollatzResearch.WordTrace]
  refine ⟨74947339011553425620060143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99929785348737900826746857 74947339011553425620060143)
  ·
    refine ⟨112421008517330138430090215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74947339011553425620060143 112421008517330138430090215)
    ·
      refine ⟨168631512775995207645135323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112421008517330138430090215 168631512775995207645135323)
      ·
        refine ⟨252947269163992811467702985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168631512775995207645135323 252947269163992811467702985)
        ·
          refine ⟨189710451872994608600777239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252947269163992811467702985 189710451872994608600777239)
          ·
            refine ⟨284565677809491912901165859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189710451872994608600777239 284565677809491912901165859)
            ·
              refine ⟨426848516714237869351748789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284565677809491912901165859 426848516714237869351748789)
              ·
                refine ⟨40017048441959800251726449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426848516714237869351748789 40017048441959800251726449)
                ·
                  refine ⟨30012786331469850188794837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40017048441959800251726449 30012786331469850188794837)
                  ·
                    refine ⟨703424679643824613799879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30012786331469850188794837 703424679643824613799879)
                    ·
                      rfl

theorem cell23_4109744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_4109744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109744 prefixEnd_4109744 := by exact prefixLift 4109744
  have htrace : WordTrace (prefixWord ++ tailWord_4109744) baseStart_4109744 baseEnd_4109744 := by
    simpa [prefixWord, tailWord_4109744, baseEnd_4109744] using wordTrace_append hprefix tailTrace_4109744
  have hstable : (prefixWord ++ tailWord_4109744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109744).length < 2 ^ (prefixWord ++ tailWord_4109744).sum := by decide
  have hdescent : baseEnd_4109744 < baseStart_4109744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109785 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 1, 3, 2]
def baseStart_4109785 : Nat := 118140960795 + 4109785 * 2 ^ 59
def prefixEnd_4109785 : Nat := 4983230072969 + 3 ^ 40 * 4109785 * 2
def baseEnd_4109785 : Nat := 2110295091638308180986949

theorem tailTrace_4109785 : CollatzResearch.WordTrace tailWord_4109785 prefixEnd_4109785 2110295091638308180986949 := by
  unfold tailWord_4109785
  simp only [CollatzResearch.WordTrace]
  refine ⟨149896173415958315242362809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99930782277305543494908539 149896173415958315242362809)
  ·
    refine ⟨112422130061968736431772107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149896173415958315242362809 112422130061968736431772107)
    ·
      refine ⟨168633195092953104647658161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112422130061968736431772107 168633195092953104647658161)
      ·
        refine ⟨126474896319714828485743621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168633195092953104647658161 126474896319714828485743621)
        ·
          refine ⟨23714043059946530341076929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126474896319714828485743621 23714043059946530341076929)
          ·
            refine ⟨17785532294959897755807697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23714043059946530341076929 17785532294959897755807697)
            ·
              refine ⟨13339149221219923316855773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17785532294959897755807697 13339149221219923316855773)
              ·
                refine ⟨5002180957957471243820915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13339149221219923316855773 5002180957957471243820915)
                ·
                  refine ⟨7503271436936206865731373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5002180957957471243820915 7503271436936206865731373)
                  ·
                    refine ⟨2813726788851077574649265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7503271436936206865731373 2813726788851077574649265)
                    ·
                      refine ⟨2110295091638308180986949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813726788851077574649265 2110295091638308180986949)
                      ·
                        rfl

theorem cell23_4109785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_4109785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109785 prefixEnd_4109785 := by exact prefixLift 4109785
  have htrace : WordTrace (prefixWord ++ tailWord_4109785) baseStart_4109785 baseEnd_4109785 := by
    simpa [prefixWord, tailWord_4109785, baseEnd_4109785] using wordTrace_append hprefix tailTrace_4109785
  have hstable : (prefixWord ++ tailWord_4109785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109785).length < 2 ^ (prefixWord ++ tailWord_4109785).sum := by decide
  have hdescent : baseEnd_4109785 < baseStart_4109785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109855 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 5]
def baseStart_4109855 : Nat := 118140960795 + 4109855 * 2 ^ 59
def prefixEnd_4109855 : Nat := 4983230072969 + 3 ^ 40 * 4109855 * 2
def baseEnd_4109855 : Nat := 234481226142680323012403

theorem tailTrace_4109855 : CollatzResearch.WordTrace tailWord_4109855 prefixEnd_4109855 234481226142680323012403 := by
  unfold tailWord_4109855
  simp only [CollatzResearch.WordTrace]
  refine ⟨149898726525704717197411019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99932484350469811464940679 149898726525704717197411019)
  ·
    refine ⟨224848089788557075796116529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149898726525704717197411019 224848089788557075796116529)
    ·
      refine ⟨168636067341417806847087397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224848089788557075796116529 168636067341417806847087397)
      ·
        refine ⟨31619262626515838783828887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168636067341417806847087397 31619262626515838783828887)
        ·
          refine ⟨47428893939773758175743331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31619262626515838783828887 47428893939773758175743331)
          ·
            refine ⟨71143340909660637263614997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47428893939773758175743331 71143340909660637263614997)
            ·
              refine ⟨3334844105140342371731953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71143340909660637263614997 3334844105140342371731953)
              ·
                refine ⟨2501133078855256778798965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334844105140342371731953 2501133078855256778798965)
                ·
                  refine ⟨234481226142680323012403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2501133078855256778798965 234481226142680323012403)
                  ·
                    rfl

theorem cell23_4109855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 5].length) (baseStart_4109855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109855 prefixEnd_4109855 := by exact prefixLift 4109855
  have htrace : WordTrace (prefixWord ++ tailWord_4109855) baseStart_4109855 baseEnd_4109855 := by
    simpa [prefixWord, tailWord_4109855, baseEnd_4109855] using wordTrace_append hprefix tailTrace_4109855
  have hstable : (prefixWord ++ tailWord_4109855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109855).length < 2 ^ (prefixWord ++ tailWord_4109855).sum := by decide
  have hdescent : baseEnd_4109855 < baseStart_4109855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109888 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 6, 2]
def baseStart_4109888 : Nat := 118140960795 + 4109888 * 2 ^ 59
def prefixEnd_4109888 : Nat := 4983230072969 + 3 ^ 40 * 4109888 * 2
def baseEnd_4109888 : Nat := 2110347980145721277998975

theorem tailTrace_4109888 : CollatzResearch.WordTrace tailWord_4109888 prefixEnd_4109888 2110347980145721277998975 := by
  unfold tailWord_4109888
  simp only [CollatzResearch.WordTrace]
  refine ⟨74949965067292581916681159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99933286756390109222241545 74949965067292581916681159)
  ·
    refine ⟨112424947600938872875021739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74949965067292581916681159 112424947600938872875021739)
    ·
      refine ⟨168637421401408309312532609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112424947600938872875021739 168637421401408309312532609)
      ·
        refine ⟨126478066051056231984399457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168637421401408309312532609 126478066051056231984399457)
        ·
          refine ⟨94858549538292173988299593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126478066051056231984399457 94858549538292173988299593)
          ·
            refine ⟨71143912153719130491224695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94858549538292173988299593 71143912153719130491224695)
            ·
              refine ⟨106715868230578695736837043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71143912153719130491224695 106715868230578695736837043)
              ·
                refine ⟨160073802345868043605255565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106715868230578695736837043 160073802345868043605255565)
                ·
                  refine ⟨60027675879700516351970837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160073802345868043605255565 60027675879700516351970837)
                  ·
                    refine ⟨2813797306860961703998633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60027675879700516351970837 2813797306860961703998633)
                    ·
                      refine ⟨2110347980145721277998975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813797306860961703998633 2110347980145721277998975)
                      ·
                        rfl

theorem cell23_4109888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_4109888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109888 prefixEnd_4109888 := by exact prefixLift 4109888
  have htrace : WordTrace (prefixWord ++ tailWord_4109888) baseStart_4109888 baseEnd_4109888 := by
    simpa [prefixWord, tailWord_4109888, baseEnd_4109888] using wordTrace_append hprefix tailTrace_4109888
  have hstable : (prefixWord ++ tailWord_4109888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109888).length < 2 ^ (prefixWord ++ tailWord_4109888).sum := by decide
  have hdescent : baseEnd_4109888 < baseStart_4109888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109898 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_4109898 : Nat := 118140960795 + 4109898 * 2 ^ 59
def prefixEnd_4109898 : Nat := 4983230072969 + 3 ^ 40 * 4109898 * 2
def baseEnd_4109898 : Nat := 703451038317422079624643

theorem tailTrace_4109898 : CollatzResearch.WordTrace tailWord_4109898 prefixEnd_4109898 703451038317422079624643 := by
  unfold tailWord_4109898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37475073716137233885306587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99933529909699290360817565 37475073716137233885306587)
  ·
    refine ⟨56212610574205850827959881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37475073716137233885306587 56212610574205850827959881)
    ·
      refine ⟨42159457930654388120969911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56212610574205850827959881 42159457930654388120969911)
      ·
        refine ⟨63239186895981582181454867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42159457930654388120969911 63239186895981582181454867)
        ·
          refine ⟨94858780343972373272182301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63239186895981582181454867 94858780343972373272182301)
          ·
            refine ⟨35572042628989639977068363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94858780343972373272182301 35572042628989639977068363)
            ·
              refine ⟨53358063943484459965602545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35572042628989639977068363 53358063943484459965602545)
              ·
                refine ⟨40018547957613344974201909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53358063943484459965602545 40018547957613344974201909)
                ·
                  refine ⟨3751738871026251091331429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40018547957613344974201909 3751738871026251091331429)
                  ·
                    refine ⟨703451038317422079624643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3751738871026251091331429 703451038317422079624643)
                    ·
                      rfl

theorem cell23_4109898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_4109898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109898 prefixEnd_4109898 := by exact prefixLift 4109898
  have htrace : WordTrace (prefixWord ++ tailWord_4109898) baseStart_4109898 baseEnd_4109898 := by
    simpa [prefixWord, tailWord_4109898, baseEnd_4109898] using wordTrace_append hprefix tailTrace_4109898
  have hstable : (prefixWord ++ tailWord_4109898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109898).length < 2 ^ (prefixWord ++ tailWord_4109898).sum := by decide
  have hdescent : baseEnd_4109898 < baseStart_4109898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109949 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_4109949 : Nat := 118140960795 + 4109949 * 2 ^ 59
def prefixEnd_4109949 : Nat := 4983230072969 + 3 ^ 40 * 4109949 * 2
def baseEnd_4109949 : Nat := 703459767488548513112065

theorem tailTrace_4109949 : CollatzResearch.WordTrace tailWord_4109949 prefixEnd_4109949 703459767488548513112065 := by
  unfold tailWord_4109949
  simp only [CollatzResearch.WordTrace]
  refine ⟨149902154987364171251332901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99934769991576114167555267 149902154987364171251332901)
  ·
    refine ⟨28106654060130782109624919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149902154987364171251332901 28106654060130782109624919)
    ·
      refine ⟨42159981090196173164437379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28106654060130782109624919 42159981090196173164437379)
      ·
        refine ⟨63239971635294259746656069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42159981090196173164437379 63239971635294259746656069)
        ·
          refine ⟨11857494681617673702498013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63239971635294259746656069 11857494681617673702498013)
          ·
            refine ⟨4446560505606627638436755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11857494681617673702498013 4446560505606627638436755)
            ·
              refine ⟨6669840758409941457655133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446560505606627638436755 6669840758409941457655133)
              ·
                refine ⟨2501190284403728046620675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6669840758409941457655133 2501190284403728046620675)
                ·
                  refine ⟨3751785426605592069931013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501190284403728046620675 3751785426605592069931013)
                  ·
                    refine ⟨703459767488548513112065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3751785426605592069931013 703459767488548513112065)
                    ·
                      rfl

theorem cell23_4109949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_4109949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109949 prefixEnd_4109949 := by exact prefixLift 4109949
  have htrace : WordTrace (prefixWord ++ tailWord_4109949) baseStart_4109949 baseEnd_4109949 := by
    simpa [prefixWord, tailWord_4109949, baseEnd_4109949] using wordTrace_append hprefix tailTrace_4109949
  have hstable : (prefixWord ++ tailWord_4109949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109949).length < 2 ^ (prefixWord ++ tailWord_4109949).sum := by decide
  have hdescent : baseEnd_4109949 < baseStart_4109949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109951 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 7]
def baseStart_4109951 : Nat := 118140960795 + 4109951 * 2 ^ 59
def prefixEnd_4109951 : Nat := 4983230072969 + 3 ^ 40 * 4109951 * 2
def baseEnd_4109951 : Nat := 2110380329426954531511185

theorem tailTrace_4109951 : CollatzResearch.WordTrace tailWord_4109951 prefixEnd_4109951 2110380329426954531511185 := by
  unfold tailWord_4109951
  simp only [CollatzResearch.WordTrace]
  refine ⟨149902227933356925592905707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99934818622237950395270471 149902227933356925592905707)
  ·
    refine ⟨224853341900035388389358561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149902227933356925592905707 224853341900035388389358561)
    ·
      refine ⟨168640006425026541292018921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224853341900035388389358561 168640006425026541292018921)
      ·
        refine ⟨126480004818769905969014191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168640006425026541292018921 126480004818769905969014191)
        ·
          refine ⟨189720007228154858953521287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126480004818769905969014191 189720007228154858953521287)
          ·
            refine ⟨284580010842232288430281931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189720007228154858953521287 284580010842232288430281931)
            ·
              refine ⟨426870016263348432645422897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284580010842232288430281931 426870016263348432645422897)
              ·
                refine ⟨320152512197511324484067173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426870016263348432645422897 320152512197511324484067173)
                ·
                  refine ⟨60028596037033373340762595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320152512197511324484067173 60028596037033373340762595)
                  ·
                    refine ⟨90042894055550060011143893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60028596037033373340762595 90042894055550060011143893)
                    ·
                      refine ⟨2110380329426954531511185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90042894055550060011143893 2110380329426954531511185)
                      ·
                        rfl

theorem cell23_4109951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_4109951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109951 prefixEnd_4109951 := by exact prefixLift 4109951
  have htrace : WordTrace (prefixWord ++ tailWord_4109951) baseStart_4109951 baseEnd_4109951 := by
    simpa [prefixWord, tailWord_4109951, baseEnd_4109951] using wordTrace_append hprefix tailTrace_4109951
  have hstable : (prefixWord ++ tailWord_4109951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109951).length < 2 ^ (prefixWord ++ tailWord_4109951).sum := by decide
  have hdescent : baseEnd_4109951 < baseStart_4109951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4109971 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 10]
def baseStart_4109971 : Nat := 118140960795 + 4109971 * 2 ^ 59
def prefixEnd_4109971 : Nat := 4983230072969 + 3 ^ 40 * 4109971 * 2
def baseEnd_4109971 : Nat := 703463533013348151087031

theorem tailTrace_4109971 : CollatzResearch.WordTrace tailWord_4109971 prefixEnd_4109971 703463533013348151087031 := by
  unfold tailWord_4109971
  simp only [CollatzResearch.WordTrace]
  refine ⟨149902957393284469008633767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99935304928856312672422511 149902957393284469008633767)
  ·
    refine ⟨224854436089926703512950651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149902957393284469008633767 224854436089926703512950651)
    ·
      refine ⟨337281654134890055269425977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224854436089926703512950651 337281654134890055269425977)
      ·
        refine ⟨252961240601167541452069483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337281654134890055269425977 252961240601167541452069483)
        ·
          refine ⟨379441860901751312178104225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252961240601167541452069483 379441860901751312178104225)
          ·
            refine ⟨284581395676313484133578169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379441860901751312178104225 284581395676313484133578169)
            ·
              refine ⟨213436046757235113100183627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284581395676313484133578169 213436046757235113100183627)
              ·
                refine ⟨320154070135852669650275441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213436046757235113100183627 320154070135852669650275441)
                ·
                  refine ⟨240115552601889502237706581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320154070135852669650275441 240115552601889502237706581)
                  ·
                    refine ⟨703463533013348151087031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 240115552601889502237706581 703463533013348151087031)
                    ·
                      rfl

theorem cell23_4109971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 10].length) (baseStart_4109971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4109971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4109971 prefixEnd_4109971 := by exact prefixLift 4109971
  have htrace : WordTrace (prefixWord ++ tailWord_4109971) baseStart_4109971 baseEnd_4109971 := by
    simpa [prefixWord, tailWord_4109971, baseEnd_4109971] using wordTrace_append hprefix tailTrace_4109971
  have hstable : (prefixWord ++ tailWord_4109971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4109971).length < 2 ^ (prefixWord ++ tailWord_4109971).sum := by decide
  have hdescent : baseEnd_4109971 < baseStart_4109971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4109971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110062 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_4110062 : Nat := 118140960795 + 4110062 * 2 ^ 59
def prefixEnd_4110062 : Nat := 4983230072969 + 3 ^ 40 * 4110062 * 2
def baseEnd_4110062 : Nat := 2110437325779603597223175

theorem tailTrace_4110062 : CollatzResearch.WordTrace tailWord_4110062 prefixEnd_4110062 2110437325779603597223175 := by
  unfold tailWord_4110062
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738284554494348943774555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99937517623969861033464293 18738284554494348943774555)
  ·
    refine ⟨28107426831741523415661833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18738284554494348943774555 28107426831741523415661833)
    ·
      refine ⟨21080570123806142561746375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28107426831741523415661833 21080570123806142561746375)
      ·
        refine ⟨31620855185709213842619563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21080570123806142561746375 31620855185709213842619563)
        ·
          refine ⟨47431282778563820763929345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31620855185709213842619563 47431282778563820763929345)
          ·
            refine ⟨35573462083922865572947009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47431282778563820763929345 35573462083922865572947009)
            ·
              refine ⟨26680096562942149179710257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35573462083922865572947009 26680096562942149179710257)
              ·
                refine ⟨20010072422206611884782693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26680096562942149179710257 20010072422206611884782693)
                ·
                  refine ⟨3751888579163739728396755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20010072422206611884782693 3751888579163739728396755)
                  ·
                    refine ⟨5627832868745609592595133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3751888579163739728396755 5627832868745609592595133)
                    ·
                      refine ⟨2110437325779603597223175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627832868745609592595133 2110437325779603597223175)
                      ·
                        rfl

theorem cell23_4110062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_4110062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110062 prefixEnd_4110062 := by exact prefixLift 4110062
  have htrace : WordTrace (prefixWord ++ tailWord_4110062) baseStart_4110062 baseEnd_4110062 := by
    simpa [prefixWord, tailWord_4110062, baseEnd_4110062] using wordTrace_append hprefix tailTrace_4110062
  have hstable : (prefixWord ++ tailWord_4110062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110062).length < 2 ^ (prefixWord ++ tailWord_4110062).sum := by decide
  have hdescent : baseEnd_4110062 < baseStart_4110062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110085 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 8, 2]
def baseStart_4110085 : Nat := 118140960795 + 4110085 * 2 ^ 59
def prefixEnd_4110085 : Nat := 4983230072969 + 3 ^ 40 * 4110085 * 2
def baseEnd_4110085 : Nat := 2110449135834657007235569

theorem tailTrace_4110085 : CollatzResearch.WordTrace tailWord_4110085 prefixEnd_4110085 2110449135834657007235569 := by
  unfold tailWord_4110085
  simp only [CollatzResearch.WordTrace]
  refine ⟨149907115314871466478283709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99938076876580977652189139 149907115314871466478283709)
  ·
    refine ⟨56215168243076799929356391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149907115314871466478283709 56215168243076799929356391)
    ·
      refine ⟨84322752364615199894034587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56215168243076799929356391 84322752364615199894034587)
      ·
        refine ⟨126484128546922799841051881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84322752364615199894034587 126484128546922799841051881)
        ·
          refine ⟨94863096410192099880788911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126484128546922799841051881 94863096410192099880788911)
          ·
            refine ⟨142294644615288149821183367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94863096410192099880788911 142294644615288149821183367)
            ·
              refine ⟨213441966922932224731775051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142294644615288149821183367 213441966922932224731775051)
              ·
                refine ⟨320162950384398337097662577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213441966922932224731775051 320162950384398337097662577)
                ·
                  refine ⟨240122212788298752823246933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320162950384398337097662577 240122212788298752823246933)
                  ·
                    refine ⟨2813932181112876009647425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 240122212788298752823246933 2813932181112876009647425)
                    ·
                      refine ⟨2110449135834657007235569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2813932181112876009647425 2110449135834657007235569)
                      ·
                        rfl

theorem cell23_4110085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_4110085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110085 prefixEnd_4110085 := by exact prefixLift 4110085
  have htrace : WordTrace (prefixWord ++ tailWord_4110085) baseStart_4110085 baseEnd_4110085 := by
    simpa [prefixWord, tailWord_4110085, baseEnd_4110085] using wordTrace_append hprefix tailTrace_4110085
  have hstable : (prefixWord ++ tailWord_4110085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110085).length < 2 ^ (prefixWord ++ tailWord_4110085).sum := by decide
  have hdescent : baseEnd_4110085 < baseStart_4110085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110128 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_4110128 : Nat := 118140960795 + 4110128 * 2 ^ 59
def prefixEnd_4110128 : Nat := 4983230072969 + 3 ^ 40 * 4110128 * 2
def baseEnd_4110128 : Nat := 2110471215502800338997871

theorem tailTrace_4110128 : CollatzResearch.WordTrace tailWord_4110128 prefixEnd_4110128 2110471215502800338997871 := by
  unfold tailWord_4110128
  simp only [CollatzResearch.WordTrace]
  refine ⟨74954341826857842411049519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99939122435810456548066025 74954341826857842411049519)
  ·
    refine ⟨112431512740286763616574279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74954341826857842411049519 112431512740286763616574279)
    ·
      refine ⟨168647269110430145424861419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112431512740286763616574279 168647269110430145424861419)
      ·
        refine ⟨252970903665645218137292129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168647269110430145424861419 252970903665645218137292129)
        ·
          refine ⟨189728177749233913602969097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252970903665645218137292129 189728177749233913602969097)
          ·
            refine ⟨142296133311925435202226823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189728177749233913602969097 142296133311925435202226823)
            ·
              refine ⟨213444199967888152803340235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142296133311925435202226823 213444199967888152803340235)
              ·
                refine ⟨320166299951832229205010353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213444199967888152803340235 320166299951832229205010353)
                ·
                  refine ⟨240124724963874171903757765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320166299951832229205010353 240124724963874171903757765)
                  ·
                    refine ⟨45023385930726407231954581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 240124724963874171903757765 45023385930726407231954581)
                    ·
                      refine ⟨2110471215502800338997871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45023385930726407231954581 2110471215502800338997871)
                      ·
                        rfl

theorem cell23_4110128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_4110128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110128 prefixEnd_4110128 := by exact prefixLift 4110128
  have htrace : WordTrace (prefixWord ++ tailWord_4110128) baseStart_4110128 baseEnd_4110128 := by
    simpa [prefixWord, tailWord_4110128, baseEnd_4110128] using wordTrace_append hprefix tailTrace_4110128
  have hstable : (prefixWord ++ tailWord_4110128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110128).length < 2 ^ (prefixWord ++ tailWord_4110128).sum := by decide
  have hdescent : baseEnd_4110128 < baseStart_4110128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110135 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_4110135 : Nat := 118140960795 + 4110135 * 2 ^ 59
def prefixEnd_4110135 : Nat := 4983230072969 + 3 ^ 40 * 4110135 * 2
def baseEnd_4110135 : Nat := 2110474809867381811610339

theorem tailTrace_4110135 : CollatzResearch.WordTrace tailWord_4110135 prefixEnd_4110135 2110474809867381811610339 := by
  unfold tailWord_4110135
  simp only [CollatzResearch.WordTrace]
  refine ⟨149908938964690325017603859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99939292643126883345069239 149908938964690325017603859)
  ·
    refine ⟨224863408447035487526405789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149908938964690325017603859 224863408447035487526405789)
    ·
      refine ⟨84323778167638307822402171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224863408447035487526405789 84323778167638307822402171)
      ·
        refine ⟨126485667251457461733603257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84323778167638307822402171 126485667251457461733603257)
        ·
          refine ⟨94864250438593096300202443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126485667251457461733603257 94864250438593096300202443)
          ·
            refine ⟨142296375657889644450303665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94864250438593096300202443 142296375657889644450303665)
            ·
              refine ⟨106722281743417233337727749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142296375657889644450303665 106722281743417233337727749)
              ·
                refine ⟨20010427826890731250823953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106722281743417233337727749 20010427826890731250823953)
                ·
                  refine ⟨15007820870168048438117965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20010427826890731250823953 15007820870168048438117965)
                  ·
                    refine ⟨5627932826313018164294237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15007820870168048438117965 5627932826313018164294237)
                    ·
                      refine ⟨2110474809867381811610339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5627932826313018164294237 2110474809867381811610339)
                      ·
                        rfl

theorem cell23_4110135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_4110135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110135 prefixEnd_4110135 := by exact prefixLift 4110135
  have htrace : WordTrace (prefixWord ++ tailWord_4110135) baseStart_4110135 baseEnd_4110135 := by
    simpa [prefixWord, tailWord_4110135, baseEnd_4110135] using wordTrace_append hprefix tailTrace_4110135
  have hstable : (prefixWord ++ tailWord_4110135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110135).length < 2 ^ (prefixWord ++ tailWord_4110135).sum := by decide
  have hdescent : baseEnd_4110135 < baseStart_4110135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110142 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_4110142 : Nat := 118140960795 + 4110142 * 2 ^ 59
def prefixEnd_4110142 : Nat := 4983230072969 + 3 ^ 40 * 4110142 * 2
def baseEnd_4110142 : Nat := 234497600470218142691423

theorem tailTrace_4110142 : CollatzResearch.WordTrace tailWord_4110142 prefixEnd_4110142 234497600470218142691423 := by
  unfold tailWord_4110142
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738649284458120651638585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99939462850443310142072453 18738649284458120651638585)
  ·
    refine ⟨14053986963343590488728939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18738649284458120651638585 14053986963343590488728939)
    ·
      refine ⟨21080980445015385733093409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14053986963343590488728939 21080980445015385733093409)
      ·
        refine ⟨15810735333761539299820057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21080980445015385733093409 15810735333761539299820057)
        ·
          refine ⟨11858051500321154474865043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15810735333761539299820057 11858051500321154474865043)
          ·
            refine ⟨17787077250481731712297565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858051500321154474865043 17787077250481731712297565)
            ·
              refine ⟨6670153968930649392111587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17787077250481731712297565 6670153968930649392111587)
              ·
                refine ⟨10005230953395974088167381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670153968930649392111587 10005230953395974088167381)
                ·
                  refine ⟨234497600470218142691423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10005230953395974088167381 234497600470218142691423)
                  ·
                    rfl

theorem cell23_4110142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_4110142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110142 prefixEnd_4110142 := by exact prefixLift 4110142
  have htrace : WordTrace (prefixWord ++ tailWord_4110142) baseStart_4110142 baseEnd_4110142 := by
    simpa [prefixWord, tailWord_4110142, baseEnd_4110142] using wordTrace_append hprefix tailTrace_4110142
  have hstable : (prefixWord ++ tailWord_4110142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110142).length < 2 ^ (prefixWord ++ tailWord_4110142).sum := by decide
  have hdescent : baseEnd_4110142 < baseStart_4110142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110192 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 2, 4, 2]
def baseStart_4110192 : Nat := 118140960795 + 4110192 * 2 ^ 59
def prefixEnd_4110192 : Nat := 4983230072969 + 3 ^ 40 * 4110192 * 2
def baseEnd_4110192 : Nat := 2110504078264688088597577

theorem tailTrace_4110192 : CollatzResearch.WordTrace tailWord_4110192 prefixEnd_4110192 2110504078264688088597577 := by
  unfold tailWord_4110192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74955508962741911876214415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99940678616989215834952553 74955508962741911876214415)
  ·
    refine ⟨112433263444112867814321623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74955508962741911876214415 112433263444112867814321623)
    ·
      refine ⟨168649895166169301721482435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112433263444112867814321623 168649895166169301721482435)
      ·
        refine ⟨252974842749253952582223653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168649895166169301721482435 252974842749253952582223653)
        ·
          refine ⟨47432783015485116109166935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252974842749253952582223653 47432783015485116109166935)
          ·
            refine ⟨71149174523227674163750403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47432783015485116109166935 71149174523227674163750403)
            ·
              refine ⟨106723761784841511245625605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71149174523227674163750403 106723761784841511245625605)
              ·
                refine ⟨20010705334657783358554801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106723761784841511245625605 20010705334657783358554801)
                ·
                  refine ⟨15008029000993337518916101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20010705334657783358554801 15008029000993337518916101)
                  ·
                    refine ⟨2814005437686250784796769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15008029000993337518916101 2814005437686250784796769)
                    ·
                      refine ⟨2110504078264688088597577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814005437686250784796769 2110504078264688088597577)
                      ·
                        rfl

theorem cell23_4110192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 4, 2].length) (baseStart_4110192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110192 prefixEnd_4110192 := by exact prefixLift 4110192
  have htrace : WordTrace (prefixWord ++ tailWord_4110192) baseStart_4110192 baseEnd_4110192 := by
    simpa [prefixWord, tailWord_4110192, baseEnd_4110192] using wordTrace_append hprefix tailTrace_4110192
  have hstable : (prefixWord ++ tailWord_4110192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110192).length < 2 ^ (prefixWord ++ tailWord_4110192).sum := by decide
  have hdescent : baseEnd_4110192 < baseStart_4110192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110195 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 3]
def baseStart_4110195 : Nat := 118140960795 + 4110195 * 2 ^ 59
def prefixEnd_4110195 : Nat := 4983230072969 + 3 ^ 40 * 4110195 * 2
def baseEnd_4110195 : Nat := 2110505618706651576860063

theorem tailTrace_4110195 : CollatzResearch.WordTrace tailWord_4110195 prefixEnd_4110195 2110505618706651576860063 := by
  unfold tailWord_4110195
  simp only [CollatzResearch.WordTrace]
  refine ⟨149911127344472955264788039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99940751562981970176525359 149911127344472955264788039)
  ·
    refine ⟨224866691016709432897182059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149911127344472955264788039 224866691016709432897182059)
    ·
      refine ⟨337300036525064149345773089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224866691016709432897182059 337300036525064149345773089)
      ·
        refine ⟨252975027393798112009329817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337300036525064149345773089 252975027393798112009329817)
        ·
          refine ⟨189731270545348584006997363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252975027393798112009329817 189731270545348584006997363)
          ·
            refine ⟨284596905818022876010496045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189731270545348584006997363 284596905818022876010496045)
            ·
              refine ⟨106723839681758578503936017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284596905818022876010496045 106723839681758578503936017)
              ·
                refine ⟨80042879761318933877952013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106723839681758578503936017 80042879761318933877952013)
                ·
                  refine ⟨30016079910494600204232005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80042879761318933877952013 30016079910494600204232005)
                  ·
                    refine ⟨5628014983217737538293501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30016079910494600204232005 5628014983217737538293501)
                    ·
                      refine ⟨2110505618706651576860063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628014983217737538293501 2110505618706651576860063)
                      ·
                        rfl

theorem cell23_4110195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_4110195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110195 prefixEnd_4110195 := by exact prefixLift 4110195
  have htrace : WordTrace (prefixWord ++ tailWord_4110195) baseStart_4110195 baseEnd_4110195 := by
    simpa [prefixWord, tailWord_4110195, baseEnd_4110195] using wordTrace_append hprefix tailTrace_4110195
  have hstable : (prefixWord ++ tailWord_4110195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110195).length < 2 ^ (prefixWord ++ tailWord_4110195).sum := by decide
  have hdescent : baseEnd_4110195 < baseStart_4110195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110205 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_4110205 : Nat := 118140960795 + 4110205 * 2 ^ 59
def prefixEnd_4110205 : Nat := 4983230072969 + 3 ^ 40 * 4110205 * 2
def baseEnd_4110205 : Nat := 2110510753513196537735017

theorem tailTrace_4110205 : CollatzResearch.WordTrace tailWord_4110205 prefixEnd_4110205 2110510753513196537735017 := by
  unfold tailWord_4110205
  simp only [CollatzResearch.WordTrace]
  refine ⟨149911492074436726972652069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99940994716291151315101379 149911492074436726972652069)
  ·
    refine ⟨28108404763956886307372263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149911492074436726972652069 28108404763956886307372263)
    ·
      refine ⟨42162607145935329461058395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28108404763956886307372263 42162607145935329461058395)
      ·
        refine ⟨63243910718902994191587593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42162607145935329461058395 63243910718902994191587593)
        ·
          refine ⟨47432933039177245643690695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63243910718902994191587593 47432933039177245643690695)
          ·
            refine ⟨71149399558765868465536043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47432933039177245643690695 71149399558765868465536043)
            ·
              refine ⟨106724099338148802698304065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71149399558765868465536043 106724099338148802698304065)
              ·
                refine ⟨80043074503611602023728049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106724099338148802698304065 80043074503611602023728049)
                ·
                  refine ⟨60032305877708701517796037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80043074503611602023728049 60032305877708701517796037)
                  ·
                    refine ⟨11256057352070381534586757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60032305877708701517796037 11256057352070381534586757)
                    ·
                      refine ⟨2110510753513196537735017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11256057352070381534586757 2110510753513196537735017)
                      ·
                        rfl

theorem cell23_4110205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_4110205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110205 prefixEnd_4110205 := by exact prefixLift 4110205
  have htrace : WordTrace (prefixWord ++ tailWord_4110205) baseStart_4110205 baseEnd_4110205 := by
    simpa [prefixWord, tailWord_4110205, baseEnd_4110205] using wordTrace_append hprefix tailTrace_4110205
  have hstable : (prefixWord ++ tailWord_4110205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110205).length < 2 ^ (prefixWord ++ tailWord_4110205).sum := by decide
  have hdescent : baseEnd_4110205 < baseStart_4110205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110212 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_4110212 : Nat := 118140960795 + 4110212 * 2 ^ 59
def prefixEnd_4110212 : Nat := 4983230072969 + 3 ^ 40 * 4110212 * 2
def baseEnd_4110212 : Nat := 2110514347877778010347485

theorem tailTrace_4110212 : CollatzResearch.WordTrace tailWord_4110212 prefixEnd_4110212 2110514347877778010347485 := by
  unfold tailWord_4110212
  simp only [CollatzResearch.WordTrace]
  refine ⟨74955873692705683584078445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99941164923607578112104593 74955873692705683584078445)
  ·
    refine ⟨28108452634764631344029417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74955873692705683584078445 28108452634764631344029417)
    ·
      refine ⟨21081339476073473508022063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28108452634764631344029417 21081339476073473508022063)
      ·
        refine ⟨31622009214110210262033095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21081339476073473508022063 31622009214110210262033095)
        ·
          refine ⟨47433013821165315393049643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31622009214110210262033095 47433013821165315393049643)
          ·
            refine ⟨71149520731747973089574465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47433013821165315393049643 71149520731747973089574465)
            ·
              refine ⟨53362140548810979817180849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71149520731747973089574465 53362140548810979817180849)
              ·
                refine ⟨40021605411608234862885637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53362140548810979817180849 40021605411608234862885637)
                ·
                  refine ⟨7504051014676544036791057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40021605411608234862885637 7504051014676544036791057)
                  ·
                    refine ⟨5628038261007408027593293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7504051014676544036791057 5628038261007408027593293)
                    ·
                      refine ⟨2110514347877778010347485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628038261007408027593293 2110514347877778010347485)
                      ·
                        rfl

theorem cell23_4110212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_4110212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110212 prefixEnd_4110212 := by exact prefixLift 4110212
  have htrace : WordTrace (prefixWord ++ tailWord_4110212) baseStart_4110212 baseEnd_4110212 := by
    simpa [prefixWord, tailWord_4110212, baseEnd_4110212] using wordTrace_append hprefix tailTrace_4110212
  have hstable : (prefixWord ++ tailWord_4110212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110212).length < 2 ^ (prefixWord ++ tailWord_4110212).sum := by decide
  have hdescent : baseEnd_4110212 < baseStart_4110212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110226 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4110226 : Nat := 118140960795 + 4110226 * 2 ^ 59
def prefixEnd_4110226 : Nat := 4983230072969 + 3 ^ 40 * 4110226 * 2
def baseEnd_4110226 : Nat := 2110521536606940955572421

theorem tailTrace_4110226 : CollatzResearch.WordTrace tailWord_4110226 prefixEnd_4110226 2110521536606940955572421 := by
  unfold tailWord_4110226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478064501840161889791633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99941505338240431706111021 37478064501840161889791633)
  ·
    refine ⟨28108548376380121417343725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37478064501840161889791633 28108548376380121417343725)
    ·
      refine ⟨10540705641142545531503897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28108548376380121417343725 10540705641142545531503897)
      ·
        refine ⟨7905529230856909148627923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10540705641142545531503897 7905529230856909148627923)
        ·
          refine ⟨11858293846285363722941885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905529230856909148627923 11858293846285363722941885)
          ·
            refine ⟨4446860192357011396103207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11858293846285363722941885 4446860192357011396103207)
            ·
              refine ⟨6670290288535517094154811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446860192357011396103207 6670290288535517094154811)
              ·
                refine ⟨10005435432803275641232217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670290288535517094154811 10005435432803275641232217)
                ·
                  refine ⟨7504076574602456730924163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10005435432803275641232217 7504076574602456730924163)
                  ·
                    refine ⟨11256114861903685096386245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504076574602456730924163 11256114861903685096386245)
                    ·
                      refine ⟨2110521536606940955572421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11256114861903685096386245 2110521536606940955572421)
                      ·
                        rfl

theorem cell23_4110226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4110226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110226 prefixEnd_4110226 := by exact prefixLift 4110226
  have htrace : WordTrace (prefixWord ++ tailWord_4110226) baseStart_4110226 baseEnd_4110226 := by
    simpa [prefixWord, tailWord_4110226, baseEnd_4110226] using wordTrace_append hprefix tailTrace_4110226
  have hstable : (prefixWord ++ tailWord_4110226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110226).length < 2 ^ (prefixWord ++ tailWord_4110226).sum := by decide
  have hdescent : baseEnd_4110226 < baseStart_4110226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110236 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_4110236 : Nat := 118140960795 + 4110236 * 2 ^ 59
def prefixEnd_4110236 : Nat := 4983230072969 + 3 ^ 40 * 4110236 * 2
def baseEnd_4110236 : Nat := 703508890471161972149125

theorem tailTrace_4110236 : CollatzResearch.WordTrace tailWord_4110236 prefixEnd_4110236 703508890471161972149125 := by
  unfold tailWord_4110236
  simp only [CollatzResearch.WordTrace]
  refine ⟨74956311368662209633515281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99941748491549612844687041 74956311368662209633515281)
  ·
    refine ⟨56217233526496657225136461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74956311368662209633515281 56217233526496657225136461)
    ·
      refine ⟨21081462572436246459426173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56217233526496657225136461 21081462572436246459426173)
      ·
        refine ⟨7905548464663592422284815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21081462572436246459426173 7905548464663592422284815)
        ·
          refine ⟨11858322696995388633427223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7905548464663592422284815 11858322696995388633427223)
          ·
            refine ⟨17787484045493082950140835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858322696995388633427223 17787484045493082950140835)
            ·
              refine ⟨26681226068239624425211253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17787484045493082950140835 26681226068239624425211253)
              ·
                refine ⟨2501364943897464789863555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26681226068239624425211253 2501364943897464789863555)
                ·
                  refine ⟨3752047415846197184795333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501364943897464789863555 3752047415846197184795333)
                  ·
                    refine ⟨703508890471161972149125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752047415846197184795333 703508890471161972149125)
                    ·
                      rfl

theorem cell23_4110236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_4110236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110236 prefixEnd_4110236 := by exact prefixLift 4110236
  have htrace : WordTrace (prefixWord ++ tailWord_4110236) baseStart_4110236 baseEnd_4110236 := by
    simpa [prefixWord, tailWord_4110236, baseEnd_4110236] using wordTrace_append hprefix tailTrace_4110236
  have hstable : (prefixWord ++ tailWord_4110236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110236).length < 2 ^ (prefixWord ++ tailWord_4110236).sum := by decide
  have hdescent : baseEnd_4110236 < baseStart_4110236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110252 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 5, 5, 2]
def baseStart_4110252 : Nat := 118140960795 + 4110252 * 2 ^ 59
def prefixEnd_4110252 : Nat := 4983230072969 + 3 ^ 40 * 4110252 * 2
def baseEnd_4110252 : Nat := 2110534887103957853847301

theorem tailTrace_4110252 : CollatzResearch.WordTrace tailWord_4110252 prefixEnd_4110252 2110534887103957853847301 := by
  unfold tailWord_4110252
  simp only [CollatzResearch.WordTrace]
  refine ⟨74956603152633226999806505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99942137536844302666408673 74956603152633226999806505)
  ·
    refine ⟨56217452364474920249854879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74956603152633226999806505 56217452364474920249854879)
    ·
      refine ⟨84326178546712380374782319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56217452364474920249854879 84326178546712380374782319)
      ·
        refine ⟨126489267820068570562173479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84326178546712380374782319 126489267820068570562173479)
        ·
          refine ⟨189733901730102855843260219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126489267820068570562173479 189733901730102855843260219)
          ·
            refine ⟨284600852595154283764890329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189733901730102855843260219 284600852595154283764890329)
            ·
              refine ⟨213450639446365712823667747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284600852595154283764890329 213450639446365712823667747)
              ·
                refine ⟨320175959169548569235501621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213450639446365712823667747 320175959169548569235501621)
                ·
                  refine ⟨30016496172145178365828277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320175959169548569235501621 30016496172145178365828277)
                  ·
                    refine ⟨2814046516138610471796401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30016496172145178365828277 2814046516138610471796401)
                    ·
                      refine ⟨2110534887103957853847301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814046516138610471796401 2110534887103957853847301)
                      ·
                        rfl

theorem cell23_4110252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 5, 2].length) (baseStart_4110252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110252 prefixEnd_4110252 := by exact prefixLift 4110252
  have htrace : WordTrace (prefixWord ++ tailWord_4110252) baseStart_4110252 baseEnd_4110252 := by
    simpa [prefixWord, tailWord_4110252, baseEnd_4110252] using wordTrace_append hprefix tailTrace_4110252
  have hstable : (prefixWord ++ tailWord_4110252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110252).length < 2 ^ (prefixWord ++ tailWord_4110252).sum := by decide
  have hdescent : baseEnd_4110252 < baseStart_4110252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110259 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 3]
def baseStart_4110259 : Nat := 118140960795 + 4110259 * 2 ^ 59
def prefixEnd_4110259 : Nat := 4983230072969 + 3 ^ 40 * 4110259 * 2
def baseEnd_4110259 : Nat := 2110538481468539326459769

theorem tailTrace_4110259 : CollatzResearch.WordTrace tailWord_4110259 prefixEnd_4110259 2110538481468539326459769 := by
  unfold tailWord_4110259
  simp only [CollatzResearch.WordTrace]
  refine ⟨149913461616241094195117831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99942307744160729463411887 149913461616241094195117831)
  ·
    refine ⟨224870192424361641292676747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149913461616241094195117831 224870192424361641292676747)
    ·
      refine ⟨337305288636542461939015121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224870192424361641292676747 337305288636542461939015121)
      ·
        refine ⟨252978966477406846454261341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337305288636542461939015121 252978966477406846454261341)
        ·
          refine ⟨94867112429027567420348003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252978966477406846454261341 94867112429027567420348003)
          ·
            refine ⟨142300668643541351130522005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94867112429027567420348003 142300668643541351130522005)
            ·
              refine ⟨6670343842666000834243219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142300668643541351130522005 6670343842666000834243219)
              ·
                refine ⟨10005515763999001251364829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670343842666000834243219 10005515763999001251364829)
                ·
                  refine ⟨3752068411499625469261811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10005515763999001251364829 3752068411499625469261811)
                  ·
                    refine ⟨5628102617249438203892717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752068411499625469261811 5628102617249438203892717)
                    ·
                      refine ⟨2110538481468539326459769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628102617249438203892717 2110538481468539326459769)
                      ·
                        rfl

theorem cell23_4110259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_4110259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110259 prefixEnd_4110259 := by exact prefixLift 4110259
  have htrace : WordTrace (prefixWord ++ tailWord_4110259) baseStart_4110259 baseEnd_4110259 := by
    simpa [prefixWord, tailWord_4110259, baseEnd_4110259] using wordTrace_append hprefix tailTrace_4110259
  have hstable : (prefixWord ++ tailWord_4110259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110259).length < 2 ^ (prefixWord ++ tailWord_4110259).sum := by decide
  have hdescent : baseEnd_4110259 < baseStart_4110259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110269 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_4110269 : Nat := 118140960795 + 4110269 * 2 ^ 59
def prefixEnd_4110269 : Nat := 4983230072969 + 3 ^ 40 * 4110269 * 2
def baseEnd_4110269 : Nat := 2110543616275084287334723

theorem tailTrace_4110269 : CollatzResearch.WordTrace tailWord_4110269 prefixEnd_4110269 2110543616275084287334723 := by
  unfold tailWord_4110269
  simp only [CollatzResearch.WordTrace]
  refine ⟨149913826346204865902981861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99942550897469910601987907 149913826346204865902981861)
  ·
    refine ⟨28108842439913412356809099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149913826346204865902981861 28108842439913412356809099)
    ·
      refine ⟨42163263659870118535213649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28108842439913412356809099 42163263659870118535213649)
      ·
        refine ⟨31622447744902588901410237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42163263659870118535213649 31622447744902588901410237)
        ·
          refine ⟨11858417904338470838028839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31622447744902588901410237 11858417904338470838028839)
          ·
            refine ⟨17787626856507706257043259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858417904338470838028839 17787626856507706257043259)
            ·
              refine ⟨26681440284761559385564889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17787626856507706257043259 26681440284761559385564889)
              ·
                refine ⟨20011080213571169539173667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26681440284761559385564889 20011080213571169539173667)
                ·
                  refine ⟨30016620320356754308760501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20011080213571169539173667 30016620320356754308760501)
                  ·
                    refine ⟨2814058155033445716446297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30016620320356754308760501 2814058155033445716446297)
                    ·
                      refine ⟨2110543616275084287334723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814058155033445716446297 2110543616275084287334723)
                      ·
                        rfl

theorem cell23_4110269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_4110269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110269 prefixEnd_4110269 := by exact prefixLift 4110269
  have htrace : WordTrace (prefixWord ++ tailWord_4110269) baseStart_4110269 baseEnd_4110269 := by
    simpa [prefixWord, tailWord_4110269, baseEnd_4110269] using wordTrace_append hprefix tailTrace_4110269
  have hstable : (prefixWord ++ tailWord_4110269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110269).length < 2 ^ (prefixWord ++ tailWord_4110269).sum := by decide
  have hdescent : baseEnd_4110269 < baseStart_4110269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110282 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_4110282 : Nat := 118140960795 + 4110282 * 2 ^ 59
def prefixEnd_4110282 : Nat := 4983230072969 + 3 ^ 40 * 4110282 * 2
def baseEnd_4110282 : Nat := 2110550291523592736472163

theorem tailTrace_4110282 : CollatzResearch.WordTrace tailWord_4110282 prefixEnd_4110282 2110550291523592736472163 := by
  unfold tailWord_4110282
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478575123789442280801275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99942866996771846082136733 37478575123789442280801275)
  ·
    refine ⟨56217862685684163421201913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37478575123789442280801275 56217862685684163421201913)
    ·
      refine ⟨42163397014263122565901435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56217862685684163421201913 42163397014263122565901435)
      ·
        refine ⟨63245095521394683848852153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42163397014263122565901435 63245095521394683848852153)
        ·
          refine ⟨47433821641046012886639115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63245095521394683848852153 47433821641046012886639115)
          ·
            refine ⟨71150732461569019329958673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47433821641046012886639115 71150732461569019329958673)
            ·
              refine ⟨53363049346176764497469005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71150732461569019329958673 53363049346176764497469005)
              ·
                refine ⟨20011143504816286686550877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53363049346176764497469005 20011143504816286686550877)
                ·
                  refine ⟨7504178814306107507456579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20011143504816286686550877 7504178814306107507456579)
                  ·
                    refine ⟨11256268221459161261184869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504178814306107507456579 11256268221459161261184869)
                    ·
                      refine ⟨2110550291523592736472163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11256268221459161261184869 2110550291523592736472163)
                      ·
                        rfl

theorem cell23_4110282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_4110282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110282 prefixEnd_4110282 := by exact prefixLift 4110282
  have htrace : WordTrace (prefixWord ++ tailWord_4110282) baseStart_4110282 baseEnd_4110282 := by
    simpa [prefixWord, tailWord_4110282, baseEnd_4110282] using wordTrace_append hprefix tailTrace_4110282
  have hstable : (prefixWord ++ tailWord_4110282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110282).length < 2 ^ (prefixWord ++ tailWord_4110282).sum := by decide
  have hdescent : baseEnd_4110282 < baseStart_4110282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110292 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_4110292 : Nat := 118140960795 + 4110292 * 2 ^ 59
def prefixEnd_4110292 : Nat := 4983230072969 + 3 ^ 40 * 4110292 * 2
def baseEnd_4110292 : Nat := 703518475443379232449039

theorem tailTrace_4110292 : CollatzResearch.WordTrace tailWord_4110292 prefixEnd_4110292 703518475443379232449039 := by
  unfold tailWord_4110292
  simp only [CollatzResearch.WordTrace]
  refine ⟨74957332612560770415534565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99943110150081027220712753 74957332612560770415534565)
  ·
    refine ⟨14054499864855144452912731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74957332612560770415534565 14054499864855144452912731)
    ·
      refine ⟨21081749797282716679369097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14054499864855144452912731 21081749797282716679369097)
      ·
        refine ⟨15811312347962037509526823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21081749797282716679369097 15811312347962037509526823)
        ·
          refine ⟨23716968521943056264290235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15811312347962037509526823 23716968521943056264290235)
          ·
            refine ⟨35575452782914584396435353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23716968521943056264290235 35575452782914584396435353)
            ·
              refine ⟨26681589587185938297326515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35575452782914584396435353 26681589587185938297326515)
              ·
                refine ⟨40022384380778907445989773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26681589587185938297326515 40022384380778907445989773)
                ·
                  refine ⟨15008394142792090292246165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40022384380778907445989773 15008394142792090292246165)
                  ·
                    refine ⟨703518475443379232449039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15008394142792090292246165 703518475443379232449039)
                    ·
                      rfl

theorem cell23_4110292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_4110292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110292 prefixEnd_4110292 := by exact prefixLift 4110292
  have htrace : WordTrace (prefixWord ++ tailWord_4110292) baseStart_4110292 baseEnd_4110292 := by
    simpa [prefixWord, tailWord_4110292, baseEnd_4110292] using wordTrace_append hprefix tailTrace_4110292
  have hstable : (prefixWord ++ tailWord_4110292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110292).length < 2 ^ (prefixWord ++ tailWord_4110292).sum := by decide
  have hdescent : baseEnd_4110292 < baseStart_4110292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110293 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4110293 : Nat := 118140960795 + 4110293 * 2 ^ 59
def prefixEnd_4110293 : Nat := 4983230072969 + 3 ^ 40 * 4110293 * 2
def baseEnd_4110293 : Nat := 2110555939810792193434613

theorem tailTrace_4110293 : CollatzResearch.WordTrace tailWord_4110293 prefixEnd_4110293 2110555939810792193434613 := by
  unfold tailWord_4110293
  simp only [CollatzResearch.WordTrace]
  refine ⟨149914701698117918001855533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99943134465411945334570355 149914701698117918001855533)
  ·
    refine ⟨56218013136794219250695825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149914701698117918001855533 56218013136794219250695825)
    ·
      refine ⟨42163509852595664438021869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56218013136794219250695825 42163509852595664438021869)
      ·
        refine ⟨15811316194723374164258201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42163509852595664438021869 15811316194723374164258201)
        ·
          refine ⟨11858487146042530623193651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15811316194723374164258201 11858487146042530623193651)
          ·
            refine ⟨17787730719063795934790477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11858487146042530623193651 17787730719063795934790477)
            ·
              refine ⟨6670399019648923475546429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17787730719063795934790477 6670399019648923475546429)
              ·
                refine ⟨2501399632368346303329911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6670399019648923475546429 2501399632368346303329911)
                ·
                  refine ⟨3752099448552519454994867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501399632368346303329911 3752099448552519454994867)
                  ·
                    refine ⟨5628149172828779182492301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752099448552519454994867 5628149172828779182492301)
                    ·
                      refine ⟨2110555939810792193434613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628149172828779182492301 2110555939810792193434613)
                      ·
                        rfl

theorem cell23_4110293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4110293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110293 prefixEnd_4110293 := by exact prefixLift 4110293
  have htrace : WordTrace (prefixWord ++ tailWord_4110293) baseStart_4110293 baseEnd_4110293 := by
    simpa [prefixWord, tailWord_4110293, baseEnd_4110293] using wordTrace_append hprefix tailTrace_4110293
  have hstable : (prefixWord ++ tailWord_4110293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110293).length < 2 ^ (prefixWord ++ tailWord_4110293).sum := by decide
  have hdescent : baseEnd_4110293 < baseStart_4110293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110305 : List Nat := [1, 2, 3, 1, 2, 1, 13]
def baseStart_4110305 : Nat := 118140960795 + 4110305 * 2 ^ 59
def prefixEnd_4110305 : Nat := 4983230072969 + 3 ^ 40 * 4110305 * 2
def baseEnd_4110305 : Nat := 26056322241711680820797

theorem tailTrace_4110305 : CollatzResearch.WordTrace tailWord_4110305 prefixEnd_4110305 26056322241711680820797 := by
  unfold tailWord_4110305
  simp only [CollatzResearch.WordTrace]
  refine ⟨149915139374074444051292369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99943426249382962700861579 149915139374074444051292369)
  ·
    refine ⟨112436354530555833038469277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149915139374074444051292369 112436354530555833038469277)
    ·
      refine ⟨42163632948958437389425979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112436354530555833038469277 42163632948958437389425979)
      ·
        refine ⟨63245449423437656084138969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42163632948958437389425979 63245449423437656084138969)
        ·
          refine ⟨47434087067578242063104227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63245449423437656084138969 47434087067578242063104227)
          ·
            refine ⟨71151130601367363094656341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47434087067578242063104227 71151130601367363094656341)
            ·
              refine ⟨26056322241711680820797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 71151130601367363094656341 26056322241711680820797)
              ·
                rfl

theorem cell23_4110305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 13].length) (baseStart_4110305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110305 prefixEnd_4110305 := by exact prefixLift 4110305
  have htrace : WordTrace (prefixWord ++ tailWord_4110305) baseStart_4110305 baseEnd_4110305 := by
    simpa [prefixWord, tailWord_4110305, baseEnd_4110305] using wordTrace_append hprefix tailTrace_4110305
  have hstable : (prefixWord ++ tailWord_4110305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110305).length < 2 ^ (prefixWord ++ tailWord_4110305).sum := by decide
  have hdescent : baseEnd_4110305 < baseStart_4110305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110356 : List Nat := [2, 4, 3, 2, 2, 10]
def baseStart_4110356 : Nat := 118140960795 + 4110356 * 2 ^ 59
def prefixEnd_4110356 : Nat := 4983230072969 + 3 ^ 40 * 4110356 * 2
def baseEnd_4110356 : Nat := 8685548514781997724061

theorem tailTrace_4110356 : CollatzResearch.WordTrace tailWord_4110356 prefixEnd_4110356 8685548514781997724061 := by
  unfold tailWord_4110356
  simp only [CollatzResearch.WordTrace]
  refine ⟨74958499748444839880699461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99944666331259786507599281 74958499748444839880699461)
  ·
    refine ⟨14054718702833407477631149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74958499748444839880699461 14054718702833407477631149)
    ·
      refine ⟨5270519513562527804111681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14054718702833407477631149 5270519513562527804111681)
      ·
        refine ⟨3952889635171895853083761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5270519513562527804111681 3952889635171895853083761)
        ·
          refine ⟨2964667226378921889812821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3952889635171895853083761 2964667226378921889812821)
          ·
            refine ⟨8685548514781997724061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2964667226378921889812821 8685548514781997724061)
            ·
              rfl

theorem cell23_4110356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 10].length) (baseStart_4110356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110356 prefixEnd_4110356 := by exact prefixLift 4110356
  have htrace : WordTrace (prefixWord ++ tailWord_4110356) baseStart_4110356 baseEnd_4110356 := by
    simpa [prefixWord, tailWord_4110356, baseEnd_4110356] using wordTrace_append hprefix tailTrace_4110356
  have hstable : (prefixWord ++ tailWord_4110356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110356).length < 2 ^ (prefixWord ++ tailWord_4110356).sum := by decide
  have hdescent : baseEnd_4110356 < baseStart_4110356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110423 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 2, 2, 2]
def baseStart_4110423 : Nat := 118140960795 + 4110423 * 2 ^ 59
def prefixEnd_4110423 : Nat := 4983230072969 + 3 ^ 40 * 4110423 * 2
def baseEnd_4110423 : Nat := 2110622692295876684809015

theorem tailTrace_4110423 : CollatzResearch.WordTrace tailWord_4110423 prefixEnd_4110423 2110622692295876684809015 := by
  unfold tailWord_4110423
  simp only [CollatzResearch.WordTrace]
  refine ⟨149919443187646950204087923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99946295458431300136058615 149919443187646950204087923)
  ·
    refine ⟨224879164781470425306131885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149919443187646950204087923 224879164781470425306131885)
    ·
      refine ⟨84329686793051409489799457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224879164781470425306131885 84329686793051409489799457)
      ·
        refine ⟨63247265094788557117349593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84329686793051409489799457 63247265094788557117349593)
        ·
          refine ⟨47435448821091417838012195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63247265094788557117349593 47435448821091417838012195)
          ·
            refine ⟨71153173231637126757018293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47435448821091417838012195 71153173231637126757018293)
            ·
              refine ⟨6670609990465980633470465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71153173231637126757018293 6670609990465980633470465)
              ·
                refine ⟨5002957492849485475102849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6670609990465980633470465 5002957492849485475102849)
                ·
                  refine ⟨3752218119637114106327137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5002957492849485475102849 3752218119637114106327137)
                  ·
                    refine ⟨2814163589727835579745353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3752218119637114106327137 2814163589727835579745353)
                    ·
                      refine ⟨2110622692295876684809015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814163589727835579745353 2110622692295876684809015)
                      ·
                        rfl

theorem cell23_4110423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_4110423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110423 prefixEnd_4110423 := by exact prefixLift 4110423
  have htrace : WordTrace (prefixWord ++ tailWord_4110423) baseStart_4110423 baseEnd_4110423 := by
    simpa [prefixWord, tailWord_4110423, baseEnd_4110423] using wordTrace_append hprefix tailTrace_4110423
  have hstable : (prefixWord ++ tailWord_4110423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110423).length < 2 ^ (prefixWord ++ tailWord_4110423).sum := by decide
  have hdescent : baseEnd_4110423 < baseStart_4110423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110439 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_4110439 : Nat := 118140960795 + 4110439 * 2 ^ 59
def prefixEnd_4110439 : Nat := 4983230072969 + 3 ^ 40 * 4110439 * 2
def baseEnd_4110439 : Nat := 2110630907986348622208941

theorem tailTrace_4110439 : CollatzResearch.WordTrace tailWord_4110439 prefixEnd_4110439 2110630907986348622208941 := by
  unfold tailWord_4110439
  simp only [CollatzResearch.WordTrace]
  refine ⟨149920026755588984936670371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99946684503725989957780247 149920026755588984936670371)
  ·
    refine ⟨224880040133383477405005557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149920026755588984936670371 224880040133383477405005557)
    ·
      refine ⟨21082503762504701006719271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224880040133383477405005557 21082503762504701006719271)
      ·
        refine ⟨31623755643757051510078907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21082503762504701006719271 31623755643757051510078907)
        ·
          refine ⟨47435633465635577265118361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31623755643757051510078907 47435633465635577265118361)
          ·
            refine ⟨35576725099226682948838771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47435633465635577265118361 35576725099226682948838771)
            ·
              refine ⟨53365087648840024423258157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35576725099226682948838771 53365087648840024423258157)
              ·
                refine ⟨20011907868315009158721809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53365087648840024423258157 20011907868315009158721809)
                ·
                  refine ⟨15008930901236256869041357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20011907868315009158721809 15008930901236256869041357)
                  ·
                    refine ⟨5628349087963596325890509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15008930901236256869041357 5628349087963596325890509)
                    ·
                      refine ⟨2110630907986348622208941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628349087963596325890509 2110630907986348622208941)
                      ·
                        rfl

theorem cell23_4110439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_4110439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110439 prefixEnd_4110439 := by exact prefixLift 4110439
  have htrace : WordTrace (prefixWord ++ tailWord_4110439) baseStart_4110439 baseEnd_4110439 := by
    simpa [prefixWord, tailWord_4110439, baseEnd_4110439] using wordTrace_append hprefix tailTrace_4110439
  have hstable : (prefixWord ++ tailWord_4110439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110439).length < 2 ^ (prefixWord ++ tailWord_4110439).sum := by decide
  have hdescent : baseEnd_4110439 < baseStart_4110439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110510 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4110510 : Nat := 118140960795 + 4110510 * 2 ^ 59
def prefixEnd_4110510 : Nat := 4983230072969 + 3 ^ 40 * 4110510 * 2
def baseEnd_4110510 : Nat := 703555788370939281473705

theorem tailTrace_4110510 : CollatzResearch.WordTrace tailWord_4110510 prefixEnd_4110510 703555788370939281473705 := by
  unfold tailWord_4110510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740327042291470507813123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99948410892221176041669989 18740327042291470507813123)
  ·
    refine ⟨28110490563437205761719685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18740327042291470507813123 28110490563437205761719685)
    ·
      refine ⟨5270716980644476080322441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28110490563437205761719685 5270716980644476080322441)
      ·
        refine ⟨3953037735483357060241831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5270716980644476080322441 3953037735483357060241831)
        ·
          refine ⟨5929556603225035590362747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953037735483357060241831 5929556603225035590362747)
          ·
            refine ⟨8894334904837553385544121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929556603225035590362747 8894334904837553385544121)
            ·
              refine ⟨6670751178628165039158091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8894334904837553385544121 6670751178628165039158091)
              ·
                refine ⟨10006126767942247558737137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670751178628165039158091 10006126767942247558737137)
                ·
                  refine ⟨7504595075956685669052853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006126767942247558737137 7504595075956685669052853)
                  ·
                    refine ⟨703555788370939281473705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7504595075956685669052853 703555788370939281473705)
                    ·
                      rfl

theorem cell23_4110510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4110510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110510 prefixEnd_4110510 := by exact prefixLift 4110510
  have htrace : WordTrace (prefixWord ++ tailWord_4110510) baseStart_4110510 baseEnd_4110510 := by
    simpa [prefixWord, tailWord_4110510, baseEnd_4110510] using wordTrace_append hprefix tailTrace_4110510
  have hstable : (prefixWord ++ tailWord_4110510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110510).length < 2 ^ (prefixWord ++ tailWord_4110510).sum := by decide
  have hdescent : baseEnd_4110510 < baseStart_4110510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110512 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_4110512 : Nat := 118140960795 + 4110512 * 2 ^ 59
def prefixEnd_4110512 : Nat := 4983230072969 + 3 ^ 40 * 4110512 * 2
def baseEnd_4110512 : Nat := 2110668392074126836596105

theorem tailTrace_4110512 : CollatzResearch.WordTrace tailWord_4110512 prefixEnd_4110512 2110668392074126836596105 := by
  unfold tailWord_4110512
  simp only [CollatzResearch.WordTrace]
  refine ⟨74961344642162259202038895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99948459522883012269385193 74961344642162259202038895)
  ·
    refine ⟨112442016963243388803058343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74961344642162259202038895 112442016963243388803058343)
    ·
      refine ⟨168663025444865083204587515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112442016963243388803058343 168663025444865083204587515)
      ·
        refine ⟨252994538167297624806881273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168663025444865083204587515 252994538167297624806881273)
        ·
          refine ⟨189745903625473218605160955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252994538167297624806881273 189745903625473218605160955)
          ·
            refine ⟨284618855438209827907741433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189745903625473218605160955 284618855438209827907741433)
            ·
              refine ⟨213464141578657370930806075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284618855438209827907741433 213464141578657370930806075)
              ·
                refine ⟨320196212367986056396209113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213464141578657370930806075 320196212367986056396209113)
                ·
                  refine ⟨240147159275989542297156835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320196212367986056396209113 240147159275989542297156835)
                  ·
                    refine ⟨360220738913984313445735253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 240147159275989542297156835 360220738913984313445735253)
                    ·
                      refine ⟨2110668392074126836596105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 360220738913984313445735253 2110668392074126836596105)
                      ·
                        rfl

theorem cell23_4110512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_4110512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110512 prefixEnd_4110512 := by exact prefixLift 4110512
  have htrace : WordTrace (prefixWord ++ tailWord_4110512) baseStart_4110512 baseEnd_4110512 := by
    simpa [prefixWord, tailWord_4110512, baseEnd_4110512] using wordTrace_append hprefix tailTrace_4110512
  have hstable : (prefixWord ++ tailWord_4110512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110512).length < 2 ^ (prefixWord ++ tailWord_4110512).sum := by decide
  have hdescent : baseEnd_4110512 < baseStart_4110512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110513 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4110513 : Nat := 118140960795 + 4110513 * 2 ^ 59
def prefixEnd_4110513 : Nat := 4983230072969 + 3 ^ 40 * 4110513 * 2
def baseEnd_4110513 : Nat := 2110668905554781332683601

theorem tailTrace_4110513 : CollatzResearch.WordTrace tailWord_4110513 prefixEnd_4110513 2110668905554781332683601 := by
  unfold tailWord_4110513
  simp only [CollatzResearch.WordTrace]
  refine ⟨149922725757320895574864193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99948483838213930383242795 149922725757320895574864193)
  ·
    refine ⟨112442044317990671681148145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149922725757320895574864193 112442044317990671681148145)
    ·
      refine ⟨84331533238493003760861109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112442044317990671681148145 84331533238493003760861109)
      ·
        refine ⟨7906081241108719102580729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84331533238493003760861109 7906081241108719102580729)
        ·
          refine ⟨5929560930831539326935547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7906081241108719102580729 5929560930831539326935547)
          ·
            refine ⟨8894341396247308990403321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929560930831539326935547 8894341396247308990403321)
            ·
              refine ⟨6670756047185481742802491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8894341396247308990403321 6670756047185481742802491)
              ·
                refine ⟨10006134070778222614203737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6670756047185481742802491 10006134070778222614203737)
                ·
                  refine ⟨7504600553083666960652803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006134070778222614203737 7504600553083666960652803)
                  ·
                    refine ⟨11256900829625500440979205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504600553083666960652803 11256900829625500440979205)
                    ·
                      refine ⟨2110668905554781332683601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11256900829625500440979205 2110668905554781332683601)
                      ·
                        rfl

theorem cell23_4110513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4110513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110513 prefixEnd_4110513 := by exact prefixLift 4110513
  have htrace : WordTrace (prefixWord ++ tailWord_4110513) baseStart_4110513 baseEnd_4110513 := by
    simpa [prefixWord, tailWord_4110513, baseEnd_4110513] using wordTrace_append hprefix tailTrace_4110513
  have hstable : (prefixWord ++ tailWord_4110513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110513).length < 2 ^ (prefixWord ++ tailWord_4110513).sum := by decide
  have hdescent : baseEnd_4110513 < baseStart_4110513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110530 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_4110530 : Nat := 118140960795 + 4110530 * 2 ^ 59
def prefixEnd_4110530 : Nat := 4983230072969 + 3 ^ 40 * 4110530 * 2
def baseEnd_4110530 : Nat := 2110677634725907766171023

theorem tailTrace_4110530 : CollatzResearch.WordTrace tailWord_4110530 prefixEnd_4110530 2110677634725907766171023 := by
  unfold tailWord_4110530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37480836449564826869558261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99948897198839538318822029 37480836449564826869558261)
  ·
    refine ⟨3513828417146702519021087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37480836449564826869558261 3513828417146702519021087)
    ·
      refine ⟨5270742625720053778531631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3513828417146702519021087 5270742625720053778531631)
      ·
        refine ⟨7906113938580080667797447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5270742625720053778531631 7906113938580080667797447)
        ·
          refine ⟨11859170907870121001696171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906113938580080667797447 11859170907870121001696171)
          ·
            refine ⟨17788756361805181502544257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11859170907870121001696171 17788756361805181502544257)
            ·
              refine ⟨13341567271353886126908193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17788756361805181502544257 13341567271353886126908193)
              ·
                refine ⟨10006175453515414595181145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13341567271353886126908193 10006175453515414595181145)
                ·
                  refine ⟨7504631590136560946385859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10006175453515414595181145 7504631590136560946385859)
                  ·
                    refine ⟨11256947385204841419578789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7504631590136560946385859 11256947385204841419578789)
                    ·
                      refine ⟨2110677634725907766171023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11256947385204841419578789 2110677634725907766171023)
                      ·
                        rfl

theorem cell23_4110530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_4110530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110530 prefixEnd_4110530 := by exact prefixLift 4110530
  have htrace : WordTrace (prefixWord ++ tailWord_4110530) baseStart_4110530 baseEnd_4110530 := by
    simpa [prefixWord, tailWord_4110530, baseEnd_4110530] using wordTrace_append hprefix tailTrace_4110530
  have hstable : (prefixWord ++ tailWord_4110530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110530).length < 2 ^ (prefixWord ++ tailWord_4110530).sum := by decide
  have hdescent : baseEnd_4110530 < baseStart_4110530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110579 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 1, 6]
def baseStart_4110579 : Nat := 118140960795 + 4110579 * 2 ^ 59
def prefixEnd_4110579 : Nat := 4983230072969 + 3 ^ 40 * 4110579 * 2
def baseEnd_4110579 : Nat := 703567598425992691486099

theorem tailTrace_4110579 : CollatzResearch.WordTrace tailWord_4110579 prefixEnd_4110579 703567598425992691486099 := by
  unfold tailWord_4110579
  simp only [CollatzResearch.WordTrace]
  refine ⟨149925132975081788846766791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99950088650054525897844527 149925132975081788846766791)
  ·
    refine ⟨224887699462622683270150187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149925132975081788846766791 224887699462622683270150187)
    ·
      refine ⟨337331549193934024905225281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224887699462622683270150187 337331549193934024905225281)
      ·
        refine ⟨252998661895450518678918961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337331549193934024905225281 252998661895450518678918961)
        ·
          refine ⟨189748996421587889009189221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252998661895450518678918961 189748996421587889009189221)
          ·
            refine ⟨35577936829047729189222979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189748996421587889009189221 35577936829047729189222979)
            ·
              refine ⟨53366905243571593783834469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35577936829047729189222979 53366905243571593783834469)
              ·
                refine ⟨10006294733169673834468963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53366905243571593783834469 10006294733169673834468963)
                ·
                  refine ⟨15009442099754510751703445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10006294733169673834468963 15009442099754510751703445)
                  ·
                    refine ⟨703567598425992691486099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15009442099754510751703445 703567598425992691486099)
                    ·
                      rfl

theorem cell23_4110579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 6].length) (baseStart_4110579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110579 prefixEnd_4110579 := by exact prefixLift 4110579
  have htrace : WordTrace (prefixWord ++ tailWord_4110579) baseStart_4110579 baseEnd_4110579 := by
    simpa [prefixWord, tailWord_4110579, baseEnd_4110579] using wordTrace_append hprefix tailTrace_4110579
  have hstable : (prefixWord ++ tailWord_4110579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110579).length < 2 ^ (prefixWord ++ tailWord_4110579).sum := by decide
  have hdescent : baseEnd_4110579 < baseStart_4110579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110589 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_4110589 : Nat := 118140960795 + 4110589 * 2 ^ 59
def prefixEnd_4110589 : Nat := 4983230072969 + 3 ^ 40 * 4110589 * 2
def baseEnd_4110589 : Nat := 2110707930084523035333251

theorem tailTrace_4110589 : CollatzResearch.WordTrace tailWord_4110589 prefixEnd_4110589 2110707930084523035333251 := by
  unfold tailWord_4110589
  simp only [CollatzResearch.WordTrace]
  refine ⟨149925497705045560554630821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99950331803363707036420547 149925497705045560554630821)
  ·
    refine ⟨28111030819696042603993279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149925497705045560554630821 28111030819696042603993279)
    ·
      refine ⟨42166546229544063905989919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28111030819696042603993279 42166546229544063905989919)
      ·
        refine ⟨63249819344316095858984879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42166546229544063905989919 63249819344316095858984879)
        ·
          refine ⟨94874729016474143788477319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63249819344316095858984879 94874729016474143788477319)
          ·
            refine ⟨142312093524711215682715979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94874729016474143788477319 142312093524711215682715979)
            ·
              refine ⟨213468140287066823524073969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142312093524711215682715979 213468140287066823524073969)
              ·
                refine ⟨160101105215300117643055477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213468140287066823524073969 160101105215300117643055477)
                ·
                  refine ⟨15009478613934386029036451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160101105215300117643055477 15009478613934386029036451)
                  ·
                    refine ⟨22514217920901579043554677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15009478613934386029036451 22514217920901579043554677)
                    ·
                      refine ⟨2110707930084523035333251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22514217920901579043554677 2110707930084523035333251)
                      ·
                        rfl

theorem cell23_4110589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_4110589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110589 prefixEnd_4110589 := by exact prefixLift 4110589
  have htrace : WordTrace (prefixWord ++ tailWord_4110589) baseStart_4110589 baseEnd_4110589 := by
    simpa [prefixWord, tailWord_4110589, baseEnd_4110589] using wordTrace_append hprefix tailTrace_4110589
  have hstable : (prefixWord ++ tailWord_4110589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110589).length < 2 ^ (prefixWord ++ tailWord_4110589).sum := by decide
  have hdescent : baseEnd_4110589 < baseStart_4110589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110606 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4110606 : Nat := 118140960795 + 4110606 * 2 ^ 59
def prefixEnd_4110606 : Nat := 4983230072969 + 3 ^ 40 * 4110606 * 2
def baseEnd_4110606 : Nat := 2110716659255649468820673

theorem tailTrace_4110606 : CollatzResearch.WordTrace tailWord_4110606 prefixEnd_4110606 2110716659255649468820673 := by
  unfold tailWord_4110606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18740764718247996557249959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99950745163989314971999781 18740764718247996557249959)
  ·
    refine ⟨28111147077371994835874939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18740764718247996557249959 28111147077371994835874939)
    ·
      refine ⟨42166720616057992253812409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28111147077371994835874939 42166720616057992253812409)
      ·
        refine ⟨31625040462043494190359307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42166720616057992253812409 31625040462043494190359307)
        ·
          refine ⟨47437560693065241285538961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31625040462043494190359307 47437560693065241285538961)
          ·
            refine ⟨35578170519798930964154221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47437560693065241285538961 35578170519798930964154221)
            ·
              refine ⟨13341813944924599111557833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35578170519798930964154221 13341813944924599111557833)
              ·
                refine ⟨10006360458693449333668375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13341813944924599111557833 10006360458693449333668375)
                ·
                  refine ⟨15009540688040174000502563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10006360458693449333668375 15009540688040174000502563)
                  ·
                    refine ⟨22514311032060261000753845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15009540688040174000502563 22514311032060261000753845)
                    ·
                      refine ⟨2110716659255649468820673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22514311032060261000753845 2110716659255649468820673)
                      ·
                        rfl

theorem cell23_4110606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4110606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110606 prefixEnd_4110606 := by exact prefixLift 4110606
  have htrace : WordTrace (prefixWord ++ tailWord_4110606) baseStart_4110606 baseEnd_4110606 := by
    simpa [prefixWord, tailWord_4110606, baseEnd_4110606] using wordTrace_append hprefix tailTrace_4110606
  have hstable : (prefixWord ++ tailWord_4110606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110606).length < 2 ^ (prefixWord ++ tailWord_4110606).sum := by decide
  have hdescent : baseEnd_4110606 < baseStart_4110606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110623 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 3]
def baseStart_4110623 : Nat := 118140960795 + 4110623 * 2 ^ 59
def prefixEnd_4110623 : Nat := 4983230072969 + 3 ^ 40 * 4110623 * 2
def baseEnd_4110623 : Nat := 2110725388426775902308095

theorem tailTrace_4110623 : CollatzResearch.WordTrace tailWord_4110623 prefixEnd_4110623 2110725388426775902308095 := by
  unfold tailWord_4110623
  simp only [CollatzResearch.WordTrace]
  refine ⟨149926737786922384361368523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99951158524614922907579015 149926737786922384361368523)
  ·
    refine ⟨224890106680383576542052785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149926737786922384361368523 224890106680383576542052785)
    ·
      refine ⟨168667580010287682406539589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224890106680383576542052785 168667580010287682406539589)
      ·
        refine ⟨31625171251928940451226173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168667580010287682406539589 31625171251928940451226173)
        ·
          refine ⟨11859439219473352669209815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31625171251928940451226173 11859439219473352669209815)
          ·
            refine ⟨17789158829210029003814723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11859439219473352669209815 17789158829210029003814723)
            ·
              refine ⟨26683738243815043505722085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17789158829210029003814723 26683738243815043505722085)
              ·
                refine ⟨5003200920715320657322891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26683738243815043505722085 5003200920715320657322891)
                ·
                  refine ⟨7504801381072980985984337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003200920715320657322891 7504801381072980985984337)
                  ·
                    refine ⟨5628601035804735739488253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7504801381072980985984337 5628601035804735739488253)
                    ·
                      refine ⟨2110725388426775902308095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628601035804735739488253 2110725388426775902308095)
                      ·
                        rfl

theorem cell23_4110623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_4110623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110623 prefixEnd_4110623 := by exact prefixLift 4110623
  have htrace : WordTrace (prefixWord ++ tailWord_4110623) baseStart_4110623 baseEnd_4110623 := by
    simpa [prefixWord, tailWord_4110623, baseEnd_4110623] using wordTrace_append hprefix tailTrace_4110623
  have hstable : (prefixWord ++ tailWord_4110623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110623).length < 2 ^ (prefixWord ++ tailWord_4110623).sum := by decide
  have hdescent : baseEnd_4110623 < baseStart_4110623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110626 : List Nat := [3, 3, 1, 1, 3, 2, 1, 9]
def baseStart_4110626 : Nat := 118140960795 + 4110626 * 2 ^ 59
def prefixEnd_4110626 : Nat := 4983230072969 + 3 ^ 40 * 4110626 * 2
def baseEnd_4110626 : Nat := 78175071439582940391503

theorem tailTrace_4110626 : CollatzResearch.WordTrace tailWord_4110626 prefixEnd_4110626 78175071439582940391503 := by
  unfold tailWord_4110626
  simp only [CollatzResearch.WordTrace]
  refine ⟨37481711801477878968431933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99951231470607677249151821 37481711801477878968431933)
  ·
    refine ⟨14055641925554204613161975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37481711801477878968431933 14055641925554204613161975)
    ·
      refine ⟨21083462888331306919742963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14055641925554204613161975 21083462888331306919742963)
      ·
        refine ⟨31625194332496960379614445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21083462888331306919742963 31625194332496960379614445)
        ·
          refine ⟨11859447874686360142355417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31625194332496960379614445 11859447874686360142355417)
          ·
            refine ⟨8894585906014770106766563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11859447874686360142355417 8894585906014770106766563)
            ·
              refine ⟨13341878859022155160149845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8894585906014770106766563 13341878859022155160149845)
              ·
                refine ⟨78175071439582940391503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13341878859022155160149845 78175071439582940391503)
                ·
                  rfl

theorem cell23_4110626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_4110626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110626 prefixEnd_4110626 := by exact prefixLift 4110626
  have htrace : WordTrace (prefixWord ++ tailWord_4110626) baseStart_4110626 baseEnd_4110626 := by
    simpa [prefixWord, tailWord_4110626, baseEnd_4110626] using wordTrace_append hprefix tailTrace_4110626
  have hstable : (prefixWord ++ tailWord_4110626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110626).length < 2 ^ (prefixWord ++ tailWord_4110626).sum := by decide
  have hdescent : baseEnd_4110626 < baseStart_4110626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110636 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_4110636 : Nat := 118140960795 + 4110636 * 2 ^ 59
def prefixEnd_4110636 : Nat := 4983230072969 + 3 ^ 40 * 4110636 * 2
def baseEnd_4110636 : Nat := 2110732063675284351445535

theorem tailTrace_4110636 : CollatzResearch.WordTrace tailWord_4110636 prefixEnd_4110636 2110732063675284351445535 := by
  unfold tailWord_4110636
  simp only [CollatzResearch.WordTrace]
  refine ⟨74963605967937643790795881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99951474623916858387727841 74963605967937643790795881)
  ·
    refine ⟨56222704475953232843096911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74963605967937643790795881 56222704475953232843096911)
    ·
      refine ⟨84334056713929849264645367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56222704475953232843096911 84334056713929849264645367)
      ·
        refine ⟨126501085070894773896968051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84334056713929849264645367 126501085070894773896968051)
        ·
          refine ⟨189751627606342160845452077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126501085070894773896968051 189751627606342160845452077)
          ·
            refine ⟨71156860352378310317044529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189751627606342160845452077 71156860352378310317044529)
            ·
              refine ⟨53367645264283732737783397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71156860352378310317044529 53367645264283732737783397)
              ·
                refine ⟨10006433487053199888334387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53367645264283732737783397 10006433487053199888334387)
                ·
                  refine ⟨15009650230579799832501581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10006433487053199888334387 15009650230579799832501581)
                  ·
                    refine ⟨5628618836467424937188093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15009650230579799832501581 5628618836467424937188093)
                    ·
                      refine ⟨2110732063675284351445535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628618836467424937188093 2110732063675284351445535)
                      ·
                        rfl

theorem cell23_4110636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_4110636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110636 prefixEnd_4110636 := by exact prefixLift 4110636
  have htrace : WordTrace (prefixWord ++ tailWord_4110636) baseStart_4110636 baseEnd_4110636 := by
    simpa [prefixWord, tailWord_4110636, baseEnd_4110636] using wordTrace_append hprefix tailTrace_4110636
  have hstable : (prefixWord ++ tailWord_4110636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110636).length < 2 ^ (prefixWord ++ tailWord_4110636).sum := by decide
  have hdescent : baseEnd_4110636 < baseStart_4110636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110663 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_4110663 : Nat := 118140960795 + 4110663 * 2 ^ 59
def prefixEnd_4110663 : Nat := 4983230072969 + 3 ^ 40 * 4110663 * 2
def baseEnd_4110663 : Nat := 2110745927652955745807911

theorem tailTrace_4110663 : CollatzResearch.WordTrace tailWord_4110663 prefixEnd_4110663 2110745927652955745807911 := by
  unfold tailWord_4110663
  simp only [CollatzResearch.WordTrace]
  refine ⟨149928196706777471192824643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99952131137851647461883095 149928196706777471192824643)
  ·
    refine ⟨224892295060166206789236965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149928196706777471192824643 224892295060166206789236965)
    ·
      refine ⟨42167305323781163772981931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224892295060166206789236965 42167305323781163772981931)
      ·
        refine ⟨63250957985671745659472897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42167305323781163772981931 63250957985671745659472897)
        ·
          refine ⟨47438218489253809244604673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63250957985671745659472897 47438218489253809244604673)
          ·
            refine ⟨35578663866940356933453505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47438218489253809244604673 35578663866940356933453505)
            ·
              refine ⟨26683997900205267700090129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35578663866940356933453505 26683997900205267700090129)
              ·
                refine ⟨20012998425153950775067597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26683997900205267700090129 20012998425153950775067597)
                ·
                  refine ⟨7504874409432731540650349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20012998425153950775067597 7504874409432731540650349)
                  ·
                    refine ⟨2814327903537274327743881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7504874409432731540650349 2814327903537274327743881)
                    ·
                      refine ⟨2110745927652955745807911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814327903537274327743881 2110745927652955745807911)
                      ·
                        rfl

theorem cell23_4110663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_4110663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110663 prefixEnd_4110663 := by exact prefixLift 4110663
  have htrace : WordTrace (prefixWord ++ tailWord_4110663) baseStart_4110663 baseEnd_4110663 := by
    simpa [prefixWord, tailWord_4110663, baseEnd_4110663] using wordTrace_append hprefix tailTrace_4110663
  have hstable : (prefixWord ++ tailWord_4110663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110663).length < 2 ^ (prefixWord ++ tailWord_4110663).sum := by decide
  have hdescent : baseEnd_4110663 < baseStart_4110663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110693 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 3, 4, 2]
def baseStart_4110693 : Nat := 118140960795 + 4110693 * 2 ^ 59
def prefixEnd_4110693 : Nat := 4983230072969 + 3 ^ 40 * 4110693 * 2
def baseEnd_4110693 : Nat := 2110761332072590628432773

theorem tailTrace_4110693 : CollatzResearch.WordTrace tailWord_4110693 prefixEnd_4110693 2110761332072590628432773 := by
  unfold tailWord_4110693
  simp only [CollatzResearch.WordTrace]
  refine ⟨149929290896668786316416733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99952860597779190877611155 149929290896668786316416733)
  ·
    refine ⟨56223484086250794868656275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149929290896668786316416733 56223484086250794868656275)
    ·
      refine ⟨84335226129376192302984413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56223484086250794868656275 84335226129376192302984413)
      ·
        refine ⟨31625709798516072113619155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84335226129376192302984413 31625709798516072113619155)
        ·
          refine ⟨47438564697774108170428733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31625709798516072113619155 47438564697774108170428733)
          ·
            refine ⟨17789461761665290563910775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47438564697774108170428733 17789461761665290563910775)
            ·
              refine ⟨26684192642497935845866163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17789461761665290563910775 26684192642497935845866163)
              ·
                refine ⟨40026288963746903768799245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26684192642497935845866163 40026288963746903768799245)
                ·
                  refine ⟨15009858361405088913299717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40026288963746903768799245 15009858361405088913299717)
                  ·
                    refine ⟨2814348442763454171243697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15009858361405088913299717 2814348442763454171243697)
                    ·
                      refine ⟨2110761332072590628432773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814348442763454171243697 2110761332072590628432773)
                      ·
                        rfl

theorem cell23_4110693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_4110693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110693 prefixEnd_4110693 := by exact prefixLift 4110693
  have htrace : WordTrace (prefixWord ++ tailWord_4110693) baseStart_4110693 baseEnd_4110693 := by
    simpa [prefixWord, tailWord_4110693, baseEnd_4110693] using wordTrace_append hprefix tailTrace_4110693
  have hstable : (prefixWord ++ tailWord_4110693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110693).length < 2 ^ (prefixWord ++ tailWord_4110693).sum := by decide
  have hdescent : baseEnd_4110693 < baseStart_4110693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110699 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 9]
def baseStart_4110699 : Nat := 118140960795 + 4110699 * 2 ^ 59
def prefixEnd_4110699 : Nat := 4983230072969 + 3 ^ 40 * 4110699 * 2
def baseEnd_4110699 : Nat := 234529379217390844995305

theorem tailTrace_4110699 : CollatzResearch.WordTrace tailWord_4110699 prefixEnd_4110699 234529379217390844995305 := by
  unfold tailWord_4110699
  simp only [CollatzResearch.WordTrace]
  refine ⟨149929509734647049341135151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99953006489764699560756767 149929509734647049341135151)
  ·
    refine ⟨224894264601970574011702727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149929509734647049341135151 224894264601970574011702727)
    ·
      refine ⟨337341396902955861017554091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224894264601970574011702727 337341396902955861017554091)
      ·
        refine ⟨506012095354433791526331137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337341396902955861017554091 506012095354433791526331137)
        ·
          refine ⟨379509071515825343644748353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506012095354433791526331137 379509071515825343644748353)
          ·
            refine ⟨284631803636869007733561265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379509071515825343644748353 284631803636869007733561265)
            ·
              refine ⟨213473852727651755800170949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284631803636869007733561265 213473852727651755800170949)
              ·
                refine ⟨40026347386434704212532053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213473852727651755800170949 40026347386434704212532053)
                ·
                  refine ⟨234529379217390844995305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40026347386434704212532053 234529379217390844995305)
                  ·
                    rfl

theorem cell23_4110699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 9].length) (baseStart_4110699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110699 prefixEnd_4110699 := by exact prefixLift 4110699
  have htrace : WordTrace (prefixWord ++ tailWord_4110699) baseStart_4110699 baseEnd_4110699 := by
    simpa [prefixWord, tailWord_4110699, baseEnd_4110699] using wordTrace_append hprefix tailTrace_4110699
  have hstable : (prefixWord ++ tailWord_4110699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110699).length < 2 ^ (prefixWord ++ tailWord_4110699).sum := by decide
  have hdescent : baseEnd_4110699 < baseStart_4110699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110723 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 4]
def baseStart_4110723 : Nat := 118140960795 + 4110723 * 2 ^ 59
def prefixEnd_4110723 : Nat := 4983230072969 + 3 ^ 40 * 4110723 * 2
def baseEnd_4110723 : Nat := 2110776736492225511057635

theorem tailTrace_4110723 : CollatzResearch.WordTrace tailWord_4110723 prefixEnd_4110723 2110776736492225511057635 := by
  unfold tailWord_4110723
  simp only [CollatzResearch.WordTrace]
  refine ⟨149930385086560101440008823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99953590057706734293339215 149930385086560101440008823)
  ·
    refine ⟨224895577629840152160013235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149930385086560101440008823 224895577629840152160013235)
    ·
      refine ⟨337343366444760228240019853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224895577629840152160013235 337343366444760228240019853)
      ·
        refine ⟨126503762416785085590007445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337343366444760228240019853 126503762416785085590007445)
        ·
          refine ⟨5929863863286800887031599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126503762416785085590007445 5929863863286800887031599)
          ·
            refine ⟨8894795794930201330547399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929863863286800887031599 8894795794930201330547399)
            ·
              refine ⟨13342193692395301995821099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8894795794930201330547399 13342193692395301995821099)
              ·
                refine ⟨20013290538592952993731649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13342193692395301995821099 20013290538592952993731649)
                ·
                  refine ⟨15009967903944714745298737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20013290538592952993731649 15009967903944714745298737)
                  ·
                    refine ⟨11257475927958536058974053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15009967903944714745298737 11257475927958536058974053)
                    ·
                      refine ⟨2110776736492225511057635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11257475927958536058974053 2110776736492225511057635)
                      ·
                        rfl

theorem cell23_4110723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_4110723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110723 prefixEnd_4110723 := by exact prefixLift 4110723
  have htrace : WordTrace (prefixWord ++ tailWord_4110723) baseStart_4110723 baseEnd_4110723 := by
    simpa [prefixWord, tailWord_4110723, baseEnd_4110723] using wordTrace_append hprefix tailTrace_4110723
  have hstable : (prefixWord ++ tailWord_4110723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110723).length < 2 ^ (prefixWord ++ tailWord_4110723).sum := by decide
  have hdescent : baseEnd_4110723 < baseStart_4110723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110756 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_4110756 : Nat := 118140960795 + 4110756 * 2 ^ 59
def prefixEnd_4110756 : Nat := 4983230072969 + 3 ^ 40 * 4110756 * 2
def baseEnd_4110756 : Nat := 2110793681353823881944983

theorem tailTrace_4110756 : CollatzResearch.WordTrace tailWord_4110756 prefixEnd_4110756 2110793681353823881944983 := by
  unfold tailWord_4110756
  simp only [CollatzResearch.WordTrace]
  refine ⟨74965794347720274037980061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99954392463627032050640081 74965794347720274037980061)
  ·
    refine ⟨28112172880395102764242523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74965794347720274037980061 28112172880395102764242523)
    ·
      refine ⟨42168259320592654146363785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28112172880395102764242523 42168259320592654146363785)
      ·
        refine ⟨31626194490444490609772839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42168259320592654146363785 31626194490444490609772839)
        ·
          refine ⟨47439291735666735914659259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31626194490444490609772839 47439291735666735914659259)
          ·
            refine ⟨71158937603500103871988889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47439291735666735914659259 71158937603500103871988889)
            ·
              refine ⟨53369203202625077903991667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71158937603500103871988889 53369203202625077903991667)
              ·
                refine ⟨80053804803937616855987501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53369203202625077903991667 80053804803937616855987501)
                ·
                  refine ⟨30020176801476606320995313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80053804803937616855987501 30020176801476606320995313)
                  ·
                    refine ⟨22515132601107454740746485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30020176801476606320995313 22515132601107454740746485)
                    ·
                      refine ⟨2110793681353823881944983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22515132601107454740746485 2110793681353823881944983)
                      ·
                        rfl

theorem cell23_4110756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_4110756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110756 prefixEnd_4110756 := by exact prefixLift 4110756
  have htrace : WordTrace (prefixWord ++ tailWord_4110756) baseStart_4110756 baseEnd_4110756 := by
    simpa [prefixWord, tailWord_4110756, baseEnd_4110756] using wordTrace_append hprefix tailTrace_4110756
  have hstable : (prefixWord ++ tailWord_4110756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110756).length < 2 ^ (prefixWord ++ tailWord_4110756).sum := by decide
  have hdescent : baseEnd_4110756 < baseStart_4110756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110760 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4110760 : Nat := 118140960795 + 4110760 * 2 ^ 59
def prefixEnd_4110760 : Nat := 4983230072969 + 3 ^ 40 * 4110760 * 2
def baseEnd_4110760 : Nat := 2110795735276441866294965

theorem tailTrace_4110760 : CollatzResearch.WordTrace tailWord_4110760 prefixEnd_4110760 2110795735276441866294965 := by
  unfold tailWord_4110760
  simp only [CollatzResearch.WordTrace]
  refine ⟨74965867293713028379552867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99954489724950704506070489 74965867293713028379552867)
  ·
    refine ⟨112448800940569542569329301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74965867293713028379552867 112448800940569542569329301)
    ·
      refine ⟨5271037544089197307937311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112448800940569542569329301 5271037544089197307937311)
      ·
        refine ⟨7906556316133795961905967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271037544089197307937311 7906556316133795961905967)
        ·
          refine ⟨11859834474200693942858951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906556316133795961905967 11859834474200693942858951)
          ·
            refine ⟨17789751711301040914288427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11859834474200693942858951 17789751711301040914288427)
            ·
              refine ⟨26684627566951561371432641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17789751711301040914288427 26684627566951561371432641)
              ·
                refine ⟨20013470675213671028574481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26684627566951561371432641 20013470675213671028574481)
                ·
                  refine ⟨15010103006410253271430861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20013470675213671028574481 15010103006410253271430861)
                  ·
                    refine ⟨5628788627403844976786573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15010103006410253271430861 5628788627403844976786573)
                    ·
                      refine ⟨2110795735276441866294965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628788627403844976786573 2110795735276441866294965)
                      ·
                        rfl

theorem cell23_4110760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4110760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110760 prefixEnd_4110760 := by exact prefixLift 4110760
  have htrace : WordTrace (prefixWord ++ tailWord_4110760) baseStart_4110760 baseEnd_4110760 := by
    simpa [prefixWord, tailWord_4110760, baseEnd_4110760] using wordTrace_append hprefix tailTrace_4110760
  have hstable : (prefixWord ++ tailWord_4110760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110760).length < 2 ^ (prefixWord ++ tailWord_4110760).sum := by decide
  have hdescent : baseEnd_4110760 < baseStart_4110760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110793 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 3, 4]
def baseStart_4110793 : Nat := 118140960795 + 4110793 * 2 ^ 59
def prefixEnd_4110793 : Nat := 4983230072969 + 3 ^ 40 * 4110793 * 2
def baseEnd_4110793 : Nat := 703604226712680079060771

theorem tailTrace_4110793 : CollatzResearch.WordTrace tailWord_4110793 prefixEnd_4110793 703604226712680079060771 := by
  unfold tailWord_4110793
  simp only [CollatzResearch.WordTrace]
  refine ⟨149932938196306503395057033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99955292130871002263371355 149932938196306503395057033)
  ·
    refine ⟨112449703647229877546292775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149932938196306503395057033 112449703647229877546292775)
    ·
      refine ⟨168674555470844816319439163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112449703647229877546292775 168674555470844816319439163)
      ·
        refine ⟨253011833206267224479158745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168674555470844816319439163 253011833206267224479158745)
        ·
          refine ⟨189758874904700418359369059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253011833206267224479158745 189758874904700418359369059)
          ·
            refine ⟨284638312357050627539053589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189758874904700418359369059 284638312357050627539053589)
            ·
              refine ⟨13342420891736748165893137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284638312357050627539053589 13342420891736748165893137)
              ·
                refine ⟨10006815668802561124419853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13342420891736748165893137 10006815668802561124419853)
                ·
                  refine ⟨3752555875800960421657445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10006815668802561124419853 3752555875800960421657445)
                  ·
                    refine ⟨703604226712680079060771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752555875800960421657445 703604226712680079060771)
                    ·
                      rfl

theorem cell23_4110793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_4110793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110793 prefixEnd_4110793 := by exact prefixLift 4110793
  have htrace : WordTrace (prefixWord ++ tailWord_4110793) baseStart_4110793 baseEnd_4110793 := by
    simpa [prefixWord, tailWord_4110793, baseEnd_4110793] using wordTrace_append hprefix tailTrace_4110793
  have hstable : (prefixWord ++ tailWord_4110793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110793).length < 2 ^ (prefixWord ++ tailWord_4110793).sum := by decide
  have hdescent : baseEnd_4110793 < baseStart_4110793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110823 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 6]
def baseStart_4110823 : Nat := 118140960795 + 4110823 * 2 ^ 59
def prefixEnd_4110823 : Nat := 4983230072969 + 3 ^ 40 * 4110823 * 2
def baseEnd_4110823 : Nat := 234536453839741679978575

theorem tailTrace_4110823 : CollatzResearch.WordTrace tailWord_4110823 prefixEnd_4110823 234536453839741679978575 := by
  unfold tailWord_4110823
  simp only [CollatzResearch.WordTrace]
  refine ⟨149934032386197818518649123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99956021590798545679099415 149934032386197818518649123)
  ·
    refine ⟨224901048579296727777973685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149934032386197818518649123 224901048579296727777973685)
    ·
      refine ⟨21084473304309068229185033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224901048579296727777973685 21084473304309068229185033)
      ·
        refine ⟨15813354978231801171888775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21084473304309068229185033 15813354978231801171888775)
        ·
          refine ⟨23720032467347701757833163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813354978231801171888775 23720032467347701757833163)
          ·
            refine ⟨35580048701021552636749745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23720032467347701757833163 35580048701021552636749745)
            ·
              refine ⟨26685036525766164477562309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35580048701021552636749745 26685036525766164477562309)
              ·
                refine ⟨5003444348581155839542933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26685036525766164477562309 5003444348581155839542933)
                ·
                  refine ⟨234536453839741679978575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5003444348581155839542933 234536453839741679978575)
                  ·
                    rfl

theorem cell23_4110823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 6].length) (baseStart_4110823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110823 prefixEnd_4110823 := by exact prefixLift 4110823
  have htrace : WordTrace (prefixWord ++ tailWord_4110823) baseStart_4110823 baseEnd_4110823 := by
    simpa [prefixWord, tailWord_4110823, baseEnd_4110823] using wordTrace_append hprefix tailTrace_4110823
  have hstable : (prefixWord ++ tailWord_4110823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110823).length < 2 ^ (prefixWord ++ tailWord_4110823).sum := by decide
  have hdescent : baseEnd_4110823 < baseStart_4110823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110827 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 1, 4]
def baseStart_4110827 : Nat := 118140960795 + 4110827 * 2 ^ 59
def prefixEnd_4110827 : Nat := 4983230072969 + 3 ^ 40 * 4110827 * 2
def baseEnd_4110827 : Nat := 703610046160097701385719

theorem tailTrace_4110827 : CollatzResearch.WordTrace tailWord_4110827 prefixEnd_4110827 703610046160097701385719 := by
  unfold tailWord_4110827
  simp only [CollatzResearch.WordTrace]
  refine ⟨149934178278183327201794735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99956118852122218134529823 149934178278183327201794735)
  ·
    refine ⟨224901267417274990802692103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149934178278183327201794735 224901267417274990802692103)
    ·
      refine ⟨337351901125912486204038155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224901267417274990802692103 337351901125912486204038155)
      ·
        refine ⟨506027851688868729306057233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337351901125912486204038155 506027851688868729306057233)
        ·
          refine ⟨379520888766651546979542925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506027851688868729306057233 379520888766651546979542925)
          ·
            refine ⟨142320333287494330117328597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379520888766651546979542925 142320333287494330117328597)
            ·
              refine ⟨3335632811425648362124889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142320333287494330117328597 3335632811425648362124889)
              ·
                refine ⟨2501724608569236271593667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335632811425648362124889 2501724608569236271593667)
                ·
                  refine ⟨3752586912853854407390501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501724608569236271593667 3752586912853854407390501)
                  ·
                    refine ⟨703610046160097701385719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752586912853854407390501 703610046160097701385719)
                    ·
                      rfl

theorem cell23_4110827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 4].length) (baseStart_4110827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110827 prefixEnd_4110827 := by exact prefixLift 4110827
  have htrace : WordTrace (prefixWord ++ tailWord_4110827) baseStart_4110827 baseEnd_4110827 := by
    simpa [prefixWord, tailWord_4110827, baseEnd_4110827] using wordTrace_append hprefix tailTrace_4110827
  have hstable : (prefixWord ++ tailWord_4110827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110827).length < 2 ^ (prefixWord ++ tailWord_4110827).sum := by decide
  have hdescent : baseEnd_4110827 < baseStart_4110827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110867 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 1, 1, 3]
def baseStart_4110867 : Nat := 118140960795 + 4110867 * 2 ^ 59
def prefixEnd_4110867 : Nat := 4983230072969 + 3 ^ 40 * 4110867 * 2
def baseEnd_4110867 : Nat := 2110850677706472947656973

theorem tailTrace_4110867 : CollatzResearch.WordTrace tailWord_4110867 prefixEnd_4110867 2110850677706472947656973 := by
  unfold tailWord_4110867
  simp only [CollatzResearch.WordTrace]
  refine ⟨149935637198038414033250855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99957091465358942688833903 149935637198038414033250855)
  ·
    refine ⟨224903455797057621049876283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149935637198038414033250855 224903455797057621049876283)
    ·
      refine ⟨337355183695586431574814425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224903455797057621049876283 337355183695586431574814425)
      ·
        refine ⟨253016387771689823681110819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337355183695586431574814425 253016387771689823681110819)
        ·
          refine ⟨379524581657534735521666229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253016387771689823681110819 379524581657534735521666229)
          ·
            refine ⟨35580429530393881455156209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 379524581657534735521666229 35580429530393881455156209)
            ·
              refine ⟨26685322147795411091367157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35580429530393881455156209 26685322147795411091367157)
              ·
                refine ⟨2501748951355819789815671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26685322147795411091367157 2501748951355819789815671)
                ·
                  refine ⟨3752623427033729684723507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501748951355819789815671 3752623427033729684723507)
                  ·
                    refine ⟨5628935140550594527085261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752623427033729684723507 5628935140550594527085261)
                    ·
                      refine ⟨2110850677706472947656973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5628935140550594527085261 2110850677706472947656973)
                      ·
                        rfl

theorem cell23_4110867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 1, 3].length) (baseStart_4110867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110867 prefixEnd_4110867 := by exact prefixLift 4110867
  have htrace : WordTrace (prefixWord ++ tailWord_4110867) baseStart_4110867 baseEnd_4110867 := by
    simpa [prefixWord, tailWord_4110867, baseEnd_4110867] using wordTrace_append hprefix tailTrace_4110867
  have hstable : (prefixWord ++ tailWord_4110867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110867).length < 2 ^ (prefixWord ++ tailWord_4110867).sum := by decide
  have hdescent : baseEnd_4110867 < baseStart_4110867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110877 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_4110877 : Nat := 118140960795 + 4110877 * 2 ^ 59
def prefixEnd_4110877 : Nat := 4983230072969 + 3 ^ 40 * 4110877 * 2
def baseEnd_4110877 : Nat := 2110855812513017908531927

theorem tailTrace_4110877 : CollatzResearch.WordTrace tailWord_4110877 prefixEnd_4110877 2110855812513017908531927 := by
  unfold tailWord_4110877
  simp only [CollatzResearch.WordTrace]
  refine ⟨149936001928002185741114885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99957334618668123827409923 149936001928002185741114885)
  ·
    refine ⟨28113000361500409826459041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149936001928002185741114885 28113000361500409826459041)
    ·
      refine ⟨21084750271125307369844281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28113000361500409826459041 21084750271125307369844281)
      ·
        refine ⟨15813562703343980527383211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21084750271125307369844281 15813562703343980527383211)
        ·
          refine ⟨23720344055015970791074817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813562703343980527383211 23720344055015970791074817)
          ·
            refine ⟨17790258041261978093306113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23720344055015970791074817 17790258041261978093306113)
            ·
              refine ⟨13342693530946483569979585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17790258041261978093306113 13342693530946483569979585)
              ·
                refine ⟨10007020148209862677484689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13342693530946483569979585 10007020148209862677484689)
                ·
                  refine ⟨7505265111157397008113517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10007020148209862677484689 7505265111157397008113517)
                  ·
                    refine ⟨2814474416684023878042569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7505265111157397008113517 2814474416684023878042569)
                    ·
                      refine ⟨2110855812513017908531927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814474416684023878042569 2110855812513017908531927)
                      ·
                        rfl

theorem cell23_4110877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_4110877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110877 prefixEnd_4110877 := by exact prefixLift 4110877
  have htrace : WordTrace (prefixWord ++ tailWord_4110877) baseStart_4110877 baseEnd_4110877 := by
    simpa [prefixWord, tailWord_4110877, baseEnd_4110877] using wordTrace_append hprefix tailTrace_4110877
  have hstable : (prefixWord ++ tailWord_4110877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110877).length < 2 ^ (prefixWord ++ tailWord_4110877).sum := by decide
  have hdescent : baseEnd_4110877 < baseStart_4110877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110890 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4110890 : Nat := 118140960795 + 4110890 * 2 ^ 59
def prefixEnd_4110890 : Nat := 4983230072969 + 3 ^ 40 * 4110890 * 2
def baseEnd_4110890 : Nat := 2110862487761526357669367

theorem tailTrace_4110890 : CollatzResearch.WordTrace tailWord_4110890 prefixEnd_4110890 2110862487761526357669367 := by
  unfold tailWord_4110890
  simp only [CollatzResearch.WordTrace]
  refine ⟨37484119019238772240334531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99957650717970059307558749 37484119019238772240334531)
  ·
    refine ⟨56226178528858158360501797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37484119019238772240334531 56226178528858158360501797)
    ·
      refine ⟨10542408474160904692594087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56226178528858158360501797 10542408474160904692594087)
      ·
        refine ⟨15813612711241357038891131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542408474160904692594087 15813612711241357038891131)
        ·
          refine ⟨23720419066862035558336697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15813612711241357038891131 23720419066862035558336697)
          ·
            refine ⟨17790314300146526668752523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23720419066862035558336697 17790314300146526668752523)
            ·
              refine ⟨26685471450219790003128785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17790314300146526668752523 26685471450219790003128785)
              ·
                refine ⟨20014103587664842502346589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26685471450219790003128785 20014103587664842502346589)
                ·
                  refine ⟨7505288845374315938379971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20014103587664842502346589 7505288845374315938379971)
                  ·
                    refine ⟨11257933268061473907569957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7505288845374315938379971 11257933268061473907569957)
                    ·
                      refine ⟨2110862487761526357669367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11257933268061473907569957 2110862487761526357669367)
                      ·
                        rfl

theorem cell23_4110890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4110890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110890 prefixEnd_4110890 := by exact prefixLift 4110890
  have htrace : WordTrace (prefixWord ++ tailWord_4110890) baseStart_4110890 baseEnd_4110890 := by
    simpa [prefixWord, tailWord_4110890, baseEnd_4110890] using wordTrace_append hprefix tailTrace_4110890
  have hstable : (prefixWord ++ tailWord_4110890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110890).length < 2 ^ (prefixWord ++ tailWord_4110890).sum := by decide
  have hdescent : baseEnd_4110890 < baseStart_4110890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110918 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4110918 : Nat := 118140960795 + 4110918 * 2 ^ 59
def prefixEnd_4110918 : Nat := 4983230072969 + 3 ^ 40 * 4110918 * 2
def baseEnd_4110918 : Nat := 2110876865219852248119239

theorem tailTrace_4110918 : CollatzResearch.WordTrace tailWord_4110918 prefixEnd_4110918 2110876865219852248119239 := by
  unfold tailWord_4110918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685546791276676554479919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99958331547235766495571605 4685546791276676554479919)
  ·
    refine ⟨7028320186915014831719879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685546791276676554479919 7028320186915014831719879)
    ·
      refine ⟨10542480280372522247579819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028320186915014831719879 10542480280372522247579819)
      ·
        refine ⟨15813720420558783371369729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10542480280372522247579819 15813720420558783371369729)
        ·
          refine ⟨11860290315419087528527297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15813720420558783371369729 11860290315419087528527297)
          ·
            refine ⟨8895217736564315646395473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11860290315419087528527297 8895217736564315646395473)
            ·
              refine ⟨6671413302423236734796605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8895217736564315646395473 6671413302423236734796605)
              ·
                refine ⟨2501779988408713775548727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6671413302423236734796605 2501779988408713775548727)
                ·
                  refine ⟨3752669982613070663323091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501779988408713775548727 3752669982613070663323091)
                  ·
                    refine ⟨5629004973919605994984637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752669982613070663323091 5629004973919605994984637)
                    ·
                      refine ⟨2110876865219852248119239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629004973919605994984637 2110876865219852248119239)
                      ·
                        rfl

theorem cell23_4110918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4110918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110918 prefixEnd_4110918 := by exact prefixLift 4110918
  have htrace : WordTrace (prefixWord ++ tailWord_4110918) baseStart_4110918 baseEnd_4110918 := by
    simpa [prefixWord, tailWord_4110918, baseEnd_4110918] using wordTrace_append hprefix tailTrace_4110918
  have hstable : (prefixWord ++ tailWord_4110918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110918).length < 2 ^ (prefixWord ++ tailWord_4110918).sum := by decide
  have hdescent : baseEnd_4110918 < baseStart_4110918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110927 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 1, 2, 3]
def baseStart_4110927 : Nat := 118140960795 + 4110927 * 2 ^ 59
def prefixEnd_4110927 : Nat := 4983230072969 + 3 ^ 40 * 4110927 * 2
def baseEnd_4110927 : Nat := 2110881486545742712906697

theorem tailTrace_4110927 : CollatzResearch.WordTrace tailWord_4110927 prefixEnd_4110927 2110881486545742712906697 := by
  unfold tailWord_4110927
  simp only [CollatzResearch.WordTrace]
  refine ⟨149937825577821044280435035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99958550385214029520290023 149937825577821044280435035)
  ·
    refine ⟨224906738366731566420652553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149937825577821044280435035 224906738366731566420652553)
    ·
      refine ⟨168680053775048674815489415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224906738366731566420652553 168680053775048674815489415)
      ·
        refine ⟨253020080662573012223234123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168680053775048674815489415 253020080662573012223234123)
        ·
          refine ⟨379530120993859518334851185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253020080662573012223234123 379530120993859518334851185)
          ·
            refine ⟨284647590745394638751138389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379530120993859518334851185 284647590745394638751138389)
            ·
              refine ⟨3335713954047593422864903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 284647590745394638751138389 3335713954047593422864903)
              ·
                refine ⟨5003570931071390134297355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335713954047593422864903 5003570931071390134297355)
                ·
                  refine ⟨7505356396607085201446033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003570931071390134297355 7505356396607085201446033)
                  ·
                    refine ⟨5629017297455313901084525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7505356396607085201446033 5629017297455313901084525)
                    ·
                      refine ⟨2110881486545742712906697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629017297455313901084525 2110881486545742712906697)
                      ·
                        rfl

theorem cell23_4110927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 2, 3].length) (baseStart_4110927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110927 prefixEnd_4110927 := by exact prefixLift 4110927
  have htrace : WordTrace (prefixWord ++ tailWord_4110927) baseStart_4110927 baseEnd_4110927 := by
    simpa [prefixWord, tailWord_4110927, baseEnd_4110927] using wordTrace_append hprefix tailTrace_4110927
  have hstable : (prefixWord ++ tailWord_4110927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110927).length < 2 ^ (prefixWord ++ tailWord_4110927).sum := by decide
  have hdescent : baseEnd_4110927 < baseStart_4110927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110957 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_4110957 : Nat := 118140960795 + 4110957 * 2 ^ 59
def prefixEnd_4110957 : Nat := 4983230072969 + 3 ^ 40 * 4110957 * 2
def baseEnd_4110957 : Nat := 2110896890965377595531559

theorem tailTrace_4110957 : CollatzResearch.WordTrace tailWord_4110957 prefixEnd_4110957 2110896890965377595531559 := by
  unfold tailWord_4110957
  simp only [CollatzResearch.WordTrace]
  refine ⟨149938919767712359404027125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99959279845141572936018083 149938919767712359404027125)
  ·
    refine ⟨14056773728223033694127543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149938919767712359404027125 14056773728223033694127543)
    ·
      refine ⟨21085160592334550541191315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14056773728223033694127543 21085160592334550541191315)
      ·
        refine ⟨31627740888501825811786973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21085160592334550541191315 31627740888501825811786973)
        ·
          refine ⟨11860402833188184679420115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31627740888501825811786973 11860402833188184679420115)
          ·
            refine ⟨17790604249782277019130173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11860402833188184679420115 17790604249782277019130173)
            ·
              refine ⟨6671476593668353882173815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17790604249782277019130173 6671476593668353882173815)
              ·
                refine ⟨10007214890502530823260723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671476593668353882173815 10007214890502530823260723)
                ·
                  refine ⟨15010822335753796234891085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10007214890502530823260723 15010822335753796234891085)
                  ·
                    refine ⟨5629058375907673588084157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15010822335753796234891085 5629058375907673588084157)
                    ·
                      refine ⟨2110896890965377595531559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629058375907673588084157 2110896890965377595531559)
                      ·
                        rfl

theorem cell23_4110957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_4110957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110957 prefixEnd_4110957 := by exact prefixLift 4110957
  have htrace : WordTrace (prefixWord ++ tailWord_4110957) baseStart_4110957 baseEnd_4110957 := by
    simpa [prefixWord, tailWord_4110957, baseEnd_4110957] using wordTrace_append hprefix tailTrace_4110957
  have hstable : (prefixWord ++ tailWord_4110957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110957).length < 2 ^ (prefixWord ++ tailWord_4110957).sum := by decide
  have hdescent : baseEnd_4110957 < baseStart_4110957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4110967 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 1, 3, 2]
def baseStart_4110967 : Nat := 118140960795 + 4110967 * 2 ^ 59
def prefixEnd_4110967 : Nat := 4983230072969 + 3 ^ 40 * 4110967 * 2
def baseEnd_4110967 : Nat := 2110902025771922556406513

theorem tailTrace_4110967 : CollatzResearch.WordTrace tailWord_4110967 prefixEnd_4110967 2110902025771922556406513 := by
  unfold tailWord_4110967
  simp only [CollatzResearch.WordTrace]
  refine ⟨149939284497676131111891155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99959522998450754074594103 149939284497676131111891155)
  ·
    refine ⟨224908926746514196667836733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149939284497676131111891155 224908926746514196667836733)
    ·
      refine ⟨84340847529942823750438775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224908926746514196667836733 84340847529942823750438775)
      ·
        refine ⟨126511271294914235625658163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84340847529942823750438775 126511271294914235625658163)
        ·
          refine ⟨189766906942371353438487245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126511271294914235625658163 189766906942371353438487245)
          ·
            refine ⟨71162590103389257539432717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189766906942371353438487245 71162590103389257539432717)
            ·
              refine ⟨26685971288770971577287269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71162590103389257539432717 26685971288770971577287269)
              ·
                refine ⟨5003619616644557170741363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26685971288770971577287269 5003619616644557170741363)
                ·
                  refine ⟨7505429424966835756112045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003619616644557170741363 7505429424966835756112045)
                  ·
                    refine ⟨2814536034362563408542017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7505429424966835756112045 2814536034362563408542017)
                    ·
                      refine ⟨2110902025771922556406513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814536034362563408542017 2110902025771922556406513)
                      ·
                        rfl

theorem cell23_4110967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_4110967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4110967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4110967 prefixEnd_4110967 := by exact prefixLift 4110967
  have htrace : WordTrace (prefixWord ++ tailWord_4110967) baseStart_4110967 baseEnd_4110967 := by
    simpa [prefixWord, tailWord_4110967, baseEnd_4110967] using wordTrace_append hprefix tailTrace_4110967
  have hstable : (prefixWord ++ tailWord_4110967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4110967).length < 2 ^ (prefixWord ++ tailWord_4110967).sum := by decide
  have hdescent : baseEnd_4110967 < baseStart_4110967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4110967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111000 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4111000 : Nat := 118140960795 + 4111000 * 2 ^ 59
def prefixEnd_4111000 : Nat := 4983230072969 + 3 ^ 40 * 4111000 * 2
def baseEnd_4111000 : Nat := 2110918970633520927293861

theorem tailTrace_4111000 : CollatzResearch.WordTrace tailWord_4111000 prefixEnd_4111000 2110918970633520927293861 := by
  unfold tailWord_4111000
  simp only [CollatzResearch.WordTrace]
  refine ⟨74970244053278288873921227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99960325404371051831894969 74970244053278288873921227)
  ·
    refine ⟨112455366079917433310881841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74970244053278288873921227 112455366079917433310881841)
    ·
      refine ⟨84341524559938074983161381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112455366079917433310881841 84341524559938074983161381)
      ·
        refine ⟨15814035854988389059342759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84341524559938074983161381 15814035854988389059342759)
        ·
          refine ⟨23721053782482583589014139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15814035854988389059342759 23721053782482583589014139)
          ·
            refine ⟨35581580673723875383521209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23721053782482583589014139 35581580673723875383521209)
            ·
              refine ⟨26686185505292906537640907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35581580673723875383521209 26686185505292906537640907)
              ·
                refine ⟨40029278257939359806461361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26686185505292906537640907 40029278257939359806461361)
                ·
                  refine ⟨30021958693454519854846021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40029278257939359806461361 30021958693454519854846021)
                  ·
                    refine ⟨5629117255022722472783629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30021958693454519854846021 5629117255022722472783629)
                    ·
                      refine ⟨2110918970633520927293861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629117255022722472783629 2110918970633520927293861)
                      ·
                        rfl

theorem cell23_4111000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4111000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111000 prefixEnd_4111000 := by exact prefixLift 4111000
  have htrace : WordTrace (prefixWord ++ tailWord_4111000) baseStart_4111000 baseEnd_4111000 := by
    simpa [prefixWord, tailWord_4111000, baseEnd_4111000] using wordTrace_append hprefix tailTrace_4111000
  have hstable : (prefixWord ++ tailWord_4111000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111000).length < 2 ^ (prefixWord ++ tailWord_4111000).sum := by decide
  have hdescent : baseEnd_4111000 < baseStart_4111000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111008 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 2, 1, 3]
def baseStart_4111008 : Nat := 118140960795 + 4111008 * 2 ^ 59
def prefixEnd_4111008 : Nat := 4983230072969 + 3 ^ 40 * 4111008 * 2
def baseEnd_4111008 : Nat := 2110923078478756895993825

theorem tailTrace_4111008 : CollatzResearch.WordTrace tailWord_4111008 prefixEnd_4111008 2110923078478756895993825 := by
  unfold tailWord_4111008
  simp only [CollatzResearch.WordTrace]
  refine ⟨74970389945263797557066839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99960519927018396742755785 74970389945263797557066839)
  ·
    refine ⟨112455584917895696335600259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74970389945263797557066839 112455584917895696335600259)
    ·
      refine ⟨168683377376843544503400389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112455584917895696335600259 168683377376843544503400389)
      ·
        refine ⟨31628133258158164594387573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168683377376843544503400389 31628133258158164594387573)
        ·
          refine ⟨2965137492952327930723835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31628133258158164594387573 2965137492952327930723835)
          ·
            refine ⟨4447706239428491896085753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965137492952327930723835 4447706239428491896085753)
            ·
              refine ⟨3335779679571368922064315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4447706239428491896085753 3335779679571368922064315)
              ·
                refine ⟨5003669519357053383096473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3335779679571368922064315 5003669519357053383096473)
                ·
                  refine ⟨3752752139517790037322355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5003669519357053383096473 3752752139517790037322355)
                  ·
                    refine ⟨5629128209276685055983533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752752139517790037322355 5629128209276685055983533)
                    ·
                      refine ⟨2110923078478756895993825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629128209276685055983533 2110923078478756895993825)
                      ·
                        rfl

theorem cell23_4111008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_4111008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111008 prefixEnd_4111008 := by exact prefixLift 4111008
  have htrace : WordTrace (prefixWord ++ tailWord_4111008) baseStart_4111008 baseEnd_4111008 := by
    simpa [prefixWord, tailWord_4111008, baseEnd_4111008] using wordTrace_append hprefix tailTrace_4111008
  have hstable : (prefixWord ++ tailWord_4111008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111008).length < 2 ^ (prefixWord ++ tailWord_4111008).sum := by decide
  have hdescent : baseEnd_4111008 < baseStart_4111008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111054 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_4111054 : Nat := 118140960795 + 4111054 * 2 ^ 59
def prefixEnd_4111054 : Nat := 4983230072969 + 3 ^ 40 * 4111054 * 2
def baseEnd_4111054 : Nat := 234549633176540412890957

theorem tailTrace_4111054 : CollatzResearch.WordTrace tailWord_4111054 prefixEnd_4111054 234549633176540412890957 := by
  unfold tailWord_4111054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18742807206045118121288527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99961638432240629980205477 18742807206045118121288527)
  ·
    refine ⟨28114210809067677181932791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18742807206045118121288527 28114210809067677181932791)
    ·
      refine ⟨42171316213601515772899187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28114210809067677181932791 42171316213601515772899187)
      ·
        refine ⟨63256974320402273659348781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42171316213601515772899187 63256974320402273659348781)
        ·
          refine ⟨23721365370150852622255793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63256974320402273659348781 23721365370150852622255793)
          ·
            refine ⟨17791024027613139466691845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23721365370150852622255793 17791024027613139466691845)
            ·
              refine ⟨3335817005177463650004721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17791024027613139466691845 3335817005177463650004721)
              ·
                refine ⟨2501862753883097737503541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335817005177463650004721 2501862753883097737503541)
                ·
                  refine ⟨234549633176540412890957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2501862753883097737503541 234549633176540412890957)
                  ·
                    rfl

theorem cell23_4111054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_4111054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111054 prefixEnd_4111054 := by exact prefixLift 4111054
  have htrace : WordTrace (prefixWord ++ tailWord_4111054) baseStart_4111054 baseEnd_4111054 := by
    simpa [prefixWord, tailWord_4111054, baseEnd_4111054] using wordTrace_append hprefix tailTrace_4111054
  have hstable : (prefixWord ++ tailWord_4111054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111054).length < 2 ^ (prefixWord ++ tailWord_4111054).sum := by decide
  have hdescent : baseEnd_4111054 < baseStart_4111054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111087 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_4111087 : Nat := 118140960795 + 4111087 * 2 ^ 59
def prefixEnd_4111087 : Nat := 4983230072969 + 3 ^ 40 * 4111087 * 2
def baseEnd_4111087 : Nat := 2110963643450462086905961

theorem tailTrace_4111087 : CollatzResearch.WordTrace tailWord_4111087 prefixEnd_4111087 2110963643450462086905961 := by
  unfold tailWord_4111087
  simp only [CollatzResearch.WordTrace]
  refine ⟨149943661257241391606259515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99962440838160927737506343 149943661257241391606259515)
  ·
    refine ⟨224915491885862087409389273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149943661257241391606259515 224915491885862087409389273)
    ·
      refine ⟨168686618914396565557041955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224915491885862087409389273 168686618914396565557041955)
      ·
        refine ⟨253029928371594848335562933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168686618914396565557041955 253029928371594848335562933)
        ·
          refine ⟨23721555784837017031459025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253029928371594848335562933 23721555784837017031459025)
          ·
            refine ⟨17791166838627762773594269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23721555784837017031459025 17791166838627762773594269)
            ·
              refine ⟨6671687564485411040097851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17791166838627762773594269 6671687564485411040097851)
              ·
                refine ⟨10007531346728116560146777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6671687564485411040097851 10007531346728116560146777)
                ·
                  refine ⟨7505648510046087420110083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10007531346728116560146777 7505648510046087420110083)
                  ·
                    refine ⟨11258472765069131130165125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7505648510046087420110083 11258472765069131130165125)
                    ·
                      refine ⟨2110963643450462086905961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11258472765069131130165125 2110963643450462086905961)
                      ·
                        rfl

theorem cell23_4111087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_4111087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111087 prefixEnd_4111087 := by exact prefixLift 4111087
  have htrace : WordTrace (prefixWord ++ tailWord_4111087) baseStart_4111087 baseEnd_4111087 := by
    simpa [prefixWord, tailWord_4111087, baseEnd_4111087] using wordTrace_append hprefix tailTrace_4111087
  have hstable : (prefixWord ++ tailWord_4111087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111087).length < 2 ^ (prefixWord ++ tailWord_4111087).sum := by decide
  have hdescent : baseEnd_4111087 < baseStart_4111087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111100 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_4111100 : Nat := 118140960795 + 4111100 * 2 ^ 59
def prefixEnd_4111100 : Nat := 4983230072969 + 3 ^ 40 * 4111100 * 2
def baseEnd_4111100 : Nat := 2110970318698970536043401

theorem tailTrace_4111100 : CollatzResearch.WordTrace tailWord_4111100 prefixEnd_4111100 2110970318698970536043401 := by
  unfold tailWord_4111100
  simp only [CollatzResearch.WordTrace]
  refine ⟨74972067703097147413241377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99962756937462863217655169 74972067703097147413241377)
  ·
    refine ⟨56229050777322860559931033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74972067703097147413241377 56229050777322860559931033)
    ·
      refine ⟨42171788082992145419948275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56229050777322860559931033 42171788082992145419948275)
      ·
        refine ⟨63257682124488218129922413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42171788082992145419948275 63257682124488218129922413)
        ·
          refine ⟨23721630796683081798720905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63257682124488218129922413 23721630796683081798720905)
          ·
            refine ⟨17791223097512311349040679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23721630796683081798720905 17791223097512311349040679)
            ·
              refine ⟨26686834646268467023561019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791223097512311349040679 26686834646268467023561019)
              ·
                refine ⟨40030251969402700535341529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26686834646268467023561019 40030251969402700535341529)
                ·
                  refine ⟨30022688977052025401506147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40030251969402700535341529 30022688977052025401506147)
                  ·
                    refine ⟨45034033465578038102259221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30022688977052025401506147 45034033465578038102259221)
                    ·
                      refine ⟨2110970318698970536043401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45034033465578038102259221 2110970318698970536043401)
                      ·
                        rfl

theorem cell23_4111100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_4111100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111100 prefixEnd_4111100 := by exact prefixLift 4111100
  have htrace : WordTrace (prefixWord ++ tailWord_4111100) baseStart_4111100 baseEnd_4111100 := by
    simpa [prefixWord, tailWord_4111100, baseEnd_4111100] using wordTrace_append hprefix tailTrace_4111100
  have hstable : (prefixWord ++ tailWord_4111100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111100).length < 2 ^ (prefixWord ++ tailWord_4111100).sum := by decide
  have hdescent : baseEnd_4111100 < baseStart_4111100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111114 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_4111114 : Nat := 118140960795 + 4111114 * 2 ^ 59
def prefixEnd_4111114 : Nat := 4983230072969 + 3 ^ 40 * 4111114 * 2
def baseEnd_4111114 : Nat := 703659169142711160422779

theorem tailTrace_4111114 : CollatzResearch.WordTrace tailWord_4111114 prefixEnd_4111114 703659169142711160422779 := by
  unfold tailWord_4111114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37486161507035893804373099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99963097352095716811661597 37486161507035893804373099)
  ·
    refine ⟨56229242260553840706559649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37486161507035893804373099 56229242260553840706559649)
    ·
      refine ⟨42171931695415380529919737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56229242260553840706559649 42171931695415380529919737)
      ·
        refine ⟨31628948771561535397439803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42171931695415380529919737 31628948771561535397439803)
        ·
          refine ⟨47443423157342303096159705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31628948771561535397439803 47443423157342303096159705)
          ·
            refine ⟨35582567368006727322119779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47443423157342303096159705 35582567368006727322119779)
            ·
              refine ⟨53373851052010090983179669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35582567368006727322119779 53373851052010090983179669)
              ·
                refine ⟨2501899268062973014836547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53373851052010090983179669 2501899268062973014836547)
                ·
                  refine ⟨3752848902094459522254821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501899268062973014836547 3752848902094459522254821)
                  ·
                    refine ⟨703659169142711160422779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752848902094459522254821 703659169142711160422779)
                    ·
                      rfl

theorem cell23_4111114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_4111114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111114 prefixEnd_4111114 := by exact prefixLift 4111114
  have htrace : WordTrace (prefixWord ++ tailWord_4111114) baseStart_4111114 baseEnd_4111114 := by
    simpa [prefixWord, tailWord_4111114, baseEnd_4111114] using wordTrace_append hprefix tailTrace_4111114
  have hstable : (prefixWord ++ tailWord_4111114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111114).length < 2 ^ (prefixWord ++ tailWord_4111114).sum := by decide
  have hdescent : baseEnd_4111114 < baseStart_4111114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111130 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_4111130 : Nat := 118140960795 + 4111130 * 2 ^ 59
def prefixEnd_4111130 : Nat := 4983230072969 + 3 ^ 40 * 4111130 * 2
def baseEnd_4111130 : Nat := 2110985723118605418668263

theorem tailTrace_4111130 : CollatzResearch.WordTrace tailWord_4111130 prefixEnd_4111130 2110985723118605418668263 := by
  unfold tailWord_4111130
  simp only [CollatzResearch.WordTrace]
  refine ⟨37486307399021402487518711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99963486397390406633383229 37486307399021402487518711)
  ·
    refine ⟨56229461098532103731278067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37486307399021402487518711 56229461098532103731278067)
    ·
      refine ⟨84344191647798155596917101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56229461098532103731278067 84344191647798155596917101)
      ·
        refine ⟨31629071867924308348843913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84344191647798155596917101 31629071867924308348843913)
        ·
          refine ⟨23721803900943231261632935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31629071867924308348843913 23721803900943231261632935)
          ·
            refine ⟨35582705851414846892449403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23721803900943231261632935 35582705851414846892449403)
            ·
              refine ⟨53374058777122270338674105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35582705851414846892449403 53374058777122270338674105)
              ·
                refine ⟨40030544082841702754005579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53374058777122270338674105 40030544082841702754005579)
                ·
                  refine ⟨60045816124262554131008369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40030544082841702754005579 60045816124262554131008369)
                  ·
                    refine ⟨45034362093196915598256277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60045816124262554131008369 45034362093196915598256277)
                    ·
                      refine ⟨2110985723118605418668263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45034362093196915598256277 2110985723118605418668263)
                      ·
                        rfl

theorem cell23_4111130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_4111130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111130 prefixEnd_4111130 := by exact prefixLift 4111130
  have htrace : WordTrace (prefixWord ++ tailWord_4111130) baseStart_4111130 baseEnd_4111130 := by
    simpa [prefixWord, tailWord_4111130, baseEnd_4111130] using wordTrace_append hprefix tailTrace_4111130
  have hstable : (prefixWord ++ tailWord_4111130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111130).length < 2 ^ (prefixWord ++ tailWord_4111130).sum := by decide
  have hdescent : baseEnd_4111130 < baseStart_4111130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111194 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_4111194 : Nat := 118140960795 + 4111194 * 2 ^ 59
def prefixEnd_4111194 : Nat := 4983230072969 + 3 ^ 40 * 4111194 * 2
def baseEnd_4111194 : Nat := 2111018585880493168267969

theorem tailTrace_4111194 : CollatzResearch.WordTrace tailWord_4111194 prefixEnd_4111194 2111018585880493168267969 := by
  unfold tailWord_4111194
  simp only [CollatzResearch.WordTrace]
  refine ⟨37486890966963437220101159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99965042578569165920269757 37486890966963437220101159)
  ·
    refine ⟨56230336450445155830151739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37486890966963437220101159 56230336450445155830151739)
    ·
      refine ⟨84345504675667733745227609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56230336450445155830151739 84345504675667733745227609)
      ·
        refine ⟨63259128506750800308920707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84345504675667733745227609 63259128506750800308920707)
        ·
          refine ⟨94888692760126200463381061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63259128506750800308920707 94888692760126200463381061)
          ·
            refine ⟨17791629892523662586883949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94888692760126200463381061 17791629892523662586883949)
            ·
              refine ⟨6671861209696373470081481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17791629892523662586883949 6671861209696373470081481)
              ·
                refine ⟨5003895907272280102561111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6671861209696373470081481 5003895907272280102561111)
                ·
                  refine ⟨7505843860908420153841667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5003895907272280102561111 7505843860908420153841667)
                  ·
                    refine ⟨11258765791362630230762501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7505843860908420153841667 11258765791362630230762501)
                    ·
                      refine ⟨2111018585880493168267969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11258765791362630230762501 2111018585880493168267969)
                      ·
                        rfl

theorem cell23_4111194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_4111194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111194 prefixEnd_4111194 := by exact prefixLift 4111194
  have htrace : WordTrace (prefixWord ++ tailWord_4111194) baseStart_4111194 baseEnd_4111194 := by
    simpa [prefixWord, tailWord_4111194, baseEnd_4111194] using wordTrace_append hprefix tailTrace_4111194
  have hstable : (prefixWord ++ tailWord_4111194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111194).length < 2 ^ (prefixWord ++ tailWord_4111194).sum := by decide
  have hdescent : baseEnd_4111194 < baseStart_4111194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111200 : List Nat := [2, 1, 1, 3, 3, 1, 1, 11]
def baseStart_4111200 : Nat := 118140960795 + 4111200 * 2 ^ 59
def prefixEnd_4111200 : Nat := 4983230072969 + 3 ^ 40 * 4111200 * 2
def baseEnd_4111200 : Nat := 78185987657941486844183

theorem tailTrace_4111200 : CollatzResearch.WordTrace tailWord_4111200 prefixEnd_4111200 78185987657941486844183 := by
  unfold tailWord_4111200
  simp only [CollatzResearch.WordTrace]
  refine ⟨74973891352916005952561527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99965188470554674603415369 74973891352916005952561527)
  ·
    refine ⟨112460837029374008928842291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74973891352916005952561527 112460837029374008928842291)
    ·
      refine ⟨168691255544061013393263437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112460837029374008928842291 168691255544061013393263437)
      ·
        refine ⟨63259220829022880022473789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168691255544061013393263437 63259220829022880022473789)
        ·
          refine ⟨23722207810883580008427671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63259220829022880022473789 23722207810883580008427671)
          ·
            refine ⟨35583311716325370012641507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23722207810883580008427671 35583311716325370012641507)
            ·
              refine ⟨53374967574488055018962261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35583311716325370012641507 53374967574488055018962261)
              ·
                refine ⟨78185987657941486844183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53374967574488055018962261 78185987657941486844183)
                ·
                  rfl

theorem cell23_4111200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 11].length) (baseStart_4111200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111200 prefixEnd_4111200 := by exact prefixLift 4111200
  have htrace : WordTrace (prefixWord ++ tailWord_4111200) baseStart_4111200 baseEnd_4111200 := by
    simpa [prefixWord, tailWord_4111200, baseEnd_4111200] using wordTrace_append hprefix tailTrace_4111200
  have hstable : (prefixWord ++ tailWord_4111200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111200).length < 2 ^ (prefixWord ++ tailWord_4111200).sum := by decide
  have hdescent : baseEnd_4111200 < baseStart_4111200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111207 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_4111207 : Nat := 118140960795 + 4111207 * 2 ^ 59
def prefixEnd_4111207 : Nat := 4983230072969 + 3 ^ 40 * 4111207 * 2
def baseEnd_4111207 : Nat := 2111025261129001617405409

theorem tailTrace_4111207 : CollatzResearch.WordTrace tailWord_4111207 prefixEnd_4111207 2111025261129001617405409 := by
  unfold tailWord_4111207
  simp only [CollatzResearch.WordTrace]
  refine ⟨149948038016806652100627875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99965358677871101400418583 149948038016806652100627875)
  ·
    refine ⟨224922057025209978150941813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149948038016806652100627875 224922057025209978150941813)
    ·
      refine ⟨21086442846113435451650795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224922057025209978150941813 21086442846113435451650795)
      ·
        refine ⟨31629664269170153177476193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21086442846113435451650795 31629664269170153177476193)
        ·
          refine ⟨23722248201877614883107145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31629664269170153177476193 23722248201877614883107145)
          ·
            refine ⟨17791686151408211162330359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23722248201877614883107145 17791686151408211162330359)
            ·
              refine ⟨26687529227112316743495539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791686151408211162330359 26687529227112316743495539)
              ·
                refine ⟨40031293840668475115243309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26687529227112316743495539 40031293840668475115243309)
                ·
                  refine ⟨15011735190250678168216241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40031293840668475115243309 15011735190250678168216241)
                  ·
                    refine ⟨11258801392688008626162181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15011735190250678168216241 11258801392688008626162181)
                    ·
                      refine ⟨2111025261129001617405409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11258801392688008626162181 2111025261129001617405409)
                      ·
                        rfl

theorem cell23_4111207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_4111207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111207 prefixEnd_4111207 := by exact prefixLift 4111207
  have htrace : WordTrace (prefixWord ++ tailWord_4111207) baseStart_4111207 baseEnd_4111207 := by
    simpa [prefixWord, tailWord_4111207, baseEnd_4111207] using wordTrace_append hprefix tailTrace_4111207
  have hstable : (prefixWord ++ tailWord_4111207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111207).length < 2 ^ (prefixWord ++ tailWord_4111207).sum := by decide
  have hdescent : baseEnd_4111207 < baseStart_4111207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111221 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4111221 : Nat := 118140960795 + 4111221 * 2 ^ 59
def prefixEnd_4111221 : Nat := 4983230072969 + 3 ^ 40 * 4111221 * 2
def baseEnd_4111221 : Nat := 703677483286054854210115

theorem tailTrace_4111221 : CollatzResearch.WordTrace tailWord_4111221 prefixEnd_4111221 703677483286054854210115 := by
  unfold tailWord_4111221
  simp only [CollatzResearch.WordTrace]
  refine ⟨149948548638755932491637517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99965699092503954994425011 149948548638755932491637517)
  ·
    refine ⟨56230705739533474684364069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149948548638755932491637517 56230705739533474684364069)
    ·
      refine ⟨10543257326162526503318263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56230705739533474684364069 10543257326162526503318263)
      ·
        refine ⟨15814885989243789754977395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10543257326162526503318263 15814885989243789754977395)
        ·
          refine ⟨23722328983865684632466093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15814885989243789754977395 23722328983865684632466093)
          ·
            refine ⟨8895873368949631737174785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23722328983865684632466093 8895873368949631737174785)
            ·
              refine ⟨6671905026712223802881089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8895873368949631737174785 6671905026712223802881089)
              ·
                refine ⟨5003928770034167852160817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6671905026712223802881089 5003928770034167852160817)
                ·
                  refine ⟨3752946577525625889120613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5003928770034167852160817 3752946577525625889120613)
                  ·
                    refine ⟨703677483286054854210115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3752946577525625889120613 703677483286054854210115)
                    ·
                      rfl

theorem cell23_4111221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4111221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111221 prefixEnd_4111221 := by exact prefixLift 4111221
  have htrace : WordTrace (prefixWord ++ tailWord_4111221) baseStart_4111221 baseEnd_4111221 := by
    simpa [prefixWord, tailWord_4111221, baseEnd_4111221] using wordTrace_append hprefix tailTrace_4111221
  have hstable : (prefixWord ++ tailWord_4111221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111221).length < 2 ^ (prefixWord ++ tailWord_4111221).sum := by decide
  have hdescent : baseEnd_4111221 < baseStart_4111221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111222 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4111222 : Nat := 118140960795 + 4111222 * 2 ^ 59
def prefixEnd_4111222 : Nat := 4983230072969 + 3 ^ 40 * 4111222 * 2
def baseEnd_4111222 : Nat := 2111032963338819058717841

theorem tailTrace_4111222 : CollatzResearch.WordTrace tailWord_4111222 prefixEnd_4111222 2111032963338819058717841 := by
  unfold tailWord_4111222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371786569484519353901495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99965723407834873108282613 9371786569484519353901495)
  ·
    refine ⟨14057679854226779030852243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9371786569484519353901495 14057679854226779030852243)
    ·
      refine ⟨21086519781340168546278365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14057679854226779030852243 21086519781340168546278365)
      ·
        refine ⟨7907444918002563204854387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21086519781340168546278365 7907444918002563204854387)
        ·
          refine ⟨11861167377003844807281581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7907444918002563204854387 11861167377003844807281581)
          ·
            refine ⟨4447937766376441802730593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11861167377003844807281581 4447937766376441802730593)
            ·
              refine ⟨3335953324782331352047945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4447937766376441802730593 3335953324782331352047945)
              ·
                refine ⟨2501964993586748514035959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3335953324782331352047945 2501964993586748514035959)
                ·
                  refine ⟨3752947490380122771053939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2501964993586748514035959 3752947490380122771053939)
                  ·
                    refine ⟨5629421235570184156580909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3752947490380122771053939 5629421235570184156580909)
                    ·
                      refine ⟨2111032963338819058717841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629421235570184156580909 2111032963338819058717841)
                      ·
                        rfl

theorem cell23_4111222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4111222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111222 prefixEnd_4111222 := by exact prefixLift 4111222
  have htrace : WordTrace (prefixWord ++ tailWord_4111222) baseStart_4111222 baseEnd_4111222 := by
    simpa [prefixWord, tailWord_4111222, baseEnd_4111222] using wordTrace_append hprefix tailTrace_4111222
  have hstable : (prefixWord ++ tailWord_4111222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111222).length < 2 ^ (prefixWord ++ tailWord_4111222).sum := by decide
  have hdescent : baseEnd_4111222 < baseStart_4111222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111287 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_4111287 : Nat := 118140960795 + 4111287 * 2 ^ 59
def prefixEnd_4111287 : Nat := 4983230072969 + 3 ^ 40 * 4111287 * 2
def baseEnd_4111287 : Nat := 2111066339581361304405041

theorem tailTrace_4111287 : CollatzResearch.WordTrace tailWord_4111287 prefixEnd_4111287 2111066339581361304405041 := by
  unfold tailWord_4111287
  simp only [CollatzResearch.WordTrace]
  refine ⟨149950955856516825763540115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99967303904344550509026743 149950955856516825763540115)
  ·
    refine ⟨224926433784775238645310173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149950955856516825763540115 224926433784775238645310173)
    ·
      refine ⟨84347412669290714491991315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224926433784775238645310173 84347412669290714491991315)
      ·
        refine ⟨126521119003936071737986973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84347412669290714491991315 126521119003936071737986973)
        ·
          refine ⟨47445419626476026901745115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126521119003936071737986973 47445419626476026901745115)
          ·
            refine ⟨71168129439714040352617673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47445419626476026901745115 71168129439714040352617673)
            ·
              refine ⟨53376097079785530264463255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71168129439714040352617673 53376097079785530264463255)
              ·
                refine ⟨80064145619678295396694883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53376097079785530264463255 80064145619678295396694883)
                ·
                  refine ⟨120096218429517443095042325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80064145619678295396694883 120096218429517443095042325)
                  ·
                    refine ⟨5629510238883630145080109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 120096218429517443095042325 5629510238883630145080109)
                    ·
                      refine ⟨2111066339581361304405041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629510238883630145080109 2111066339581361304405041)
                      ·
                        rfl

theorem cell23_4111287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_4111287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111287 prefixEnd_4111287 := by exact prefixLift 4111287
  have htrace : WordTrace (prefixWord ++ tailWord_4111287) baseStart_4111287 baseEnd_4111287 := by
    simpa [prefixWord, tailWord_4111287, baseEnd_4111287] using wordTrace_append hprefix tailTrace_4111287
  have hstable : (prefixWord ++ tailWord_4111287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111287).length < 2 ^ (prefixWord ++ tailWord_4111287).sum := by decide
  have hdescent : baseEnd_4111287 < baseStart_4111287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111302 : List Nat := [6, 1, 3, 1, 1, 2, 2, 7]
def baseStart_4111302 : Nat := 118140960795 + 4111302 * 2 ^ 59
def prefixEnd_4111302 : Nat := 4983230072969 + 3 ^ 40 * 4111302 * 2
def baseEnd_4111302 : Nat := 78187927473747360952499

theorem tailTrace_4111302 : CollatzResearch.WordTrace tailWord_4111302 prefixEnd_4111302 78187927473747360952499 := by
  unfold tailWord_4111302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685984467233202603916755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99967668634308322216890773 4685984467233202603916755)
  ·
    refine ⟨7028976700849803905875133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685984467233202603916755 7028976700849803905875133)
    ·
      refine ⟨2635866262818676464703175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7028976700849803905875133 2635866262818676464703175)
      ·
        refine ⟨3953799394228014697054763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635866262818676464703175 3953799394228014697054763)
        ·
          refine ⟨5930699091342022045582145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953799394228014697054763 5930699091342022045582145)
          ·
            refine ⟨4448024318506516534186609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5930699091342022045582145 4448024318506516534186609)
            ·
              refine ⟨3336018238879887400639957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448024318506516534186609 3336018238879887400639957)
              ·
                refine ⟨78187927473747360952499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3336018238879887400639957 78187927473747360952499)
                ·
                  rfl

theorem cell23_4111302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_4111302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111302 prefixEnd_4111302 := by exact prefixLift 4111302
  have htrace : WordTrace (prefixWord ++ tailWord_4111302) baseStart_4111302 baseEnd_4111302 := by
    simpa [prefixWord, tailWord_4111302, baseEnd_4111302] using wordTrace_append hprefix tailTrace_4111302
  have hstable : (prefixWord ++ tailWord_4111302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111302).length < 2 ^ (prefixWord ++ tailWord_4111302).sum := by decide
  have hdescent : baseEnd_4111302 < baseStart_4111302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111307 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 7]
def baseStart_4111307 : Nat := 118140960795 + 4111307 * 2 ^ 59
def prefixEnd_4111307 : Nat := 4983230072969 + 3 ^ 40 * 4111307 * 2
def baseEnd_4111307 : Nat := 234564067688272358461661

theorem tailTrace_4111307 : CollatzResearch.WordTrace tailWord_4111307 prefixEnd_4111307 234564067688272358461661 := by
  unfold tailWord_4111307
  simp only [CollatzResearch.WordTrace]
  refine ⟨149951685316444369179268175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99967790210962912786178783 149951685316444369179268175)
  ·
    refine ⟨224927527974666553768902263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149951685316444369179268175 224927527974666553768902263)
    ·
      refine ⟨337391291961999830653353395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224927527974666553768902263 337391291961999830653353395)
      ·
        refine ⟨506086937942999745980030093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337391291961999830653353395 506086937942999745980030093)
        ·
          refine ⟨189782601728624904742511285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506086937942999745980030093 189782601728624904742511285)
          ·
            refine ⟨17792118912058584819610433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189782601728624904742511285 17792118912058584819610433)
            ·
              refine ⟨13344089184043938614707825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17792118912058584819610433 13344089184043938614707825)
              ·
                refine ⟨10008066888032953961030869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13344089184043938614707825 10008066888032953961030869)
                ·
                  refine ⟨234564067688272358461661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10008066888032953961030869 234564067688272358461661)
                  ·
                    rfl

theorem cell23_4111307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 7].length) (baseStart_4111307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111307 prefixEnd_4111307 := by exact prefixLift 4111307
  have htrace : WordTrace (prefixWord ++ tailWord_4111307) baseStart_4111307 baseEnd_4111307 := by
    simpa [prefixWord, tailWord_4111307, baseEnd_4111307] using wordTrace_append hprefix tailTrace_4111307
  have hstable : (prefixWord ++ tailWord_4111307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111307).length < 2 ^ (prefixWord ++ tailWord_4111307).sum := by decide
  have hdescent : baseEnd_4111307 < baseStart_4111307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111344 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 2, 5, 2]
def baseStart_4111344 : Nat := 118140960795 + 4111344 * 2 ^ 59
def prefixEnd_4111344 : Nat := 4983230072969 + 3 ^ 40 * 4111344 * 2
def baseEnd_4111344 : Nat := 2111095607978667581392279

theorem tailTrace_4111344 : CollatzResearch.WordTrace tailWord_4111344 prefixEnd_4111344 2111095607978667581392279 := by
  unfold tailWord_4111344
  simp only [CollatzResearch.WordTrace]
  refine ⟨74976517408655162249182543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99968689878206882998910057 74976517408655162249182543)
  ·
    refine ⟨112464776112982743373773815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74976517408655162249182543 112464776112982743373773815)
    ·
      refine ⟨168697164169474115060660723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112464776112982743373773815 168697164169474115060660723)
      ·
        refine ⟨253045746254211172590991085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168697164169474115060660723 253045746254211172590991085)
        ·
          refine ⟨94892154845329189721621657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253045746254211172590991085 94892154845329189721621657)
          ·
            refine ⟨71169116133996892291216243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94892154845329189721621657 71169116133996892291216243)
            ·
              refine ⟨106753674200995338436824365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71169116133996892291216243 106753674200995338436824365)
              ·
                refine ⟨40032627825373251913809137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106753674200995338436824365 40032627825373251913809137)
                ·
                  refine ⟨30024470869029938935356853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40032627825373251913809137 30024470869029938935356853)
                  ·
                    refine ⟨2814794143971556775189705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30024470869029938935356853 2814794143971556775189705)
                    ·
                      refine ⟨2111095607978667581392279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814794143971556775189705 2111095607978667581392279)
                      ·
                        rfl

theorem cell23_4111344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 5, 2].length) (baseStart_4111344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111344 prefixEnd_4111344 := by exact prefixLift 4111344
  have htrace : WordTrace (prefixWord ++ tailWord_4111344) baseStart_4111344 baseEnd_4111344 := by
    simpa [prefixWord, tailWord_4111344, baseEnd_4111344] using wordTrace_append hprefix tailTrace_4111344
  have hstable : (prefixWord ++ tailWord_4111344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111344).length < 2 ^ (prefixWord ++ tailWord_4111344).sum := by decide
  have hdescent : baseEnd_4111344 < baseStart_4111344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111387 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4]
def baseStart_4111387 : Nat := 118140960795 + 4111387 * 2 ^ 59
def prefixEnd_4111387 : Nat := 4983230072969 + 3 ^ 40 * 4111387 * 2
def baseEnd_4111387 : Nat := 2111117687646810913154581

theorem tailTrace_4111387 : CollatzResearch.WordTrace tailWord_4111387 prefixEnd_4111387 2111117687646810913154581 := by
  unfold tailWord_4111387
  simp only [CollatzResearch.WordTrace]
  refine ⟨149954603156154542842180415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99969735437436361894786943 149954603156154542842180415)
  ·
    refine ⟨224931904734231814263270623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149954603156154542842180415 224931904734231814263270623)
    ·
      refine ⟨337397857101347721394905935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224931904734231814263270623 337397857101347721394905935)
      ·
        refine ⟨506096785652021582092358903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337397857101347721394905935 506096785652021582092358903)
        ·
          refine ⟨759145178478032373138538355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506096785652021582092358903 759145178478032373138538355)
          ·
            refine ⟨1138717767717048559707807533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759145178478032373138538355 1138717767717048559707807533)
            ·
              refine ⟨427019162893893209890427825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1138717767717048559707807533 427019162893893209890427825)
              ·
                refine ⟨320264372170419907417820869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427019162893893209890427825 320264372170419907417820869)
                ·
                  refine ⟨60049569781953732640841413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320264372170419907417820869 60049569781953732640841413)
                  ·
                    refine ⟨11259294334116324870157765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60049569781953732640841413 11259294334116324870157765)
                    ·
                      refine ⟨2111117687646810913154581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11259294334116324870157765 2111117687646810913154581)
                      ·
                        rfl

theorem cell23_4111387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_4111387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111387 prefixEnd_4111387 := by exact prefixLift 4111387
  have htrace : WordTrace (prefixWord ++ tailWord_4111387) baseStart_4111387 baseEnd_4111387 := by
    simpa [prefixWord, tailWord_4111387, baseEnd_4111387] using wordTrace_append hprefix tailTrace_4111387
  have hstable : (prefixWord ++ tailWord_4111387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111387).length < 2 ^ (prefixWord ++ tailWord_4111387).sum := by decide
  have hdescent : baseEnd_4111387 < baseStart_4111387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111392 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 5]
def baseStart_4111392 : Nat := 118140960795 + 4111392 * 2 ^ 59
def prefixEnd_4111392 : Nat := 4983230072969 + 3 ^ 40 * 4111392 * 2
def baseEnd_4111392 : Nat := 234568917227787043732451

theorem tailTrace_4111392 : CollatzResearch.WordTrace tailWord_4111392 prefixEnd_4111392 234568917227787043732451 := by
  unfold tailWord_4111392
  simp only [CollatzResearch.WordTrace]
  refine ⟨74977392760568214348056215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99969857014090952464074953 74977392760568214348056215)
  ·
    refine ⟨112466089140852321522084323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74977392760568214348056215 112466089140852321522084323)
    ·
      refine ⟨168699133711278482283126485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112466089140852321522084323 168699133711278482283126485)
      ·
        refine ⟨3953885946358089428510777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 168699133711278482283126485 3953885946358089428510777)
        ·
          refine ⟨2965414459768567071383083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953885946358089428510777 2965414459768567071383083)
          ·
            refine ⟨4448121689652850607074625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965414459768567071383083 4448121689652850607074625)
            ·
              refine ⟨3336091267239637955305969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448121689652850607074625 3336091267239637955305969)
              ·
                refine ⟨2502068450429728466479477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336091267239637955305969 2502068450429728466479477)
                ·
                  refine ⟨234568917227787043732451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2502068450429728466479477 234568917227787043732451)
                  ·
                    rfl

theorem cell23_4111392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 5].length) (baseStart_4111392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111392 prefixEnd_4111392 := by exact prefixLift 4111392
  have htrace : WordTrace (prefixWord ++ tailWord_4111392) baseStart_4111392 baseEnd_4111392 := by
    simpa [prefixWord, tailWord_4111392, baseEnd_4111392] using wordTrace_append hprefix tailTrace_4111392
  have hstable : (prefixWord ++ tailWord_4111392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111392).length < 2 ^ (prefixWord ++ tailWord_4111392).sum := by decide
  have hdescent : baseEnd_4111392 < baseStart_4111392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111425 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4111425 : Nat := 118140960795 + 4111425 * 2 ^ 59
def prefixEnd_4111425 : Nat := 4983230072969 + 3 ^ 40 * 4111425 * 2
def baseEnd_4111425 : Nat := 2111137199911681764479407

theorem tailTrace_4111425 : CollatzResearch.WordTrace tailWord_4111425 prefixEnd_4111425 2111137199911681764479407 := by
  unfold tailWord_4111425
  simp only [CollatzResearch.WordTrace]
  refine ⟨149955989130016875332063729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99970659420011250221375819 149955989130016875332063729)
  ·
    refine ⟨112466991847512656499047797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149955989130016875332063729 112466991847512656499047797)
    ·
      refine ⟨10543780485704311546785731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112466991847512656499047797 10543780485704311546785731)
      ·
        refine ⟨15815670728556467320178597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10543780485704311546785731 15815670728556467320178597)
        ·
          refine ⟨2965438261604337622533487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15815670728556467320178597 2965438261604337622533487)
          ·
            refine ⟨4448157392406506433800231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965438261604337622533487 4448157392406506433800231)
            ·
              refine ⟨6672236088609759650700347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448157392406506433800231 6672236088609759650700347)
              ·
                refine ⟨10008354132914639476050521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672236088609759650700347 10008354132914639476050521)
                ·
                  refine ⟨7506265599685979607037891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10008354132914639476050521 7506265599685979607037891)
                  ·
                    refine ⟨11259398399528969410556837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7506265599685979607037891 11259398399528969410556837)
                    ·
                      refine ⟨2111137199911681764479407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11259398399528969410556837 2111137199911681764479407)
                      ·
                        rfl

theorem cell23_4111425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4111425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111425 prefixEnd_4111425 := by exact prefixLift 4111425
  have htrace : WordTrace (prefixWord ++ tailWord_4111425) baseStart_4111425 baseEnd_4111425 := by
    simpa [prefixWord, tailWord_4111425, baseEnd_4111425] using wordTrace_append hprefix tailTrace_4111425
  have hstable : (prefixWord ++ tailWord_4111425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111425).length < 2 ^ (prefixWord ++ tailWord_4111425).sum := by decide
  have hdescent : baseEnd_4111425 < baseStart_4111425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111478 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_4111478 : Nat := 118140960795 + 4111478 * 2 ^ 59
def prefixEnd_4111478 : Nat := 4983230072969 + 3 ^ 40 * 4111478 * 2
def baseEnd_4111478 : Nat := 703721471462123352372221

theorem tailTrace_4111478 : CollatzResearch.WordTrace tailWord_4111478 prefixEnd_4111478 703721471462123352372221 := by
  unfold tailWord_4111478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372370137426554086483943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99971948132549910255828725 9372370137426554086483943)
  ·
    refine ⟨14058555206139831129725915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9372370137426554086483943 14058555206139831129725915)
    ·
      refine ⟨21087832809209746694588873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14058555206139831129725915 21087832809209746694588873)
      ·
        refine ⟨15815874606907310020941655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21087832809209746694588873 15815874606907310020941655)
        ·
          refine ⟨23723811910360965031412483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15815874606907310020941655 23723811910360965031412483)
          ·
            refine ⟨35585717865541447547118725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23723811910360965031412483 35585717865541447547118725)
            ·
              refine ⟨6672322099789021415084761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35585717865541447547118725 6672322099789021415084761)
              ·
                refine ⟨5004241574841766061313571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672322099789021415084761 5004241574841766061313571)
                ·
                  refine ⟨7506362362262649091970357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004241574841766061313571 7506362362262649091970357)
                  ·
                    refine ⟨703721471462123352372221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7506362362262649091970357 703721471462123352372221)
                    ·
                      rfl

theorem cell23_4111478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_4111478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111478 prefixEnd_4111478 := by exact prefixLift 4111478
  have htrace : WordTrace (prefixWord ++ tailWord_4111478) baseStart_4111478 baseEnd_4111478 := by
    simpa [prefixWord, tailWord_4111478, baseEnd_4111478] using wordTrace_append hprefix tailTrace_4111478
  have hstable : (prefixWord ++ tailWord_4111478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111478).length < 2 ^ (prefixWord ++ tailWord_4111478).sum := by decide
  have hdescent : baseEnd_4111478 < baseStart_4111478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111484 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_4111484 : Nat := 118140960795 + 4111484 * 2 ^ 59
def prefixEnd_4111484 : Nat := 4983230072969 + 3 ^ 40 * 4111484 * 2
def baseEnd_4111484 : Nat := 2111167495270297033641635

theorem tailTrace_4111484 : CollatzResearch.WordTrace tailWord_4111484 prefixEnd_4111484 2111167495270297033641635 := by
  unfold tailWord_4111484
  simp only [CollatzResearch.WordTrace]
  refine ⟨74979070518401564204230753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99972094024535418938974337 74979070518401564204230753)
  ·
    refine ⟨56234302888801173153173065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74979070518401564204230753 56234302888801173153173065)
    ·
      refine ⟨42175727166600879864879799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56234302888801173153173065 42175727166600879864879799)
      ·
        refine ⟨63263590749901319797319699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42175727166600879864879799 63263590749901319797319699)
        ·
          refine ⟨94895386124851979695979549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63263590749901319797319699 94895386124851979695979549)
          ·
            refine ⟨35585769796819492385992331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94895386124851979695979549 35585769796819492385992331)
            ·
              refine ⟨53378654695229238578988497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35585769796819492385992331 53378654695229238578988497)
              ·
                refine ⟨40033991021421928934241373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53378654695229238578988497 40033991021421928934241373)
                ·
                  refine ⟨15012746633033223350340515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40033991021421928934241373 15012746633033223350340515)
                  ·
                    refine ⟨22519119949549835025510773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15012746633033223350340515 22519119949549835025510773)
                    ·
                      refine ⟨2111167495270297033641635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22519119949549835025510773 2111167495270297033641635)
                      ·
                        rfl

theorem cell23_4111484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_4111484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111484 prefixEnd_4111484 := by exact prefixLift 4111484
  have htrace : WordTrace (prefixWord ++ tailWord_4111484) baseStart_4111484 baseEnd_4111484 := by
    simpa [prefixWord, tailWord_4111484, baseEnd_4111484] using wordTrace_append hprefix tailTrace_4111484
  have hstable : (prefixWord ++ tailWord_4111484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111484).length < 2 ^ (prefixWord ++ tailWord_4111484).sum := by decide
  have hdescent : baseEnd_4111484 < baseStart_4111484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111486 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4111486 : Nat := 118140960795 + 4111486 * 2 ^ 59
def prefixEnd_4111486 : Nat := 4983230072969 + 3 ^ 40 * 4111486 * 2
def baseEnd_4111486 : Nat := 703722840743868675272209

theorem tailTrace_4111486 : CollatzResearch.WordTrace tailWord_4111486 prefixEnd_4111486 703722840743868675272209 := by
  unfold tailWord_4111486
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744776747849485343754289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99972142655197255166689541 18744776747849485343754289)
  ·
    refine ⟨14058582560887114007815717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18744776747849485343754289 14058582560887114007815717)
    ·
      refine ⟨2635984230166333876465447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14058582560887114007815717 2635984230166333876465447)
      ·
        refine ⟨3953976345249500814698171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635984230166333876465447 3953976345249500814698171)
        ·
          refine ⟨5930964517874251222047257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953976345249500814698171 5930964517874251222047257)
          ·
            refine ⟨4448223388405688416535443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5930964517874251222047257 4448223388405688416535443)
            ·
              refine ⟨6672335082608532624803165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448223388405688416535443 6672335082608532624803165)
              ·
                refine ⟨2502125655978199734301187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6672335082608532624803165 2502125655978199734301187)
                ·
                  refine ⟨3753188483967299601451781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502125655978199734301187 3753188483967299601451781)
                  ·
                    refine ⟨703722840743868675272209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753188483967299601451781 703722840743868675272209)
                    ·
                      rfl

theorem cell23_4111486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4111486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111486 prefixEnd_4111486 := by exact prefixLift 4111486
  have htrace : WordTrace (prefixWord ++ tailWord_4111486) baseStart_4111486 baseEnd_4111486 := by
    simpa [prefixWord, tailWord_4111486, baseEnd_4111486] using wordTrace_append hprefix tailTrace_4111486
  have hstable : (prefixWord ++ tailWord_4111486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111486).length < 2 ^ (prefixWord ++ tailWord_4111486).sum := by decide
  have hdescent : baseEnd_4111486 < baseStart_4111486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111492 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_4111492 : Nat := 118140960795 + 4111492 * 2 ^ 59
def prefixEnd_4111492 : Nat := 4983230072969 + 3 ^ 40 * 4111492 * 2
def baseEnd_4111492 : Nat := 2111171603115533002341599

theorem tailTrace_4111492 : CollatzResearch.WordTrace tailWord_4111492 prefixEnd_4111492 2111171603115533002341599 := by
  unfold tailWord_4111492
  simp only [CollatzResearch.WordTrace]
  refine ⟨74979216410387072887376365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99972288547182763849835153 74979216410387072887376365)
  ·
    refine ⟨28117206153895152332766137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74979216410387072887376365 28117206153895152332766137)
    ·
      refine ⟨21087904615421364249574603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28117206153895152332766137 21087904615421364249574603)
      ·
        refine ⟨31631856923132046374361905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21087904615421364249574603 31631856923132046374361905)
        ·
          refine ⟨23723892692349034780771429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31631856923132046374361905 23723892692349034780771429)
          ·
            refine ⟨4448229879815444021394643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23723892692349034780771429 4448229879815444021394643)
            ·
              refine ⟨6672344819723166032091965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448229879815444021394643 6672344819723166032091965)
              ·
                refine ⟨2502129307396187262034487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6672344819723166032091965 2502129307396187262034487)
                ·
                  refine ⟨3753193961094280893051731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502129307396187262034487 3753193961094280893051731)
                  ·
                    refine ⟨5629790941641421339577597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3753193961094280893051731 5629790941641421339577597)
                    ·
                      refine ⟨2111171603115533002341599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629790941641421339577597 2111171603115533002341599)
                      ·
                        rfl

theorem cell23_4111492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_4111492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111492 prefixEnd_4111492 := by exact prefixLift 4111492
  have htrace : WordTrace (prefixWord ++ tailWord_4111492) baseStart_4111492 baseEnd_4111492 := by
    simpa [prefixWord, tailWord_4111492, baseEnd_4111492] using wordTrace_append hprefix tailTrace_4111492
  have hstable : (prefixWord ++ tailWord_4111492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111492).length < 2 ^ (prefixWord ++ tailWord_4111492).sum := by decide
  have hdescent : baseEnd_4111492 < baseStart_4111492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111518 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4111518 : Nat := 118140960795 + 4111518 * 2 ^ 59
def prefixEnd_4111518 : Nat := 4983230072969 + 3 ^ 40 * 4111518 * 2
def baseEnd_4111518 : Nat := 2111184953612549900616479

theorem tailTrace_4111518 : CollatzResearch.WordTrace tailWord_4111518 prefixEnd_4111518 2111184953612549900616479 := by
  unfold tailWord_4111518
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744922639834994026899901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99972920745786634810132805 18744922639834994026899901)
  ·
    refine ⟨7029345989938122760087463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18744922639834994026899901 7029345989938122760087463)
    ·
      refine ⟨10544018984907184140131195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7029345989938122760087463 10544018984907184140131195)
      ·
        refine ⟨15816028477360776210196793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10544018984907184140131195 15816028477360776210196793)
        ·
          refine ⟨11862021358020582157647595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15816028477360776210196793 11862021358020582157647595)
          ·
            refine ⟨17793032037030873236471393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11862021358020582157647595 17793032037030873236471393)
            ·
              refine ⟨13344774027773154927353545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17793032037030873236471393 13344774027773154927353545)
              ·
                refine ⟨10008580520829866195515159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13344774027773154927353545 10008580520829866195515159)
                ·
                  refine ⟨15012870781244799293272739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10008580520829866195515159 15012870781244799293272739)
                  ·
                    refine ⟨22519306171867198939909109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15012870781244799293272739 22519306171867198939909109)
                    ·
                      refine ⟨2111184953612549900616479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22519306171867198939909109 2111184953612549900616479)
                      ·
                        rfl

theorem cell23_4111518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4111518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111518 prefixEnd_4111518 := by exact prefixLift 4111518
  have htrace : WordTrace (prefixWord ++ tailWord_4111518) baseStart_4111518 baseEnd_4111518 := by
    simpa [prefixWord, tailWord_4111518, baseEnd_4111518] using wordTrace_append hprefix tailTrace_4111518
  have hstable : (prefixWord ++ tailWord_4111518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111518).length < 2 ^ (prefixWord ++ tailWord_4111518).sum := by decide
  have hdescent : baseEnd_4111518 < baseStart_4111518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111525 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_4111525 : Nat := 118140960795 + 4111525 * 2 ^ 59
def prefixEnd_4111525 : Nat := 4983230072969 + 3 ^ 40 * 4111525 * 2
def baseEnd_4111525 : Nat := 703729515992377124409649

theorem tailTrace_4111525 : CollatzResearch.WordTrace tailWord_4111525 prefixEnd_4111525 703729515992377124409649 := by
  unfold tailWord_4111525
  simp only [CollatzResearch.WordTrace]
  refine ⟨149959636429654592410704029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99973090953103061607136019 149959636429654592410704029)
  ·
    refine ⟨56234863661120472154014011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149959636429654592410704029 56234863661120472154014011)
    ·
      refine ⟨84352295491680708231021017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56234863661120472154014011 84352295491680708231021017)
      ·
        refine ⟨63264221618760531173265763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84352295491680708231021017 63264221618760531173265763)
        ·
          refine ⟨94896332428140796759898645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63264221618760531173265763 94896332428140796759898645)
          ·
            refine ⟨4448265582569099848120249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94896332428140796759898645 4448265582569099848120249)
            ·
              refine ⟨3336199186926824886090187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448265582569099848120249 3336199186926824886090187)
              ·
                refine ⟨5004298780390237329135281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3336199186926824886090187 5004298780390237329135281)
                ·
                  refine ⟨3753224085292677996851461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004298780390237329135281 3753224085292677996851461)
                  ·
                    refine ⟨703729515992377124409649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753224085292677996851461 703729515992377124409649)
                    ·
                      rfl

theorem cell23_4111525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_4111525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111525 prefixEnd_4111525 := by exact prefixLift 4111525
  have htrace : WordTrace (prefixWord ++ tailWord_4111525) baseStart_4111525 baseEnd_4111525 := by
    simpa [prefixWord, tailWord_4111525, baseEnd_4111525] using wordTrace_append hprefix tailTrace_4111525
  have hstable : (prefixWord ++ tailWord_4111525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111525).length < 2 ^ (prefixWord ++ tailWord_4111525).sum := by decide
  have hdescent : baseEnd_4111525 < baseStart_4111525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111544 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_4111544 : Nat := 118140960795 + 4111544 * 2 ^ 59
def prefixEnd_4111544 : Nat := 4983230072969 + 3 ^ 40 * 4111544 * 2
def baseEnd_4111544 : Nat := 2111198304109566798891359

theorem tailTrace_4111544 : CollatzResearch.WordTrace tailWord_4111544 prefixEnd_4111544 2111198304109566798891359 := by
  unfold tailWord_4111544
  simp only [CollatzResearch.WordTrace]
  refine ⟨74980164708292879327822843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99973552944390505770430457 74980164708292879327822843)
  ·
    refine ⟨112470247062439318991734265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74980164708292879327822843 112470247062439318991734265)
    ·
      refine ⟨84352685296829489243800699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112470247062439318991734265 84352685296829489243800699)
      ·
        refine ⟨126529027945244233865701049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84352685296829489243800699 126529027945244233865701049)
        ·
          refine ⟨94896770958933175399275787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126529027945244233865701049 94896770958933175399275787)
          ·
            refine ⟨142345156438399763098913681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94896770958933175399275787 142345156438399763098913681)
            ·
              refine ⟨106758867328799822324185261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142345156438399763098913681 106758867328799822324185261)
              ·
                refine ⟨40034575248299933371569473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106758867328799822324185261 40034575248299933371569473)
                ·
                  refine ⟨30025931436224950028677105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40034575248299933371569473 30025931436224950028677105)
                  ·
                    refine ⟨22519448577168712521507829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30025931436224950028677105 22519448577168712521507829)
                    ·
                      refine ⟨2111198304109566798891359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22519448577168712521507829 2111198304109566798891359)
                      ·
                        rfl

theorem cell23_4111544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_4111544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111544 prefixEnd_4111544 := by exact prefixLift 4111544
  have htrace : WordTrace (prefixWord ++ tailWord_4111544) baseStart_4111544 baseEnd_4111544 := by
    simpa [prefixWord, tailWord_4111544, baseEnd_4111544] using wordTrace_append hprefix tailTrace_4111544
  have hstable : (prefixWord ++ tailWord_4111544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111544).length < 2 ^ (prefixWord ++ tailWord_4111544).sum := by decide
  have hdescent : baseEnd_4111544 < baseStart_4111544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111548 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_4111548 : Nat := 118140960795 + 4111548 * 2 ^ 59
def prefixEnd_4111548 : Nat := 4983230072969 + 3 ^ 40 * 4111548 * 2
def baseEnd_4111548 : Nat := 2111200358032184783241341

theorem tailTrace_4111548 : CollatzResearch.WordTrace tailWord_4111548 prefixEnd_4111548 2111200358032184783241341 := by
  unfold tailWord_4111548
  simp only [CollatzResearch.WordTrace]
  refine ⟨74980237654285633669395649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99973650205714178225860865 74980237654285633669395649)
  ·
    refine ⟨56235178240714225252046737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74980237654285633669395649 56235178240714225252046737)
    ·
      refine ⟨42176383680535668939035053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56235178240714225252046737 42176383680535668939035053)
      ·
        refine ⟨15816143880200875852138145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42176383680535668939035053 15816143880200875852138145)
        ·
          refine ⟨11862107910150656889103609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15816143880200875852138145 11862107910150656889103609)
          ·
            refine ⟨8896580932612992666827707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11862107910150656889103609 8896580932612992666827707)
            ·
              refine ⟨13344871398919489000241561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8896580932612992666827707 13344871398919489000241561)
              ·
                refine ⟨10008653549189616750181171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13344871398919489000241561 10008653549189616750181171)
                ·
                  refine ⟨15012980323784425125271757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10008653549189616750181171 15012980323784425125271757)
                  ·
                    refine ⟨5629867621419159421976909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15012980323784425125271757 5629867621419159421976909)
                    ·
                      refine ⟨2111200358032184783241341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629867621419159421976909 2111200358032184783241341)
                      ·
                        rfl

theorem cell23_4111548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_4111548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111548 prefixEnd_4111548 := by exact prefixLift 4111548
  have htrace : WordTrace (prefixWord ++ tailWord_4111548) baseStart_4111548 baseEnd_4111548 := by
    simpa [prefixWord, tailWord_4111548, baseEnd_4111548] using wordTrace_append hprefix tailTrace_4111548
  have hstable : (prefixWord ++ tailWord_4111548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111548).length < 2 ^ (prefixWord ++ tailWord_4111548).sum := by decide
  have hdescent : baseEnd_4111548 < baseStart_4111548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111566 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_4111566 : Nat := 118140960795 + 4111566 * 2 ^ 59
def prefixEnd_4111566 : Nat := 4983230072969 + 3 ^ 40 * 4111566 * 2
def baseEnd_4111566 : Nat := 2111209600683965712816259

theorem tailTrace_4111566 : CollatzResearch.WordTrace tailWord_4111566 prefixEnd_4111566 2111209600683965712816259 := by
  unfold tailWord_4111566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18745141477813257051618319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99974087881670704275297701 18745141477813257051618319)
  ·
    refine ⟨28117712216719885577427479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18745141477813257051618319 28117712216719885577427479)
    ·
      refine ⟨42176568325079828366141219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28117712216719885577427479 42176568325079828366141219)
      ·
        refine ⟨63264852487619742549211829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42176568325079828366141219 63264852487619742549211829)
        ·
          refine ⟨5931079920714350863988609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63264852487619742549211829 5931079920714350863988609)
          ·
            refine ⟨4448309940535763147991457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5931079920714350863988609 4448309940535763147991457)
            ·
              refine ⟨3336232455401822360993593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448309940535763147991457 3336232455401822360993593)
              ·
                refine ⟨2502174341551366770745195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336232455401822360993593 2502174341551366770745195)
                ·
                  refine ⟨3753261512327050156117793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502174341551366770745195 3753261512327050156117793)
                  ·
                    refine ⟨2814946134245287617088345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3753261512327050156117793 2814946134245287617088345)
                    ·
                      refine ⟨2111209600683965712816259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814946134245287617088345 2111209600683965712816259)
                      ·
                        rfl

theorem cell23_4111566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_4111566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111566 prefixEnd_4111566 := by exact prefixLift 4111566
  have htrace : WordTrace (prefixWord ++ tailWord_4111566) baseStart_4111566 baseEnd_4111566 := by
    simpa [prefixWord, tailWord_4111566, baseEnd_4111566] using wordTrace_append hprefix tailTrace_4111566
  have hstable : (prefixWord ++ tailWord_4111566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111566).length < 2 ^ (prefixWord ++ tailWord_4111566).sum := by decide
  have hdescent : baseEnd_4111566 < baseStart_4111566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111588 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_4111588 : Nat := 118140960795 + 4111588 * 2 ^ 59
def prefixEnd_4111588 : Nat := 4983230072969 + 3 ^ 40 * 4111588 * 2
def baseEnd_4111588 : Nat := 2111220897258364626741157

theorem tailTrace_4111588 : CollatzResearch.WordTrace tailWord_4111588 prefixEnd_4111588 2111220897258364626741157 := by
  unfold tailWord_4111588
  simp only [CollatzResearch.WordTrace]
  refine ⟨74980967114213177085123709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99974622818950902780164945 74980967114213177085123709)
  ·
    refine ⟨28117862667829941406921391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74980967114213177085123709 28117862667829941406921391)
    ·
      refine ⟨42176794001744912110382087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28117862667829941406921391 42176794001744912110382087)
      ·
        refine ⟨63265191002617368165573131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42176794001744912110382087 63265191002617368165573131)
        ·
          refine ⟨94897786503926052248359697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63265191002617368165573131 94897786503926052248359697)
          ·
            refine ⟨71173339877944539186269773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94897786503926052248359697 71173339877944539186269773)
            ·
              refine ⟨26690002454229202194851165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71173339877944539186269773 26690002454229202194851165)
              ·
                refine ⟨10008750920335950823069187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26690002454229202194851165 10008750920335950823069187)
                ·
                  refine ⟨15013126380503926234603781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10008750920335950823069187 15013126380503926234603781)
                  ·
                    refine ⟨2814961196344486168988209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15013126380503926234603781 2814961196344486168988209)
                    ·
                      refine ⟨2111220897258364626741157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2814961196344486168988209 2111220897258364626741157)
                      ·
                        rfl

theorem cell23_4111588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_4111588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111588 prefixEnd_4111588 := by exact prefixLift 4111588
  have htrace : WordTrace (prefixWord ++ tailWord_4111588) baseStart_4111588 baseEnd_4111588 := by
    simpa [prefixWord, tailWord_4111588, baseEnd_4111588] using wordTrace_append hprefix tailTrace_4111588
  have hstable : (prefixWord ++ tailWord_4111588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111588).length < 2 ^ (prefixWord ++ tailWord_4111588).sum := by decide
  have hdescent : baseEnd_4111588 < baseStart_4111588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111621 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_4111621 : Nat := 118140960795 + 4111621 * 2 ^ 59
def prefixEnd_4111621 : Nat := 4983230072969 + 3 ^ 40 * 4111621 * 2
def baseEnd_4111621 : Nat := 2111237842119962997628505

theorem tailTrace_4111621 : CollatzResearch.WordTrace tailWord_4111621 prefixEnd_4111621 2111237842119962997628505 := by
  unfold tailWord_4111621
  simp only [CollatzResearch.WordTrace]
  refine ⟨149963137837306800806198717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99975425224871200537465811 149963137837306800806198717)
  ·
    refine ⟨56236176688990050302324519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149963137837306800806198717 56236176688990050302324519)
    ·
      refine ⟨84354265033485075453486779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56236176688990050302324519 84354265033485075453486779)
      ·
        refine ⟨126531397550227613180230169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84354265033485075453486779 126531397550227613180230169)
        ·
          refine ⟨94898548162670709885172627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126531397550227613180230169 94898548162670709885172627)
          ·
            refine ⟨142347822244006064827758941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94898548162670709885172627 142347822244006064827758941)
            ·
              refine ⟨53380433341502274310409603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142347822244006064827758941 53380433341502274310409603)
              ·
                refine ⟨80070650012253411465614405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53380433341502274310409603 80070650012253411465614405)
                ·
                  refine ⟨15013246877297514649802701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80070650012253411465614405 15013246877297514649802701)
                  ·
                    refine ⟨5629967578986567993676013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15013246877297514649802701 5629967578986567993676013)
                    ·
                      refine ⟨2111237842119962997628505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5629967578986567993676013 2111237842119962997628505)
                      ·
                        rfl

theorem cell23_4111621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_4111621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111621 prefixEnd_4111621 := by exact prefixLift 4111621
  have htrace : WordTrace (prefixWord ++ tailWord_4111621) baseStart_4111621 baseEnd_4111621 := by
    simpa [prefixWord, tailWord_4111621, baseEnd_4111621] using wordTrace_append hprefix tailTrace_4111621
  have hstable : (prefixWord ++ tailWord_4111621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111621).length < 2 ^ (prefixWord ++ tailWord_4111621).sum := by decide
  have hdescent : baseEnd_4111621 < baseStart_4111621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111628 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 5]
def baseStart_4111628 : Nat := 118140960795 + 4111628 * 2 ^ 59
def prefixEnd_4111628 : Nat := 4983230072969 + 3 ^ 40 * 4111628 * 2
def baseEnd_4111628 : Nat := 234582381831616052248997

theorem tailTrace_4111628 : CollatzResearch.WordTrace tailWord_4111628 prefixEnd_4111628 234582381831616052248997 := by
  unfold tailWord_4111628
  simp only [CollatzResearch.WordTrace]
  refine ⟨74981696574140720500851769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99975595432187627334469025 74981696574140720500851769)
  ·
    refine ⟨56236272430605540375638827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74981696574140720500851769 56236272430605540375638827)
    ·
      refine ⟨84354408645908310563458241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56236272430605540375638827 84354408645908310563458241)
      ·
        refine ⟨63265806484431232922593681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84354408645908310563458241 63265806484431232922593681)
        ·
          refine ⟨47449354863323424691945261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63265806484431232922593681 47449354863323424691945261)
          ·
            refine ⟨17793508073746284259479473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47449354863323424691945261 17793508073746284259479473)
            ·
              refine ⟨13345131055309713194609605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17793508073746284259479473 13345131055309713194609605)
              ·
                refine ⟨2502212072870571223989301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13345131055309713194609605 2502212072870571223989301)
                ·
                  refine ⟨234582381831616052248997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2502212072870571223989301 234582381831616052248997)
                  ·
                    rfl

theorem cell23_4111628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_4111628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111628 prefixEnd_4111628 := by exact prefixLift 4111628
  have htrace : WordTrace (prefixWord ++ tailWord_4111628) baseStart_4111628 baseEnd_4111628 := by
    simpa [prefixWord, tailWord_4111628, baseEnd_4111628] using wordTrace_append hprefix tailTrace_4111628
  have hstable : (prefixWord ++ tailWord_4111628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111628).length < 2 ^ (prefixWord ++ tailWord_4111628).sum := by decide
  have hdescent : baseEnd_4111628 < baseStart_4111628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111658 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4111658 : Nat := 118140960795 + 4111658 * 2 ^ 59
def prefixEnd_4111658 : Nat := 4983230072969 + 3 ^ 40 * 4111658 * 2
def baseEnd_4111658 : Nat := 703752280301393117621945

theorem tailTrace_4111658 : CollatzResearch.WordTrace tailWord_4111658 prefixEnd_4111658 703752280301393117621945 := by
  unfold tailWord_4111658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37491121834543189031323907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99976324892115170750197085 37491121834543189031323907)
  ·
    refine ⟨56236682751814783546985861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37491121834543189031323907 56236682751814783546985861)
    ·
      refine ⟨10544378015965271915059849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56236682751814783546985861 10544378015965271915059849)
      ·
        refine ⟨7908283511973953936294887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10544378015965271915059849 7908283511973953936294887)
        ·
          refine ⟨11862425267960930904442331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908283511973953936294887 11862425267960930904442331)
          ·
            refine ⟨17793637901941396356663497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11862425267960930904442331 17793637901941396356663497)
            ·
              refine ⟨13345228426456047267497623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17793637901941396356663497 13345228426456047267497623)
              ·
                refine ⟨20017842639684070901246435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13345228426456047267497623 20017842639684070901246435)
                ·
                  refine ⟨30026763959526106351869653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20017842639684070901246435 30026763959526106351869653)
                  ·
                    refine ⟨703752280301393117621945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30026763959526106351869653 703752280301393117621945)
                    ·
                      rfl

theorem cell23_4111658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4111658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111658 prefixEnd_4111658 := by exact prefixLift 4111658
  have htrace : WordTrace (prefixWord ++ tailWord_4111658) baseStart_4111658 baseEnd_4111658 := by
    simpa [prefixWord, tailWord_4111658, baseEnd_4111658] using wordTrace_append hprefix tailTrace_4111658
  have hstable : (prefixWord ++ tailWord_4111658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111658).length < 2 ^ (prefixWord ++ tailWord_4111658).sum := by decide
  have hdescent : baseEnd_4111658 < baseStart_4111658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111668 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4111668 : Nat := 118140960795 + 4111668 * 2 ^ 59
def prefixEnd_4111668 : Nat := 4983230072969 + 3 ^ 40 * 4111668 * 2
def baseEnd_4111668 : Nat := 2111261975710724313740789

theorem tailTrace_4111668 : CollatzResearch.WordTrace tailWord_4111668 prefixEnd_4111668 2111261975710724313740789 := by
  unfold tailWord_4111668
  simp only [CollatzResearch.WordTrace]
  refine ⟨74982426034068263916579829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99976568045424351888773105 74982426034068263916579829)
  ·
    refine ⟨7029602440693899742179359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74982426034068263916579829 7029602440693899742179359)
    ·
      refine ⟨10544403661040849613269039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7029602440693899742179359 10544403661040849613269039)
      ·
        refine ⟨15816605491561274419903559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10544403661040849613269039 15816605491561274419903559)
        ·
          refine ⟨23724908237341911629855339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15816605491561274419903559 23724908237341911629855339)
          ·
            refine ⟨35587362356012867444783009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23724908237341911629855339 35587362356012867444783009)
            ·
              refine ⟨26690521767009650583587257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35587362356012867444783009 26690521767009650583587257)
              ·
                refine ⟨20017891325257237937690443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26690521767009650583587257 20017891325257237937690443)
                ·
                  refine ⟨30026836987885856906535665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20017891325257237937690443 30026836987885856906535665)
                  ·
                    refine ⟨22520127740914392679901749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30026836987885856906535665 22520127740914392679901749)
                    ·
                      refine ⟨2111261975710724313740789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22520127740914392679901749 2111261975710724313740789)
                      ·
                        rfl

theorem cell23_4111668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4111668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111668 prefixEnd_4111668 := by exact prefixLift 4111668
  have htrace : WordTrace (prefixWord ++ tailWord_4111668) baseStart_4111668 baseEnd_4111668 := by
    simpa [prefixWord, tailWord_4111668, baseEnd_4111668] using wordTrace_append hprefix tailTrace_4111668
  have hstable : (prefixWord ++ tailWord_4111668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111668).length < 2 ^ (prefixWord ++ tailWord_4111668).sum := by decide
  have hdescent : baseEnd_4111668 < baseStart_4111668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111698 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_4111698 : Nat := 118140960795 + 4111698 * 2 ^ 59
def prefixEnd_4111698 : Nat := 4983230072969 + 3 ^ 40 * 4111698 * 2
def baseEnd_4111698 : Nat := 2111277380130359196365651

theorem tailTrace_4111698 : CollatzResearch.WordTrace tailWord_4111698 prefixEnd_4111698 2111277380130359196365651 := by
  unfold tailWord_4111698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37491486564506960739187937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99977297505351895304501165 37491486564506960739187937)
  ·
    refine ⟨28118614923380220554390953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37491486564506960739187937 28118614923380220554390953)
    ·
      refine ⟨21088961192535165415793215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28118614923380220554390953 21088961192535165415793215)
      ·
        refine ⟨31633441788802748123689823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21088961192535165415793215 31633441788802748123689823)
        ·
          refine ⟨47450162683204122185534735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31633441788802748123689823 47450162683204122185534735)
          ·
            refine ⟨71175244024806183278302103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47450162683204122185534735 71175244024806183278302103)
            ·
              refine ⟨106762866037209274917453155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71175244024806183278302103 106762866037209274917453155)
              ·
                refine ⟨160144299055813912376179733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106762866037209274917453155 160144299055813912376179733)
                ·
                  refine ⟨7506764018241277142633425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160144299055813912376179733 7506764018241277142633425)
                  ·
                    refine ⟨5630073013680957856975069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7506764018241277142633425 5630073013680957856975069)
                    ·
                      refine ⟨2111277380130359196365651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5630073013680957856975069 2111277380130359196365651)
                      ·
                        rfl

theorem cell23_4111698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_4111698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111698 prefixEnd_4111698 := by exact prefixLift 4111698
  have htrace : WordTrace (prefixWord ++ tailWord_4111698) baseStart_4111698 baseEnd_4111698 := by
    simpa [prefixWord, tailWord_4111698, baseEnd_4111698] using wordTrace_append hprefix tailTrace_4111698
  have hstable : (prefixWord ++ tailWord_4111698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111698).length < 2 ^ (prefixWord ++ tailWord_4111698).sum := by decide
  have hdescent : baseEnd_4111698 < baseStart_4111698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111709 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4111709 : Nat := 118140960795 + 4111709 * 2 ^ 59
def prefixEnd_4111709 : Nat := 4983230072969 + 3 ^ 40 * 4111709 * 2
def baseEnd_4111709 : Nat := 703761009472519551109367

theorem tailTrace_4111709 : CollatzResearch.WordTrace tailWord_4111709 prefixEnd_4111709 703761009472519551109367 := by
  unfold tailWord_4111709
  simp only [CollatzResearch.WordTrace]
  refine ⟨149966347460987991835402181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99977564973991994556934787 149966347460987991835402181)
  ·
    refine ⟨28118690148935248469137909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149966347460987991835402181 28118690148935248469137909)
    ·
      refine ⟨2636127201462679543981679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28118690148935248469137909 2636127201462679543981679)
      ·
        refine ⟨3954190802194019315972519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636127201462679543981679 3954190802194019315972519)
        ·
          refine ⟨5931286203291028973958779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954190802194019315972519 5931286203291028973958779)
          ·
            refine ⟨8896929304936543460938169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931286203291028973958779 8896929304936543460938169)
            ·
              refine ⟨6672696978702407595703627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8896929304936543460938169 6672696978702407595703627)
              ·
                refine ⟨10009045468053611393555441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672696978702407595703627 10009045468053611393555441)
                ·
                  refine ⟨7506784101040208545166581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10009045468053611393555441 7506784101040208545166581)
                  ·
                    refine ⟨703761009472519551109367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7506784101040208545166581 703761009472519551109367)
                    ·
                      rfl

theorem cell23_4111709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4111709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111709 prefixEnd_4111709 := by exact prefixLift 4111709
  have htrace : WordTrace (prefixWord ++ tailWord_4111709) baseStart_4111709 baseEnd_4111709 := by
    simpa [prefixWord, tailWord_4111709, baseEnd_4111709] using wordTrace_append hprefix tailTrace_4111709
  have hstable : (prefixWord ++ tailWord_4111709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111709).length < 2 ^ (prefixWord ++ tailWord_4111709).sum := by decide
  have hdescent : baseEnd_4111709 < baseStart_4111709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111715 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 3]
def baseStart_4111715 : Nat := 118140960795 + 4111715 * 2 ^ 59
def prefixEnd_4111715 : Nat := 4983230072969 + 3 ^ 40 * 4111715 * 2
def baseEnd_4111715 : Nat := 2111286109301485629853073

theorem tailTrace_4111715 : CollatzResearch.WordTrace tailWord_4111715 prefixEnd_4111715 2111286109301485629853073 := by
  unfold tailWord_4111715
  simp only [CollatzResearch.WordTrace]
  refine ⟨149966566298966254860120599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99977710865977503240080399 149966566298966254860120599)
  ·
    refine ⟨224949849448449382290180899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149966566298966254860120599 224949849448449382290180899)
    ·
      refine ⟨337424774172674073435271349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224949849448449382290180899 337424774172674073435271349)
      ·
        refine ⟨31633572578688194384556689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337424774172674073435271349 31633572578688194384556689)
        ·
          refine ⟨23725179434016145788417517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31633572578688194384556689 23725179434016145788417517)
          ·
            refine ⟨8896942287756054670656569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23725179434016145788417517 8896942287756054670656569)
            ·
              refine ⟨6672706715817041002992427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8896942287756054670656569 6672706715817041002992427)
              ·
                refine ⟨10009060073725561504488641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672706715817041002992427 10009060073725561504488641)
                ·
                  refine ⟨7506795055294171128366481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10009060073725561504488641 7506795055294171128366481)
                  ·
                    refine ⟨5630096291470628346274861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7506795055294171128366481 5630096291470628346274861)
                    ·
                      refine ⟨2111286109301485629853073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5630096291470628346274861 2111286109301485629853073)
                      ·
                        rfl

theorem cell23_4111715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_4111715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111715 prefixEnd_4111715 := by exact prefixLift 4111715
  have htrace : WordTrace (prefixWord ++ tailWord_4111715) baseStart_4111715 baseEnd_4111715 := by
    simpa [prefixWord, tailWord_4111715, baseEnd_4111715] using wordTrace_append hprefix tailTrace_4111715
  have hstable : (prefixWord ++ tailWord_4111715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111715).length < 2 ^ (prefixWord ++ tailWord_4111715).sum := by decide
  have hdescent : baseEnd_4111715 < baseStart_4111715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111731 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 7, 5]
def baseStart_4111731 : Nat := 118140960795 + 4111731 * 2 ^ 59
def prefixEnd_4111731 : Nat := 4983230072969 + 3 ^ 40 * 4111731 * 2
def baseEnd_4111731 : Nat := 703764774997319189084333

theorem tailTrace_4111731 : CollatzResearch.WordTrace tailWord_4111731 prefixEnd_4111731 703764774997319189084333 := by
  unfold tailWord_4111731
  simp only [CollatzResearch.WordTrace]
  refine ⟨149967149866908289592703047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99978099911272193061802031 149967149866908289592703047)
  ·
    refine ⟨224950724800362434389054571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149967149866908289592703047 224950724800362434389054571)
    ·
      refine ⟨337426087200543651583581857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224950724800362434389054571 337426087200543651583581857)
      ·
        refine ⟨253069565400407738687686393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337426087200543651583581857 253069565400407738687686393)
        ·
          refine ⟨189802174050305804015764795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253069565400407738687686393 189802174050305804015764795)
          ·
            refine ⟨284703261075458706023647193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189802174050305804015764795 284703261075458706023647193)
            ·
              refine ⟨213527445806594029517735395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284703261075458706023647193 213527445806594029517735395)
              ·
                refine ⟨320291168709891044276603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213527445806594029517735395 320291168709891044276603093)
                ·
                  refine ⟨7506824266638071350232885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 320291168709891044276603093 7506824266638071350232885)
                  ·
                    refine ⟨703764774997319189084333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7506824266638071350232885 703764774997319189084333)
                    ·
                      rfl

theorem cell23_4111731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 5].length) (baseStart_4111731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111731 prefixEnd_4111731 := by exact prefixLift 4111731
  have htrace : WordTrace (prefixWord ++ tailWord_4111731) baseStart_4111731 baseEnd_4111731 := by
    simpa [prefixWord, tailWord_4111731, baseEnd_4111731] using wordTrace_append hprefix tailTrace_4111731
  have hstable : (prefixWord ++ tailWord_4111731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111731).length < 2 ^ (prefixWord ++ tailWord_4111731).sum := by decide
  have hdescent : baseEnd_4111731 < baseStart_4111731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111748 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_4111748 : Nat := 118140960795 + 4111748 * 2 ^ 59
def prefixEnd_4111748 : Nat := 4983230072969 + 3 ^ 40 * 4111748 * 2
def baseEnd_4111748 : Nat := 703767684721028000246807

theorem tailTrace_4111748 : CollatzResearch.WordTrace tailWord_4111748 prefixEnd_4111748 703767684721028000246807 := by
  unfold tailWord_4111748
  simp only [CollatzResearch.WordTrace]
  refine ⟨74983884953923350748035949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99978513271897800997381265 74983884953923350748035949)
  ·
    refine ⟨28118956857721256530513481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74983884953923350748035949 28118956857721256530513481)
    ·
      refine ⟨21089217643290942397885111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28118956857721256530513481 21089217643290942397885111)
      ·
        refine ⟨31633826464936413596827667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21089217643290942397885111 31633826464936413596827667)
        ·
          refine ⟨47450739697404620395241501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31633826464936413596827667 47450739697404620395241501)
          ·
            refine ⟨17794027386526732648215563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47450739697404620395241501 17794027386526732648215563)
            ·
              refine ⟨26691041079790098972323345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17794027386526732648215563 26691041079790098972323345)
              ·
                refine ⟨20018280809842574229242509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26691041079790098972323345 20018280809842574229242509)
                ·
                  refine ⟨7506855303690965335965941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20018280809842574229242509 7506855303690965335965941)
                  ·
                    refine ⟨703767684721028000246807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7506855303690965335965941 703767684721028000246807)
                    ·
                      rfl

theorem cell23_4111748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_4111748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111748 prefixEnd_4111748 := by exact prefixLift 4111748
  have htrace : WordTrace (prefixWord ++ tailWord_4111748) baseStart_4111748 baseEnd_4111748 := by
    simpa [prefixWord, tailWord_4111748, baseEnd_4111748] using wordTrace_append hprefix tailTrace_4111748
  have hstable : (prefixWord ++ tailWord_4111748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111748).length < 2 ^ (prefixWord ++ tailWord_4111748).sum := by decide
  have hdescent : baseEnd_4111748 < baseStart_4111748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111761 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 5, 6]
def baseStart_4111761 : Nat := 118140960795 + 4111761 * 2 ^ 59
def prefixEnd_4111761 : Nat := 4983230072969 + 3 ^ 40 * 4111761 * 2
def baseEnd_4111761 : Nat := 703769909803864149959287

theorem tailTrace_4111761 : CollatzResearch.WordTrace tailWord_4111761 prefixEnd_4111761 703769909803864149959287 := by
  unfold tailWord_4111761
  simp only [CollatzResearch.WordTrace]
  refine ⟨149968244056799604716295137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99978829371199736477530091 149968244056799604716295137)
  ·
    refine ⟨112476183042599703537221353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149968244056799604716295137 112476183042599703537221353)
    ·
      refine ⟨84357137281949777652916015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112476183042599703537221353 84357137281949777652916015)
      ·
        refine ⟨126535705922924666479374023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84357137281949777652916015 126535705922924666479374023)
        ·
          refine ⟨189803558884386999719061035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126535705922924666479374023 189803558884386999719061035)
          ·
            refine ⟨284705338326580499578591553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189803558884386999719061035 284705338326580499578591553)
            ·
              refine ⟨213529003744935374683943665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284705338326580499578591553 213529003744935374683943665)
              ·
                refine ⟨160146752808701531012957749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213529003744935374683943665 160146752808701531012957749)
                ·
                  refine ⟨15013758075815768532464789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160146752808701531012957749 15013758075815768532464789)
                  ·
                    refine ⟨703769909803864149959287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15013758075815768532464789 703769909803864149959287)
                    ·
                      rfl

theorem cell23_4111761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_4111761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111761 prefixEnd_4111761 := by exact prefixLift 4111761
  have htrace : WordTrace (prefixWord ++ tailWord_4111761) baseStart_4111761 baseEnd_4111761 := by
    simpa [prefixWord, tailWord_4111761, baseEnd_4111761] using wordTrace_append hprefix tailTrace_4111761
  have hstable : (prefixWord ++ tailWord_4111761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111761).length < 2 ^ (prefixWord ++ tailWord_4111761).sum := by decide
  have hdescent : baseEnd_4111761 < baseStart_4111761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111812 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_4111812 : Nat := 118140960795 + 4111812 * 2 ^ 59
def prefixEnd_4111812 : Nat := 4983230072969 + 3 ^ 40 * 4111812 * 2
def baseEnd_4111812 : Nat := 703778638974990583446709

theorem tailTrace_4111812 : CollatzResearch.WordTrace tailWord_4111812 prefixEnd_4111812 703778638974990583446709 := by
  unfold tailWord_4111812
  simp only [CollatzResearch.WordTrace]
  refine ⟨74985052089807420213200845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99980069453076560284267793 74985052089807420213200845)
  ·
    refine ⟨28119394533677782579950317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74985052089807420213200845 28119394533677782579950317)
    ·
      refine ⟨10544772950129168467481369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28119394533677782579950317 10544772950129168467481369)
      ·
        refine ⟨7908579712596876350611027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10544772950129168467481369 7908579712596876350611027)
        ·
          refine ⟨11862869568895314525916541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7908579712596876350611027 11862869568895314525916541)
          ·
            refine ⟨4448576088335742947218703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11862869568895314525916541 4448576088335742947218703)
            ·
              refine ⟨6672864132503614420828055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448576088335742947218703 6672864132503614420828055)
              ·
                refine ⟨10009296198755421631242083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672864132503614420828055 10009296198755421631242083)
                ·
                  refine ⟨15013944298133132446863125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009296198755421631242083 15013944298133132446863125)
                  ·
                    refine ⟨703778638974990583446709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15013944298133132446863125 703778638974990583446709)
                    ·
                      rfl

theorem cell23_4111812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_4111812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111812 prefixEnd_4111812 := by exact prefixLift 4111812
  have htrace : WordTrace (prefixWord ++ tailWord_4111812) baseStart_4111812 baseEnd_4111812 := by
    simpa [prefixWord, tailWord_4111812, baseEnd_4111812] using wordTrace_append hprefix tailTrace_4111812
  have hstable : (prefixWord ++ tailWord_4111812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111812).length < 2 ^ (prefixWord ++ tailWord_4111812).sum := by decide
  have hdescent : baseEnd_4111812 < baseStart_4111812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111848 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4111848 : Nat := 118140960795 + 4111848 * 2 ^ 59
def prefixEnd_4111848 : Nat := 4983230072969 + 3 ^ 40 * 4111848 * 2
def baseEnd_4111848 : Nat := 2111354402228533609489961

theorem tailTrace_4111848 : CollatzResearch.WordTrace tailWord_4111848 prefixEnd_4111848 2111354402228533609489961 := by
  unfold tailWord_4111848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74985708603742209287356099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99980944804989612383141465 74985708603742209287356099)
  ·
    refine ⟨112478562905613313931034149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74985708603742209287356099 112478562905613313931034149)
    ·
      refine ⟨21089730544802496362068903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112478562905613313931034149 21089730544802496362068903)
      ·
        refine ⟨31634595817203744543103355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21089730544802496362068903 31634595817203744543103355)
        ·
          refine ⟨47451893725805616814655033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31634595817203744543103355 47451893725805616814655033)
          ·
            refine ⟨35588920294354212610991275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47451893725805616814655033 35588920294354212610991275)
            ·
              refine ⟨53383380441531318916486913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35588920294354212610991275 53383380441531318916486913)
              ·
                refine ⟨40037535331148489187365185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53383380441531318916486913 40037535331148489187365185)
                ·
                  refine ⟨30028151498361366890523889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40037535331148489187365185 30028151498361366890523889)
                  ·
                    refine ⟨22521113623771025167892917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30028151498361366890523889 22521113623771025167892917)
                    ·
                      refine ⟨2111354402228533609489961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22521113623771025167892917 2111354402228533609489961)
                      ·
                        rfl

theorem cell23_4111848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4111848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111848 prefixEnd_4111848 := by exact prefixLift 4111848
  have htrace : WordTrace (prefixWord ++ tailWord_4111848) baseStart_4111848 baseEnd_4111848 := by
    simpa [prefixWord, tailWord_4111848, baseEnd_4111848] using wordTrace_append hprefix tailTrace_4111848
  have hstable : (prefixWord ++ tailWord_4111848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111848).length < 2 ^ (prefixWord ++ tailWord_4111848).sum := by decide
  have hdescent : baseEnd_4111848 < baseStart_4111848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111853 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4111853 : Nat := 118140960795 + 4111853 * 2 ^ 59
def prefixEnd_4111853 : Nat := 4983230072969 + 3 ^ 40 * 4111853 * 2
def baseEnd_4111853 : Nat := 2111356969631806089927439

theorem tailTrace_4111853 : CollatzResearch.WordTrace tailWord_4111853 prefixEnd_4111853 2111356969631806089927439 := by
  unfold tailWord_4111853
  simp only [CollatzResearch.WordTrace]
  refine ⟨149971599572466304428644213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99981066381644202952429475 149971599572466304428644213)
  ·
    refine ⟨14059837459918716040185395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149971599572466304428644213 14059837459918716040185395)
    ·
      refine ⟨21089756189878074060278093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14059837459918716040185395 21089756189878074060278093)
      ·
        refine ⟨7908658571204277772604285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21089756189878074060278093 7908658571204277772604285)
        ·
          refine ⟨2965746964201604164726607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7908658571204277772604285 2965746964201604164726607)
          ·
            refine ⟨4448620446302406247089911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965746964201604164726607 4448620446302406247089911)
            ·
              refine ⟨6672930669453609370634867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448620446302406247089911 6672930669453609370634867)
              ·
                refine ⟨10009396004180414055952301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6672930669453609370634867 10009396004180414055952301)
                ·
                  refine ⟨3753523501567655270982113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10009396004180414055952301 3753523501567655270982113)
                  ·
                    refine ⟨2815142626175741453236585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3753523501567655270982113 2815142626175741453236585)
                    ·
                      refine ⟨2111356969631806089927439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815142626175741453236585 2111356969631806089927439)
                      ·
                        rfl

theorem cell23_4111853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4111853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111853 prefixEnd_4111853 := by exact prefixLift 4111853
  have htrace : WordTrace (prefixWord ++ tailWord_4111853) baseStart_4111853 baseEnd_4111853 := by
    simpa [prefixWord, tailWord_4111853, baseEnd_4111853] using wordTrace_append hprefix tailTrace_4111853
  have hstable : (prefixWord ++ tailWord_4111853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111853).length < 2 ^ (prefixWord ++ tailWord_4111853).sum := by decide
  have hdescent : baseEnd_4111853 < baseStart_4111853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111868 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_4111868 : Nat := 118140960795 + 4111868 * 2 ^ 59
def prefixEnd_4111868 : Nat := 4983230072969 + 3 ^ 40 * 4111868 * 2
def baseEnd_4111868 : Nat := 703788223947207843746623

theorem tailTrace_4111868 : CollatzResearch.WordTrace tailWord_4111868 prefixEnd_4111868 703788223947207843746623 := by
  unfold tailWord_4111868
  simp only [CollatzResearch.WordTrace]
  refine ⟨74986073333705980995220129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99981431111607974660293505 74986073333705980995220129)
  ·
    refine ⟨56239555000279485746415097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74986073333705980995220129 56239555000279485746415097)
    ·
      refine ⟨42179666250209614309811323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56239555000279485746415097 42179666250209614309811323)
      ·
        refine ⟨63269499375314421464716985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42179666250209614309811323 63269499375314421464716985)
        ·
          refine ⟨47452124531485816098537739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63269499375314421464716985 47452124531485816098537739)
          ·
            refine ⟨71178186797228724147806609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47452124531485816098537739 71178186797228724147806609)
            ·
              refine ⟨53383640097921543110854957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71178186797228724147806609 53383640097921543110854957)
              ·
                refine ⟨20018865036720578666570609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53383640097921543110854957 20018865036720578666570609)
                ·
                  refine ⟨15014148777540433999927957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20018865036720578666570609 15014148777540433999927957)
                  ·
                    refine ⟨703788223947207843746623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15014148777540433999927957 703788223947207843746623)
                    ·
                      rfl

theorem cell23_4111868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_4111868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111868 prefixEnd_4111868 := by exact prefixLift 4111868
  have htrace : WordTrace (prefixWord ++ tailWord_4111868) baseStart_4111868 baseEnd_4111868 := by
    simpa [prefixWord, tailWord_4111868, baseEnd_4111868] using wordTrace_append hprefix tailTrace_4111868
  have hstable : (prefixWord ++ tailWord_4111868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111868).length < 2 ^ (prefixWord ++ tailWord_4111868).sum := by decide
  have hdescent : baseEnd_4111868 < baseStart_4111868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111869 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_4111869 : Nat := 118140960795 + 4111869 * 2 ^ 59
def prefixEnd_4111869 : Nat := 4983230072969 + 3 ^ 40 * 4111869 * 2
def baseEnd_4111869 : Nat := 2111365185322278027327365

theorem tailTrace_4111869 : CollatzResearch.WordTrace tailWord_4111869 prefixEnd_4111869 2111365185322278027327365 := by
  unfold tailWord_4111869
  simp only [CollatzResearch.WordTrace]
  refine ⟨149972183140408339161226661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99981455426938892774151107 149972183140408339161226661)
  ·
    refine ⟨28119784338826563592729999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149972183140408339161226661 28119784338826563592729999)
    ·
      refine ⟨42179676508239845389094999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28119784338826563592729999 42179676508239845389094999)
      ·
        refine ⟨63269514762359768083642499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42179676508239845389094999 63269514762359768083642499)
        ·
          refine ⟨94904272143539652125463749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63269514762359768083642499 94904272143539652125463749)
          ·
            refine ⟨17794551026913684773524453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94904272143539652125463749 17794551026913684773524453)
            ·
              refine ⟨3336478317546315895035835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17794551026913684773524453 3336478317546315895035835)
              ·
                refine ⟨5004717476319473842553753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3336478317546315895035835 5004717476319473842553753)
                ·
                  refine ⟨3753538107239605381915315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5004717476319473842553753 3753538107239605381915315)
                  ·
                    refine ⟨5630307160859408072872973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3753538107239605381915315 5630307160859408072872973)
                    ·
                      refine ⟨2111365185322278027327365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5630307160859408072872973 2111365185322278027327365)
                      ·
                        rfl

theorem cell23_4111869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_4111869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111869 prefixEnd_4111869 := by exact prefixLift 4111869
  have htrace : WordTrace (prefixWord ++ tailWord_4111869) baseStart_4111869 baseEnd_4111869 := by
    simpa [prefixWord, tailWord_4111869, baseEnd_4111869] using wordTrace_append hprefix tailTrace_4111869
  have hstable : (prefixWord ++ tailWord_4111869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111869).length < 2 ^ (prefixWord ++ tailWord_4111869).sum := by decide
  have hdescent : baseEnd_4111869 < baseStart_4111869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111879 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_4111879 : Nat := 118140960795 + 4111879 * 2 ^ 59
def prefixEnd_4111879 : Nat := 4983230072969 + 3 ^ 40 * 4111879 * 2
def baseEnd_4111879 : Nat := 2111370320128822988202319

theorem tailTrace_4111879 : CollatzResearch.WordTrace tailWord_4111879 prefixEnd_4111879 2111370320128822988202319 := by
  unfold tailWord_4111879
  simp only [CollatzResearch.WordTrace]
  refine ⟨149972547870372110869090691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99981698580248073912727127 149972547870372110869090691)
  ·
    refine ⟨224958821805558166303636037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149972547870372110869090691 224958821805558166303636037)
    ·
      refine ⟨42179779088542156181931757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224958821805558166303636037 42179779088542156181931757)
      ·
        refine ⟨15817417158203308568224409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42179779088542156181931757 15817417158203308568224409)
        ·
          refine ⟨11863062868652481426168307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15817417158203308568224409 11863062868652481426168307)
          ·
            refine ⟨17794594302978722139252461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11863062868652481426168307 17794594302978722139252461)
            ·
              refine ⟨6672972863617020802219673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17794594302978722139252461 6672972863617020802219673)
              ·
                refine ⟨5004729647712765601664755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6672972863617020802219673 5004729647712765601664755)
                ·
                  refine ⟨7507094471569148402497133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004729647712765601664755 7507094471569148402497133)
                  ·
                    refine ⟨2815160426838430650936425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7507094471569148402497133 2815160426838430650936425)
                    ·
                      refine ⟨2111370320128822988202319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815160426838430650936425 2111370320128822988202319)
                      ·
                        rfl

theorem cell23_4111879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_4111879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111879 prefixEnd_4111879 := by exact prefixLift 4111879
  have htrace : WordTrace (prefixWord ++ tailWord_4111879) baseStart_4111879 baseEnd_4111879 := by
    simpa [prefixWord, tailWord_4111879, baseEnd_4111879] using wordTrace_append hprefix tailTrace_4111879
  have hstable : (prefixWord ++ tailWord_4111879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111879).length < 2 ^ (prefixWord ++ tailWord_4111879).sum := by decide
  have hdescent : baseEnd_4111879 < baseStart_4111879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111896 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4111896 : Nat := 118140960795 + 4111896 * 2 ^ 59
def prefixEnd_4111896 : Nat := 4983230072969 + 3 ^ 40 * 4111896 * 2
def baseEnd_4111896 : Nat := 2111379049299949421689741

theorem tailTrace_4111896 : CollatzResearch.WordTrace tailWord_4111896 prefixEnd_4111896 2111379049299949421689741 := by
  unfold tailWord_4111896
  simp only [CollatzResearch.WordTrace]
  refine ⟨74986583955655261386229771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99982111940873681848306361 74986583955655261386229771)
  ·
    refine ⟨112479875933482892079344657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74986583955655261386229771 112479875933482892079344657)
    ·
      refine ⟨84359906950112169059508493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112479875933482892079344657 84359906950112169059508493)
      ·
        refine ⟨31634965106292063397315685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84359906950112169059508493 31634965106292063397315685)
        ·
          refine ⟨5931555957429761886996691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31634965106292063397315685 5931555957429761886996691)
          ·
            refine ⟨8897333936144642830495037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931555957429761886996691 8897333936144642830495037)
            ·
              refine ⟨3336500226054241061435639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8897333936144642830495037 3336500226054241061435639)
              ·
                refine ⟨5004750339081361592153459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3336500226054241061435639 5004750339081361592153459)
                ·
                  refine ⟨7507125508622042388230189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5004750339081361592153459 7507125508622042388230189)
                  ·
                    refine ⟨2815172065733265895586321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7507125508622042388230189 2815172065733265895586321)
                    ·
                      refine ⟨2111379049299949421689741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815172065733265895586321 2111379049299949421689741)
                      ·
                        rfl

theorem cell23_4111896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4111896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111896 prefixEnd_4111896 := by exact prefixLift 4111896
  have htrace : WordTrace (prefixWord ++ tailWord_4111896) baseStart_4111896 baseEnd_4111896 := by
    simpa [prefixWord, tailWord_4111896, baseEnd_4111896] using wordTrace_append hprefix tailTrace_4111896
  have hstable : (prefixWord ++ tailWord_4111896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111896).length < 2 ^ (prefixWord ++ tailWord_4111896).sum := by decide
  have hdescent : baseEnd_4111896 < baseStart_4111896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111925 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_4111925 : Nat := 118140960795 + 4111925 * 2 ^ 59
def prefixEnd_4111925 : Nat := 4983230072969 + 3 ^ 40 * 4111925 * 2
def baseEnd_4111925 : Nat := 2111393940238929808227107

theorem tailTrace_4111925 : CollatzResearch.WordTrace tailWord_4111925 prefixEnd_4111925 2111393940238929808227107 := by
  unfold tailWord_4111925
  simp only [CollatzResearch.WordTrace]
  refine ⟨149974225628205460725265229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99982817085470307150176819 149974225628205460725265229)
  ·
    refine ⟨56240334610577047771974461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149974225628205460725265229 56240334610577047771974461)
    ·
      refine ⟨21090125478966392914490423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56240334610577047771974461 21090125478966392914490423)
      ·
        refine ⟨31635188218449589371735635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21090125478966392914490423 31635188218449589371735635)
        ·
          refine ⟨47452782327674384057603453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31635188218449589371735635 47452782327674384057603453)
          ·
            refine ⟨17794793372877894021601295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47452782327674384057603453 17794793372877894021601295)
            ·
              refine ⟨26692190059316841032401943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17794793372877894021601295 26692190059316841032401943)
              ·
                refine ⟨40038285088975261548602915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26692190059316841032401943 40038285088975261548602915)
                ·
                  refine ⟨60057427633462892322904373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40038285088975261548602915 60057427633462892322904373)
                  ·
                    refine ⟨5630383840637146155272285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60057427633462892322904373 5630383840637146155272285)
                    ·
                      refine ⟨2111393940238929808227107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5630383840637146155272285 2111393940238929808227107)
                      ·
                        rfl

theorem cell23_4111925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_4111925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111925 prefixEnd_4111925 := by exact prefixLift 4111925
  have htrace : WordTrace (prefixWord ++ tailWord_4111925) baseStart_4111925 baseEnd_4111925 := by
    simpa [prefixWord, tailWord_4111925, baseEnd_4111925] using wordTrace_append hprefix tailTrace_4111925
  have hstable : (prefixWord ++ tailWord_4111925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111925).length < 2 ^ (prefixWord ++ tailWord_4111925).sum := by decide
  have hdescent : baseEnd_4111925 < baseStart_4111925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4111926 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_4111926 : Nat := 118140960795 + 4111926 * 2 ^ 59
def prefixEnd_4111926 : Nat := 4983230072969 + 3 ^ 40 * 4111926 * 2
def baseEnd_4111926 : Nat := 2111394453719584304314603

theorem tailTrace_4111926 : CollatzResearch.WordTrace tailWord_4111926 prefixEnd_4111926 2111394453719584304314603 := by
  unfold tailWord_4111926
  simp only [CollatzResearch.WordTrace]
  refine ⟨9373391381325114868503227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99982841400801225264034421 9373391381325114868503227)
  ·
    refine ⟨14060087071987672302754841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9373391381325114868503227 14060087071987672302754841)
    ·
      refine ⟨10545065303990754227066131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14060087071987672302754841 10545065303990754227066131)
      ·
        refine ⟨15817597955986131340599197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10545065303990754227066131 15817597955986131340599197)
        ·
          refine ⟨5931599233494799252724699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15817597955986131340599197 5931599233494799252724699)
          ·
            refine ⟨8897398850242198879087049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931599233494799252724699 8897398850242198879087049)
            ·
              refine ⟨6673049137681649159315287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8897398850242198879087049 6673049137681649159315287)
              ·
                refine ⟨10009573706522473738972931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673049137681649159315287 10009573706522473738972931)
                ·
                  refine ⟨15014360559783710608459397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009573706522473738972931 15014360559783710608459397)
                  ·
                    refine ⟨2815192604959445739086137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15014360559783710608459397 2815192604959445739086137)
                    ·
                      refine ⟨2111394453719584304314603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815192604959445739086137 2111394453719584304314603)
                      ·
                        rfl

theorem cell23_4111926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_4111926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4111926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4111926 prefixEnd_4111926 := by exact prefixLift 4111926
  have htrace : WordTrace (prefixWord ++ tailWord_4111926) baseStart_4111926 baseEnd_4111926 := by
    simpa [prefixWord, tailWord_4111926, baseEnd_4111926] using wordTrace_append hprefix tailTrace_4111926
  have hstable : (prefixWord ++ tailWord_4111926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4111926).length < 2 ^ (prefixWord ++ tailWord_4111926).sum := by decide
  have hdescent : baseEnd_4111926 < baseStart_4111926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4111926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112009 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 1, 4]
def baseStart_4112009 : Nat := 118140960795 + 4112009 * 2 ^ 59
def prefixEnd_4112009 : Nat := 4983230072969 + 3 ^ 40 * 4112009 * 2
def baseEnd_4112009 : Nat := 703812357537969159858907

theorem tailTrace_4112009 : CollatzResearch.WordTrace tailWord_4112009 prefixEnd_4112009 703812357537969159858907 := by
  unfold tailWord_4112009
  simp only [CollatzResearch.WordTrace]
  refine ⟨149977289359901143071323081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99984859573267428714215387 149977289359901143071323081)
  ·
    refine ⟨112482967019925857303492311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149977289359901143071323081 112482967019925857303492311)
    ·
      refine ⟨168724450529888785955238467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112482967019925857303492311 168724450529888785955238467)
      ·
        refine ⟨253086675794833178932857701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168724450529888785955238467 253086675794833178932857701)
        ·
          refine ⟨47453751711531221049910819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253086675794833178932857701 47453751711531221049910819)
          ·
            refine ⟨71180627567296831574866229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47453751711531221049910819 71180627567296831574866229)
            ·
              refine ⟨6673183834434077960143709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71180627567296831574866229 6673183834434077960143709)
              ·
                refine ⟨2502443937912779235053891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6673183834434077960143709 2502443937912779235053891)
                ·
                  refine ⟨3753665906869168852580837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502443937912779235053891 3753665906869168852580837)
                  ·
                    refine ⟨703812357537969159858907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753665906869168852580837 703812357537969159858907)
                    ·
                      rfl

theorem cell23_4112009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 4].length) (baseStart_4112009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112009 prefixEnd_4112009 := by exact prefixLift 4112009
  have htrace : WordTrace (prefixWord ++ tailWord_4112009) baseStart_4112009 baseEnd_4112009 := by
    simpa [prefixWord, tailWord_4112009, baseEnd_4112009] using wordTrace_append hprefix tailTrace_4112009
  have hstable : (prefixWord ++ tailWord_4112009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112009).length < 2 ^ (prefixWord ++ tailWord_4112009).sum := by decide
  have hdescent : baseEnd_4112009 < baseStart_4112009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112035 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 3, 5]
def baseStart_4112035 : Nat := 118140960795 + 4112035 * 2 ^ 59
def prefixEnd_4112035 : Nat := 4983230072969 + 3 ^ 40 * 4112035 * 2
def baseEnd_4112035 : Nat := 703816807703641459283867

theorem tailTrace_4112035 : CollatzResearch.WordTrace tailWord_4112035 prefixEnd_4112035 703816807703641459283867 := by
  unfold tailWord_4112035
  simp only [CollatzResearch.WordTrace]
  refine ⟨149978237657806949511769559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99985491771871299674513039 149978237657806949511769559)
  ·
    refine ⟨224967356486710424267654339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149978237657806949511769559 224967356486710424267654339)
    ·
      refine ⟨337451034730065636401481509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224967356486710424267654339 337451034730065636401481509)
      ·
        refine ⟨63272069011887306825277783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337451034730065636401481509 63272069011887306825277783)
        ·
          refine ⟨94908103517830960237916675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63272069011887306825277783 94908103517830960237916675)
          ·
            refine ⟨142362155276746440356875013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94908103517830960237916675 142362155276746440356875013)
            ·
              refine ⟨26692904114389957566914065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142362155276746440356875013 26692904114389957566914065)
              ·
                refine ⟨20019678085792468175185549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26692904114389957566914065 20019678085792468175185549)
                ·
                  refine ⟨7507379282172175565694581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20019678085792468175185549 7507379282172175565694581)
                  ·
                    refine ⟨703816807703641459283867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7507379282172175565694581 703816807703641459283867)
                    ·
                      rfl

theorem cell23_4112035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 5].length) (baseStart_4112035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112035 prefixEnd_4112035 := by exact prefixLift 4112035
  have htrace : WordTrace (prefixWord ++ tailWord_4112035) baseStart_4112035 baseEnd_4112035 := by
    simpa [prefixWord, tailWord_4112035, baseEnd_4112035] using wordTrace_append hprefix tailTrace_4112035
  have hstable : (prefixWord ++ tailWord_4112035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112035).length < 2 ^ (prefixWord ++ tailWord_4112035).sum := by decide
  have hdescent : baseEnd_4112035 < baseStart_4112035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112099 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 1, 6]
def baseStart_4112099 : Nat := 118140960795 + 4112099 * 2 ^ 59
def prefixEnd_4112099 : Nat := 4983230072969 + 3 ^ 40 * 4112099 * 2
def baseEnd_4112099 : Nat := 703827761957604042483769

theorem tailTrace_4112099 : CollatzResearch.WordTrace tailWord_4112099 prefixEnd_4112099 703827761957604042483769 := by
  unfold tailWord_4112099
  simp only [CollatzResearch.WordTrace]
  refine ⟨149980571929575088442099351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99987047953050058961399567 149980571929575088442099351)
  ·
    refine ⟨224970857894362632663149027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149980571929575088442099351 224970857894362632663149027)
    ·
      refine ⟨337456286841543948994723541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224970857894362632663149027 337456286841543948994723541)
      ·
        refine ⟨7909131722848686304563833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 337456286841543948994723541 7909131722848686304563833)
        ·
          refine ⟨5931848792136514728422875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7909131722848686304563833 5931848792136514728422875)
          ·
            refine ⟨8897773188204772092634313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931848792136514728422875 8897773188204772092634313)
            ·
              refine ⟨6673329891153579069475735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8897773188204772092634313 6673329891153579069475735)
              ·
                refine ⟨10009994836730368604213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673329891153579069475735 10009994836730368604213603)
                ·
                  refine ⟨15014992255095552906320405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10009994836730368604213603 15014992255095552906320405)
                  ·
                    refine ⟨703827761957604042483769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15014992255095552906320405 703827761957604042483769)
                    ·
                      rfl

theorem cell23_4112099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 6].length) (baseStart_4112099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112099 prefixEnd_4112099 := by exact prefixLift 4112099
  have htrace : WordTrace (prefixWord ++ tailWord_4112099) baseStart_4112099 baseEnd_4112099 := by
    simpa [prefixWord, tailWord_4112099, baseEnd_4112099] using wordTrace_append hprefix tailTrace_4112099
  have hstable : (prefixWord ++ tailWord_4112099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112099).length < 2 ^ (prefixWord ++ tailWord_4112099).sum := by decide
  have hdescent : baseEnd_4112099 < baseStart_4112099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112109 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4112109 : Nat := 118140960795 + 4112109 * 2 ^ 59
def prefixEnd_4112109 : Nat := 4983230072969 + 3 ^ 40 * 4112109 * 2
def baseEnd_4112109 : Nat := 2111488420679357088326261

theorem tailTrace_4112109 : CollatzResearch.WordTrace tailWord_4112109 prefixEnd_4112109 2111488420679357088326261 := by
  unfold tailWord_4112109
  simp only [CollatzResearch.WordTrace]
  refine ⟨149980936659538860149963381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99987291106359240099975587 149980936659538860149963381)
  ·
    refine ⟨14060712811831768139059067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149980936659538860149963381 14060712811831768139059067)
    ·
      refine ⟨21091069217747652208588601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14060712811831768139059067 21091069217747652208588601)
      ·
        refine ⟨15818301913310739156441451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21091069217747652208588601 15818301913310739156441451)
        ·
          refine ⟨23727452869966108734662177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15818301913310739156441451 23727452869966108734662177)
          ·
            refine ⟨17795589652474581550996633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23727452869966108734662177 17795589652474581550996633)
            ·
              refine ⟨13346692239355936163247475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17795589652474581550996633 13346692239355936163247475)
              ·
                refine ⟨20020038359033904244871213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13346692239355936163247475 20020038359033904244871213)
                ·
                  refine ⟨7507514384637714091826705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20020038359033904244871213 7507514384637714091826705)
                  ·
                    refine ⟨5630635788478285568870029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7507514384637714091826705 5630635788478285568870029)
                    ·
                      refine ⟨2111488420679357088326261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5630635788478285568870029 2111488420679357088326261)
                      ·
                        rfl

theorem cell23_4112109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4112109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112109 prefixEnd_4112109 := by exact prefixLift 4112109
  have htrace : WordTrace (prefixWord ++ tailWord_4112109) baseStart_4112109 baseEnd_4112109 := by
    simpa [prefixWord, tailWord_4112109, baseEnd_4112109] using wordTrace_append hprefix tailTrace_4112109
  have hstable : (prefixWord ++ tailWord_4112109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112109).length < 2 ^ (prefixWord ++ tailWord_4112109).sum := by decide
  have hdescent : baseEnd_4112109 < baseStart_4112109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112116 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_4112116 : Nat := 118140960795 + 4112116 * 2 ^ 59
def prefixEnd_4112116 : Nat := 4983230072969 + 3 ^ 40 * 4112116 * 2
def baseEnd_4112116 : Nat := 703830671681312853646243

theorem tailTrace_4112116 : CollatzResearch.WordTrace tailWord_4112116 prefixEnd_4112116 703830671681312853646243 := by
  unfold tailWord_4112116
  simp only [CollatzResearch.WordTrace]
  refine ⟨74990595985256750172734101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99987461313675666896978801 74990595985256750172734101)
  ·
    refine ⟨3515184186808910164346911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74990595985256750172734101 3515184186808910164346911)
    ·
      refine ⟨5272776280213365246520367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3515184186808910164346911 5272776280213365246520367)
      ·
        refine ⟨7909164420320047869780551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5272776280213365246520367 7909164420320047869780551)
        ·
          refine ⟨11863746630480071804670827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909164420320047869780551 11863746630480071804670827)
          ·
            refine ⟨17795619945720107707006241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11863746630480071804670827 17795619945720107707006241)
            ·
              refine ⟨13346714959290080780254681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17795619945720107707006241 13346714959290080780254681)
              ·
                refine ⟨10010036219467560585191011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13346714959290080780254681 10010036219467560585191011)
                ·
                  refine ⟨15015054329201340877786517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10010036219467560585191011 15015054329201340877786517)
                  ·
                    refine ⟨703830671681312853646243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15015054329201340877786517 703830671681312853646243)
                    ·
                      rfl

theorem cell23_4112116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_4112116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112116 prefixEnd_4112116 := by exact prefixLift 4112116
  have htrace : WordTrace (prefixWord ++ tailWord_4112116) baseStart_4112116 baseEnd_4112116 := by
    simpa [prefixWord, tailWord_4112116, baseEnd_4112116] using wordTrace_append hprefix tailTrace_4112116
  have hstable : (prefixWord ++ tailWord_4112116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112116).length < 2 ^ (prefixWord ++ tailWord_4112116).sum := by decide
  have hdescent : baseEnd_4112116 < baseStart_4112116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112125 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_4112125 : Nat := 118140960795 + 4112125 * 2 ^ 59
def prefixEnd_4112125 : Nat := 4983230072969 + 3 ^ 40 * 4112125 * 2
def baseEnd_4112125 : Nat := 703832212123276341908729

theorem tailTrace_4112125 : CollatzResearch.WordTrace tailWord_4112125 prefixEnd_4112125 703832212123276341908729 := by
  unfold tailWord_4112125
  simp only [CollatzResearch.WordTrace]
  refine ⟨149981520227480894882545829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99987680151653929921697219 149981520227480894882545829)
  ·
    refine ⟨28121535042652667790477343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149981520227480894882545829 28121535042652667790477343)
    ·
      refine ⟨42182302563979001685716015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28121535042652667790477343 42182302563979001685716015)
      ·
        refine ⟨63273453845968502528574023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42182302563979001685716015 63273453845968502528574023)
        ·
          refine ⟨94910180768952753792861035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63273453845968502528574023 94910180768952753792861035)
          ·
            refine ⟨142365271153429130689291553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94910180768952753792861035 142365271153429130689291553)
            ·
              refine ⟨106773953365071848016968665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142365271153429130689291553 106773953365071848016968665)
              ·
                refine ⟨80080465023803886012726499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106773953365071848016968665 80080465023803886012726499)
                ·
                  refine ⟨120120697535705829019089749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80080465023803886012726499 120120697535705829019089749)
                  ·
                    refine ⟨703832212123276341908729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 120120697535705829019089749 703832212123276341908729)
                    ·
                      rfl

theorem cell23_4112125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_4112125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112125 prefixEnd_4112125 := by exact prefixLift 4112125
  have htrace : WordTrace (prefixWord ++ tailWord_4112125) baseStart_4112125 baseEnd_4112125 := by
    simpa [prefixWord, tailWord_4112125, baseEnd_4112125] using wordTrace_append hprefix tailTrace_4112125
  have hstable : (prefixWord ++ tailWord_4112125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112125).length < 2 ^ (prefixWord ++ tailWord_4112125).sum := by decide
  have hdescent : baseEnd_4112125 < baseStart_4112125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112134 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4112134 : Nat := 118140960795 + 4112134 * 2 ^ 59
def prefixEnd_4112134 : Nat := 4983230072969 + 3 ^ 40 * 4112134 * 2
def baseEnd_4112134 : Nat := 2111501257695719490513647

theorem tailTrace_4112134 : CollatzResearch.WordTrace tailWord_4112134 prefixEnd_4112134 2111501257695719490513647 := by
  unfold tailWord_4112134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686932765139009044363233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99987898989632192946415637 4686932765139009044363233)
  ·
    refine ⟨3515199573854256783272425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4686932765139009044363233 3515199573854256783272425)
    ·
      refine ⟨2636399680390692587454319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3515199573854256783272425 2636399680390692587454319)
      ·
        refine ⟨3954599520586038881181479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636399680390692587454319 3954599520586038881181479)
        ·
          refine ⟨5931899280879058321772219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954599520586038881181479 5931899280879058321772219)
          ·
            refine ⟨8897848921318587482658329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931899280879058321772219 8897848921318587482658329)
            ·
              refine ⟨6673386690988940611993747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8897848921318587482658329 6673386690988940611993747)
              ·
                refine ⟨10010080036483410917990621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673386690988940611993747 10010080036483410917990621)
                ·
                  refine ⟨3753780013681279094246483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10010080036483410917990621 3753780013681279094246483)
                  ·
                    refine ⟨5630670020521918641369725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3753780013681279094246483 5630670020521918641369725)
                    ·
                      refine ⟨2111501257695719490513647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5630670020521918641369725 2111501257695719490513647)
                      ·
                        rfl

theorem cell23_4112134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4112134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112134 prefixEnd_4112134 := by exact prefixLift 4112134
  have htrace : WordTrace (prefixWord ++ tailWord_4112134) baseStart_4112134 baseEnd_4112134 := by
    simpa [prefixWord, tailWord_4112134, baseEnd_4112134] using wordTrace_append hprefix tailTrace_4112134
  have hstable : (prefixWord ++ tailWord_4112134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112134).length < 2 ^ (prefixWord ++ tailWord_4112134).sum := by decide
  have hdescent : baseEnd_4112134 < baseStart_4112134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112174 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4112174 : Nat := 118140960795 + 4112174 * 2 ^ 59
def prefixEnd_4112174 : Nat := 4983230072969 + 3 ^ 40 * 4112174 * 2
def baseEnd_4112174 : Nat := 2111521796921899334013463

theorem tailTrace_4112174 : CollatzResearch.WordTrace tailWord_4112174 prefixEnd_4112174 2111521796921899334013463 := by
  unfold tailWord_4112174
  simp only [CollatzResearch.WordTrace]
  refine ⟨18747913425537922031384947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99988871602868917500719717 18747913425537922031384947)
  ·
    refine ⟨28121870138306883047077421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18747913425537922031384947 28121870138306883047077421)
    ·
      refine ⟨10545701301865081142654033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28121870138306883047077421 10545701301865081142654033)
      ·
        refine ⟨7909275976398810856990525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10545701301865081142654033 7909275976398810856990525)
        ·
          refine ⟨2965978491149554071371447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7909275976398810856990525 2965978491149554071371447)
          ·
            refine ⟨4448967736724331107057171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965978491149554071371447 4448967736724331107057171)
            ·
              refine ⟨6673451605086496660585757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448967736724331107057171 6673451605086496660585757)
              ·
                refine ⟨2502544351907436247719659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6673451605086496660585757 2502544351907436247719659)
                ·
                  refine ⟨3753816527861154371579489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502544351907436247719659 3753816527861154371579489)
                  ·
                    refine ⟨2815362395895865778684617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3753816527861154371579489 2815362395895865778684617)
                    ·
                      refine ⟨2111521796921899334013463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815362395895865778684617 2111521796921899334013463)
                      ·
                        rfl

theorem cell23_4112174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4112174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112174 prefixEnd_4112174 := by exact prefixLift 4112174
  have htrace : WordTrace (prefixWord ++ tailWord_4112174) baseStart_4112174 baseEnd_4112174 := by
    simpa [prefixWord, tailWord_4112174, baseEnd_4112174] using wordTrace_append hprefix tailTrace_4112174
  have hstable : (prefixWord ++ tailWord_4112174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112174).length < 2 ^ (prefixWord ++ tailWord_4112174).sum := by decide
  have hdescent : baseEnd_4112174 < baseStart_4112174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112213 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_4112213 : Nat := 118140960795 + 4112213 * 2 ^ 59
def prefixEnd_4112213 : Nat := 4983230072969 + 3 ^ 40 * 4112213 * 2
def baseEnd_4112213 : Nat := 2111541822667424681425783

theorem tailTrace_4112213 : CollatzResearch.WordTrace tailWord_4112213 prefixEnd_4112213 2111541822667424681425783 := by
  unfold tailWord_4112213
  simp only [CollatzResearch.WordTrace]
  refine ⟨149984729851162085911749293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99989819900774723941166195 149984729851162085911749293)
  ·
    refine ⟨56244273694185782216905985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149984729851162085911749293 56244273694185782216905985)
    ·
      refine ⟨42183205270639336662679489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56244273694185782216905985 42183205270639336662679489)
      ·
        refine ⟨31637403952979502497009617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42183205270639336662679489 31637403952979502497009617)
        ·
          refine ⟨23728052964734626872757213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31637403952979502497009617 23728052964734626872757213)
          ·
            refine ⟨8898019861775485077283955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23728052964734626872757213 8898019861775485077283955)
            ·
              refine ⟨13347029792663227615925933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898019861775485077283955 13347029792663227615925933)
              ·
                refine ⟨5005136172248710355972225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13347029792663227615925933 5005136172248710355972225)
                ·
                  refine ⟨3753852129186532766979169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5005136172248710355972225 3753852129186532766979169)
                  ·
                    refine ⟨2815389096889899575234377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3753852129186532766979169 2815389096889899575234377)
                    ·
                      refine ⟨2111541822667424681425783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815389096889899575234377 2111541822667424681425783)
                      ·
                        rfl

theorem cell23_4112213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_4112213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112213 prefixEnd_4112213 := by exact prefixLift 4112213
  have htrace : WordTrace (prefixWord ++ tailWord_4112213) baseStart_4112213 baseEnd_4112213 := by
    simpa [prefixWord, tailWord_4112213, baseEnd_4112213] using wordTrace_append hprefix tailTrace_4112213
  have hstable : (prefixWord ++ tailWord_4112213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112213).length < 2 ^ (prefixWord ++ tailWord_4112213).sum := by decide
  have hdescent : baseEnd_4112213 < baseStart_4112213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112252 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_4112252 : Nat := 118140960795 + 4112252 * 2 ^ 59
def prefixEnd_4112252 : Nat := 4983230072969 + 3 ^ 40 * 4112252 * 2
def baseEnd_4112252 : Nat := 2111561848412950028838103

theorem tailTrace_4112252 : CollatzResearch.WordTrace tailWord_4112252 prefixEnd_4112252 2111561848412950028838103 := by
  unfold tailWord_4112252
  simp only [CollatzResearch.WordTrace]
  refine ⟨74993076149010397786209505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99990768198680530381612673 74993076149010397786209505)
  ·
    refine ⟨56244807111757798339657129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74993076149010397786209505 56244807111757798339657129)
    ·
      refine ⟨42183605333818348754742847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56244807111757798339657129 42183605333818348754742847)
      ·
        refine ⟨63275408000727523132114271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42183605333818348754742847 63275408000727523132114271)
        ·
          refine ⟨94913112001091284698171407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63275408000727523132114271 94913112001091284698171407)
          ·
            refine ⟨142369668001636927047257111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94913112001091284698171407 142369668001636927047257111)
            ·
              refine ⟨213554502002455390570885667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142369668001636927047257111 213554502002455390570885667)
              ·
                refine ⟨320331753003683085856328501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213554502002455390570885667 320331753003683085856328501)
                ·
                  refine ⟨30031101844095289299030797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320331753003683085856328501 30031101844095289299030797)
                  ·
                    refine ⟨11261663191535733487136549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30031101844095289299030797 11261663191535733487136549)
                    ·
                      refine ⟨2111561848412950028838103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11261663191535733487136549 2111561848412950028838103)
                      ·
                        rfl

theorem cell23_4112252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_4112252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112252 prefixEnd_4112252 := by exact prefixLift 4112252
  have htrace : WordTrace (prefixWord ++ tailWord_4112252) baseStart_4112252 baseEnd_4112252 := by
    simpa [prefixWord, tailWord_4112252, baseEnd_4112252] using wordTrace_append hprefix tailTrace_4112252
  have hstable : (prefixWord ++ tailWord_4112252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112252).length < 2 ^ (prefixWord ++ tailWord_4112252).sum := by decide
  have hdescent : baseEnd_4112252 < baseStart_4112252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112279 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 5, 4]
def baseStart_4112279 : Nat := 118140960795 + 4112279 * 2 ^ 59
def prefixEnd_4112279 : Nat := 4983230072969 + 3 ^ 40 * 4112279 * 2
def baseEnd_4112279 : Nat := 703858570796873807733493

theorem tailTrace_4112279 : CollatzResearch.WordTrace tailWord_4112279 prefixEnd_4112279 703858570796873807733493 := by
  unfold tailWord_4112279
  simp only [CollatzResearch.WordTrace]
  refine ⟨149987137068922979183651891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99991424712615319455767927 149987137068922979183651891)
  ·
    refine ⟨224980705603384468775477837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149987137068922979183651891 224980705603384468775477837)
    ·
      refine ⟨84367764601269175790804189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224980705603384468775477837 84367764601269175790804189)
      ·
        refine ⟨31637911725475940921551571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84367764601269175790804189 31637911725475940921551571)
        ·
          refine ⟨47456867588213911382327357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31637911725475940921551571 47456867588213911382327357)
          ·
            refine ⟨17796325345580216768372759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47456867588213911382327357 17796325345580216768372759)
            ·
              refine ⟨26694488018370325152559139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17796325345580216768372759 26694488018370325152559139)
              ·
                refine ⟨40041732027555487728838709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26694488018370325152559139 40041732027555487728838709)
                ·
                  refine ⟨3753912377583326974578629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40041732027555487728838709 3753912377583326974578629)
                  ·
                    refine ⟨703858570796873807733493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3753912377583326974578629 703858570796873807733493)
                    ·
                      rfl

theorem cell23_4112279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_4112279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112279 prefixEnd_4112279 := by exact prefixLift 4112279
  have htrace : WordTrace (prefixWord ++ tailWord_4112279) baseStart_4112279 baseEnd_4112279 := by
    simpa [prefixWord, tailWord_4112279, baseEnd_4112279] using wordTrace_append hprefix tailTrace_4112279
  have hstable : (prefixWord ++ tailWord_4112279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112279).length < 2 ^ (prefixWord ++ tailWord_4112279).sum := by decide
  have hdescent : baseEnd_4112279 < baseStart_4112279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112309 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 8]
def baseStart_4112309 : Nat := 118140960795 + 4112309 * 2 ^ 59
def prefixEnd_4112309 : Nat := 4983230072969 + 3 ^ 40 * 4112309 * 2
def baseEnd_4112309 : Nat := 234621235201139589536149

theorem tailTrace_4112309 : CollatzResearch.WordTrace tailWord_4112309 prefixEnd_4112309 234621235201139589536149 := by
  unfold tailWord_4112309
  simp only [CollatzResearch.WordTrace]
  refine ⟨149988231258814294307243981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99992154172542862871495987 149988231258814294307243981)
  ·
    refine ⟨56245586722055360365216493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149988231258814294307243981 56245586722055360365216493)
    ·
      refine ⟨21092095020770760136956185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56245586722055360365216493 21092095020770760136956185)
      ·
        refine ⟨15819071265578070102717139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21092095020770760136956185 15819071265578070102717139)
        ·
          refine ⟨23728606898367105154075709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15819071265578070102717139 23728606898367105154075709)
          ·
            refine ⟨8898227586887664432778391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23728606898367105154075709 8898227586887664432778391)
            ·
              refine ⟨13347341380331496649167587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8898227586887664432778391 13347341380331496649167587)
              ·
                refine ⟨20021012070497244973751381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347341380331496649167587 20021012070497244973751381)
                ·
                  refine ⟨234621235201139589536149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20021012070497244973751381 234621235201139589536149)
                  ·
                    rfl

theorem cell23_4112309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_4112309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112309 prefixEnd_4112309 := by exact prefixLift 4112309
  have htrace : WordTrace (prefixWord ++ tailWord_4112309) baseStart_4112309 baseEnd_4112309 := by
    simpa [prefixWord, tailWord_4112309, baseEnd_4112309] using wordTrace_append hprefix tailTrace_4112309
  have hstable : (prefixWord ++ tailWord_4112309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112309).length < 2 ^ (prefixWord ++ tailWord_4112309).sum := by decide
  have hdescent : baseEnd_4112309 < baseStart_4112309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112312 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_4112312 : Nat := 118140960795 + 4112312 * 2 ^ 59
def prefixEnd_4112312 : Nat := 4983230072969 + 3 ^ 40 * 4112312 * 2
def baseEnd_4112312 : Nat := 2111592657252219794087827

theorem tailTrace_4112312 : CollatzResearch.WordTrace tailWord_4112312 prefixEnd_4112312 2111592657252219794087827 := by
  unfold tailWord_4112312
  simp only [CollatzResearch.WordTrace]
  refine ⟨74994170338901712909801595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99992227118535617213068793 74994170338901712909801595)
  ·
    refine ⟨112491255508352569364702393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74994170338901712909801595 112491255508352569364702393)
    ·
      refine ⟨84368441631264427023526795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112491255508352569364702393 84368441631264427023526795)
      ·
        refine ⟨126552662446896640535290193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84368441631264427023526795 126552662446896640535290193)
        ·
          refine ⟨94914496835172480401467645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126552662446896640535290193 94914496835172480401467645)
          ·
            refine ⟨35592936313189680150550367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94914496835172480401467645 35592936313189680150550367)
            ·
              refine ⟨53389404469784520225825551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35592936313189680150550367 53389404469784520225825551)
              ·
                refine ⟨80084106704676780338738327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53389404469784520225825551 80084106704676780338738327)
                ·
                  refine ⟨120126160057015170508107491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80084106704676780338738327 120126160057015170508107491)
                  ·
                    refine ⟨180189240085522755762161237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 120126160057015170508107491 180189240085522755762161237)
                    ·
                      refine ⟨2111592657252219794087827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 180189240085522755762161237 2111592657252219794087827)
                      ·
                        rfl

theorem cell23_4112312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_4112312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112312 prefixEnd_4112312 := by exact prefixLift 4112312
  have htrace : WordTrace (prefixWord ++ tailWord_4112312) baseStart_4112312 baseEnd_4112312 := by
    simpa [prefixWord, tailWord_4112312, baseEnd_4112312] using wordTrace_append hprefix tailTrace_4112312
  have hstable : (prefixWord ++ tailWord_4112312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112312).length < 2 ^ (prefixWord ++ tailWord_4112312).sum := by decide
  have hdescent : baseEnd_4112312 < baseStart_4112312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112336 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 3, 1, 3]
def baseStart_4112336 : Nat := 118140960795 + 4112336 * 2 ^ 59
def prefixEnd_4112336 : Nat := 4983230072969 + 3 ^ 40 * 4112336 * 2
def baseEnd_4112336 : Nat := 2111604980787927700187717

theorem tailTrace_4112336 : CollatzResearch.WordTrace tailWord_4112336 prefixEnd_4112336 2111604980787927700187717 := by
  unfold tailWord_4112336
  simp only [CollatzResearch.WordTrace]
  refine ⟨74994608014858238959238431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99992810686477651945651241 74994608014858238959238431)
  ·
    refine ⟨112491912022287358438857647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74994608014858238959238431 112491912022287358438857647)
    ·
      refine ⟨168737868033431037658286471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112491912022287358438857647 168737868033431037658286471)
      ·
        refine ⟨253106802050146556487429707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168737868033431037658286471 253106802050146556487429707)
        ·
          refine ⟨379660203075219834731144561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253106802050146556487429707 379660203075219834731144561)
          ·
            refine ⟨284745152306414876048358421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379660203075219834731144561 284745152306414876048358421)
            ·
              refine ⟨13347429014363197314766801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284745152306414876048358421 13347429014363197314766801)
              ·
                refine ⟨10010571760772397986075101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13347429014363197314766801 10010571760772397986075101)
                ·
                  refine ⟨3753964410289649244778163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10010571760772397986075101 3753964410289649244778163)
                  ·
                    refine ⟨5630946615434473867167245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3753964410289649244778163 5630946615434473867167245)
                    ·
                      refine ⟨2111604980787927700187717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5630946615434473867167245 2111604980787927700187717)
                      ·
                        rfl

theorem cell23_4112336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_4112336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112336 prefixEnd_4112336 := by exact prefixLift 4112336
  have htrace : WordTrace (prefixWord ++ tailWord_4112336) baseStart_4112336 baseEnd_4112336 := by
    simpa [prefixWord, tailWord_4112336, baseEnd_4112336] using wordTrace_append hprefix tailTrace_4112336
  have hstable : (prefixWord ++ tailWord_4112336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112336).length < 2 ^ (prefixWord ++ tailWord_4112336).sum := by decide
  have hdescent : baseEnd_4112336 < baseStart_4112336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112379 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5]
def baseStart_4112379 : Nat := 118140960795 + 4112379 * 2 ^ 59
def prefixEnd_4112379 : Nat := 4983230072969 + 3 ^ 40 * 4112379 * 2
def baseEnd_4112379 : Nat := 2111627060456071031950019

theorem tailTrace_4112379 : CollatzResearch.WordTrace tailWord_4112379 prefixEnd_4112379 2111627060456071031950019 := by
  unfold tailWord_4112379
  simp only [CollatzResearch.WordTrace]
  refine ⟨149990784368560696262292191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99993856245707130841528127 149990784368560696262292191)
  ·
    refine ⟨224986176552841044393438287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149990784368560696262292191 224986176552841044393438287)
    ·
      refine ⟨337479264829261566590157431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224986176552841044393438287 337479264829261566590157431)
      ·
        refine ⟨506218897243892349885236147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337479264829261566590157431 506218897243892349885236147)
        ·
          refine ⟨759328345865838524827854221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506218897243892349885236147 759328345865838524827854221)
          ·
            refine ⟨284748129699689446810445333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 759328345865838524827854221 284748129699689446810445333)
            ·
              refine ⟨13347568579672942819239625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284748129699689446810445333 13347568579672942819239625)
              ·
                refine ⟨10010676434754707114429719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13347568579672942819239625 10010676434754707114429719)
                ·
                  refine ⟨15016014652132060671644579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10010676434754707114429719 15016014652132060671644579)
                  ·
                    refine ⟨22524021978198091007466869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15016014652132060671644579 22524021978198091007466869)
                    ·
                      refine ⟨2111627060456071031950019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22524021978198091007466869 2111627060456071031950019)
                      ·
                        rfl

theorem cell23_4112379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].length) (baseStart_4112379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112379 prefixEnd_4112379 := by exact prefixLift 4112379
  have htrace : WordTrace (prefixWord ++ tailWord_4112379) baseStart_4112379 baseEnd_4112379 := by
    simpa [prefixWord, tailWord_4112379, baseEnd_4112379] using wordTrace_append hprefix tailTrace_4112379
  have hstable : (prefixWord ++ tailWord_4112379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112379).length < 2 ^ (prefixWord ++ tailWord_4112379).sum := by decide
  have hdescent : baseEnd_4112379 < baseStart_4112379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112389 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_4112389 : Nat := 118140960795 + 4112389 * 2 ^ 59
def prefixEnd_4112389 : Nat := 4983230072969 + 3 ^ 40 * 4112389 * 2
def baseEnd_4112389 : Nat := 2111632195262615992824973

theorem tailTrace_4112389 : CollatzResearch.WordTrace tailWord_4112389 prefixEnd_4112389 2111632195262615992824973 := by
  unfold tailWord_4112389
  simp only [CollatzResearch.WordTrace]
  refine ⟨149991149098524467970156221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99994099399016311980104147 149991149098524467970156221)
  ·
    refine ⟨56246680911946675488808583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149991149098524467970156221 56246680911946675488808583)
    ·
      refine ⟨84370021367920013233212875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56246680911946675488808583 84370021367920013233212875)
      ·
        refine ⟨126555032051880019849819313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84370021367920013233212875 126555032051880019849819313)
        ·
          refine ⟨94916274038910014887364485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126555032051880019849819313 94916274038910014887364485)
          ·
            refine ⟨17796801382295627791380841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94916274038910014887364485 17796801382295627791380841)
            ·
              refine ⟨13347601036721720843535631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17796801382295627791380841 13347601036721720843535631)
              ·
                refine ⟨20021401555082581265303447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347601036721720843535631 20021401555082581265303447)
                ·
                  refine ⟨30032102332623871897955171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20021401555082581265303447 30032102332623871897955171)
                  ·
                    refine ⟨45048153498935807846932757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30032102332623871897955171 45048153498935807846932757)
                    ·
                      refine ⟨2111632195262615992824973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45048153498935807846932757 2111632195262615992824973)
                      ·
                        rfl

theorem cell23_4112389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_4112389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112389 prefixEnd_4112389 := by exact prefixLift 4112389
  have htrace : WordTrace (prefixWord ++ tailWord_4112389) baseStart_4112389 baseEnd_4112389 := by
    simpa [prefixWord, tailWord_4112389, baseEnd_4112389] using wordTrace_append hprefix tailTrace_4112389
  have hstable : (prefixWord ++ tailWord_4112389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112389).length < 2 ^ (prefixWord ++ tailWord_4112389).sum := by decide
  have hdescent : baseEnd_4112389 < baseStart_4112389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112396 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_4112396 : Nat := 118140960795 + 4112396 * 2 ^ 59
def prefixEnd_4112396 : Nat := 4983230072969 + 3 ^ 40 * 4112396 * 2
def baseEnd_4112396 : Nat := 2111635789627197465437441

theorem tailTrace_4112396 : CollatzResearch.WordTrace tailWord_4112396 prefixEnd_4112396 2111635789627197465437441 := by
  unfold tailWord_4112396
  simp only [CollatzResearch.WordTrace]
  refine ⟨74995702204749554082830521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99994269606332738777107361 74995702204749554082830521)
  ·
    refine ⟨56246776653562165562122891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74995702204749554082830521 56246776653562165562122891)
    ·
      refine ⟨84370164980343248343184337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56246776653562165562122891 84370164980343248343184337)
      ·
        refine ⟨63277623735257436257388253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84370164980343248343184337 63277623735257436257388253)
        ·
          refine ⟨23729108900721538596520595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63277623735257436257388253 23729108900721538596520595)
          ·
            refine ⟨35593663351082307894780893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23729108900721538596520595 35593663351082307894780893)
            ·
              refine ⟨13347623756655865460542835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35593663351082307894780893 13347623756655865460542835)
              ·
                refine ⟨20021435634983798190814253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347623756655865460542835 20021435634983798190814253)
                ·
                  refine ⟨7508038363118924321555345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20021435634983798190814253 7508038363118924321555345)
                  ·
                    refine ⟨5631028772339193241166509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508038363118924321555345 5631028772339193241166509)
                    ·
                      refine ⟨2111635789627197465437441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5631028772339193241166509 2111635789627197465437441)
                      ·
                        rfl

theorem cell23_4112396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_4112396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112396 prefixEnd_4112396 := by exact prefixLift 4112396
  have htrace : WordTrace (prefixWord ++ tailWord_4112396) baseStart_4112396 baseEnd_4112396 := by
    simpa [prefixWord, tailWord_4112396, baseEnd_4112396] using wordTrace_append hprefix tailTrace_4112396
  have hstable : (prefixWord ++ tailWord_4112396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112396).length < 2 ^ (prefixWord ++ tailWord_4112396).sum := by decide
  have hdescent : baseEnd_4112396 < baseStart_4112396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112413 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4112413 : Nat := 118140960795 + 4112413 * 2 ^ 59
def prefixEnd_4112413 : Nat := 4983230072969 + 3 ^ 40 * 4112413 * 2
def baseEnd_4112413 : Nat := 2111644518798323898924863

theorem tailTrace_4112413 : CollatzResearch.WordTrace tailWord_4112413 prefixEnd_4112413 2111644518798323898924863 := by
  unfold tailWord_4112413
  simp only [CollatzResearch.WordTrace]
  refine ⟨149992024450437520069029893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99994682966958346712686595 149992024450437520069029893)
  ·
    refine ⟨28123504584457035012943105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149992024450437520069029893 28123504584457035012943105)
    ·
      refine ⟨21092628438342776259707329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28123504584457035012943105 21092628438342776259707329)
      ·
        refine ⟨15819471328757082194780497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21092628438342776259707329 15819471328757082194780497)
        ·
          refine ⟨11864603496567811646085373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15819471328757082194780497 11864603496567811646085373)
          ·
            refine ⟨4449226311212929367282015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11864603496567811646085373 4449226311212929367282015)
            ·
              refine ⟨6673839466819394050923023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449226311212929367282015 6673839466819394050923023)
              ·
                refine ⟨10010759200229091076384535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6673839466819394050923023 10010759200229091076384535)
                ·
                  refine ⟨15016138800343636614576803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10010759200229091076384535 15016138800343636614576803)
                  ·
                    refine ⟨22524208200515454921865205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15016138800343636614576803 22524208200515454921865205)
                    ·
                      refine ⟨2111644518798323898924863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22524208200515454921865205 2111644518798323898924863)
                      ·
                        rfl

theorem cell23_4112413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4112413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112413 prefixEnd_4112413 := by exact prefixLift 4112413
  have htrace : WordTrace (prefixWord ++ tailWord_4112413) baseStart_4112413 baseEnd_4112413 := by
    simpa [prefixWord, tailWord_4112413, baseEnd_4112413] using wordTrace_append hprefix tailTrace_4112413
  have hstable : (prefixWord ++ tailWord_4112413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112413).length < 2 ^ (prefixWord ++ tailWord_4112413).sum := by decide
  have hdescent : baseEnd_4112413 < baseStart_4112413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112420 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_4112420 : Nat := 118140960795 + 4112420 * 2 ^ 59
def prefixEnd_4112420 : Nat := 4983230072969 + 3 ^ 40 * 4112420 * 2
def baseEnd_4112420 : Nat := 703882704387635123845777

theorem tailTrace_4112420 : CollatzResearch.WordTrace tailWord_4112420 prefixEnd_4112420 703882704387635123845777 := by
  unfold tailWord_4112420
  simp only [CollatzResearch.WordTrace]
  refine ⟨74996139880706080132267357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99994853174274773509689809 74996139880706080132267357)
  ·
    refine ⟨28123552455264780049600259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74996139880706080132267357 28123552455264780049600259)
    ·
      refine ⟨42185328682897170074400389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28123552455264780049600259 42185328682897170074400389)
      ·
        refine ⟨7909749128043219388950073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42185328682897170074400389 7909749128043219388950073)
        ·
          refine ⟨5932311846032414541712555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7909749128043219388950073 5932311846032414541712555)
          ·
            refine ⟨8898467769048621812568833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932311846032414541712555 8898467769048621812568833)
            ·
              refine ⟨6673850826786466359426625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8898467769048621812568833 6673850826786466359426625)
              ·
                refine ⟨5005388120089849769569969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6673850826786466359426625 5005388120089849769569969)
                ·
                  refine ⟨3754041090067387327177477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5005388120089849769569969 3754041090067387327177477)
                  ·
                    refine ⟨703882704387635123845777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754041090067387327177477 703882704387635123845777)
                    ·
                      rfl

theorem cell23_4112420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_4112420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112420 prefixEnd_4112420 := by exact prefixLift 4112420
  have htrace : WordTrace (prefixWord ++ tailWord_4112420) baseStart_4112420 baseEnd_4112420 := by
    simpa [prefixWord, tailWord_4112420, baseEnd_4112420] using wordTrace_append hprefix tailTrace_4112420
  have hstable : (prefixWord ++ tailWord_4112420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112420).length < 2 ^ (prefixWord ++ tailWord_4112420).sum := by decide
  have hdescent : baseEnd_4112420 < baseStart_4112420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112453 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 1, 3, 2]
def baseStart_4112453 : Nat := 118140960795 + 4112453 * 2 ^ 59
def prefixEnd_4112453 : Nat := 4983230072969 + 3 ^ 40 * 4112453 * 2
def baseEnd_4112453 : Nat := 2111665058024503742424679

theorem tailTrace_4112453 : CollatzResearch.WordTrace tailWord_4112453 prefixEnd_4112453 2111665058024503742424679 := by
  unfold tailWord_4112453
  simp only [CollatzResearch.WordTrace]
  refine ⟨149993483370292606900486013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99995655580195071266990675 149993483370292606900486013)
  ·
    refine ⟨56247556263859727587682255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149993483370292606900486013 56247556263859727587682255)
    ·
      refine ⟨84371334395789591381523383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56247556263859727587682255 84371334395789591381523383)
      ·
        refine ⟨126557001593684387072285075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84371334395789591381523383 126557001593684387072285075)
        ·
          refine ⟨189835502390526580608427613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126557001593684387072285075 189835502390526580608427613)
          ·
            refine ⟨71188313396447467728160355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189835502390526580608427613 71188313396447467728160355)
            ·
              refine ⟨106782470094671201592240533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71188313396447467728160355 106782470094671201592240533)
              ·
                refine ⟨5005428285687712574636275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106782470094671201592240533 5005428285687712574636275)
                ·
                  refine ⟨7508142428531568861954413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005428285687712574636275 7508142428531568861954413)
                  ·
                    refine ⟨2815553410699338323232905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7508142428531568861954413 2815553410699338323232905)
                    ·
                      refine ⟨2111665058024503742424679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815553410699338323232905 2111665058024503742424679)
                      ·
                        rfl

theorem cell23_4112453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_4112453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112453 prefixEnd_4112453 := by exact prefixLift 4112453
  have htrace : WordTrace (prefixWord ++ tailWord_4112453) baseStart_4112453 baseEnd_4112453 := by
    simpa [prefixWord, tailWord_4112453, baseEnd_4112453] using wordTrace_append hprefix tailTrace_4112453
  have hstable : (prefixWord ++ tailWord_4112453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112453).length < 2 ^ (prefixWord ++ tailWord_4112453).sum := by decide
  have hdescent : baseEnd_4112453 < baseStart_4112453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112476 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_4112476 : Nat := 118140960795 + 4112476 * 2 ^ 59
def prefixEnd_4112476 : Nat := 4983230072969 + 3 ^ 40 * 4112476 * 2
def baseEnd_4112476 : Nat := 703892289359852384145691

theorem tailTrace_4112476 : CollatzResearch.WordTrace tailWord_4112476 prefixEnd_4112476 703892289359852384145691 := by
  unfold tailWord_4112476
  simp only [CollatzResearch.WordTrace]
  refine ⟨74997161124604640914286641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99996214832806187885715521 74997161124604640914286641)
  ·
    refine ⟨56247870843453480685714981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74997161124604640914286641 56247870843453480685714981)
    ·
      refine ⟨10546475783147527628571559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56247870843453480685714981 10546475783147527628571559)
      ·
        refine ⟨15819713674721291442857339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10546475783147527628571559 15819713674721291442857339)
        ·
          refine ⟨23729570512081937164286009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15819713674721291442857339 23729570512081937164286009)
          ·
            refine ⟨17797177884061452873214507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23729570512081937164286009 17797177884061452873214507)
            ·
              refine ⟨26695766826092179309821761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17797177884061452873214507 26695766826092179309821761)
              ·
                refine ⟨20021825119569134482366321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26695766826092179309821761 20021825119569134482366321)
                ·
                  refine ⟨15016368839676850861774741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20021825119569134482366321 15016368839676850861774741)
                  ·
                    refine ⟨703892289359852384145691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15016368839676850861774741 703892289359852384145691)
                    ·
                      rfl

theorem cell23_4112476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_4112476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112476 prefixEnd_4112476 := by exact prefixLift 4112476
  have htrace : WordTrace (prefixWord ++ tailWord_4112476) baseStart_4112476 baseEnd_4112476 := by
    simpa [prefixWord, tailWord_4112476, baseEnd_4112476] using wordTrace_append hprefix tailTrace_4112476
  have hstable : (prefixWord ++ tailWord_4112476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112476).length < 2 ^ (prefixWord ++ tailWord_4112476).sum := by decide
  have hdescent : baseEnd_4112476 < baseStart_4112476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112477 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4112477 : Nat := 118140960795 + 4112477 * 2 ^ 59
def prefixEnd_4112477 : Nat := 4983230072969 + 3 ^ 40 * 4112477 * 2
def baseEnd_4112477 : Nat := 2111677381560211648524569

theorem tailTrace_4112477 : CollatzResearch.WordTrace tailWord_4112477 prefixEnd_4112477 2111677381560211648524569 := by
  unfold tailWord_4112477
  simp only [CollatzResearch.WordTrace]
  refine ⟨149994358722205658999359685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99996239148137105999573123 149994358722205658999359685)
  ·
    refine ⟨28123942260413561062379941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149994358722205658999359685 28123942260413561062379941)
    ·
      refine ⟨5273239173827542699196239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28123942260413561062379941 5273239173827542699196239)
      ·
        refine ⟨7909858760741314048794359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5273239173827542699196239 7909858760741314048794359)
        ·
          refine ⟨11864788141111971073191539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7909858760741314048794359 11864788141111971073191539)
          ·
            refine ⟨17797182211667956609787309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11864788141111971073191539 17797182211667956609787309)
            ·
              refine ⟨6673943329375483728670241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17797182211667956609787309 6673943329375483728670241)
              ·
                refine ⟨5005457497031612796502681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6673943329375483728670241 5005457497031612796502681)
                ·
                  refine ⟨3754093122773709597377011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5005457497031612796502681 3754093122773709597377011)
                  ·
                    refine ⟨5631139684160564396065517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3754093122773709597377011 5631139684160564396065517)
                    ·
                      refine ⟨2111677381560211648524569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5631139684160564396065517 2111677381560211648524569)
                      ·
                        rfl

theorem cell23_4112477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4112477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112477 prefixEnd_4112477 := by exact prefixLift 4112477
  have htrace : WordTrace (prefixWord ++ tailWord_4112477) baseStart_4112477 baseEnd_4112477 := by
    simpa [prefixWord, tailWord_4112477, baseEnd_4112477] using wordTrace_append hprefix tailTrace_4112477
  have hstable : (prefixWord ++ tailWord_4112477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112477).length < 2 ^ (prefixWord ++ tailWord_4112477).sum := by decide
  have hdescent : baseEnd_4112477 < baseStart_4112477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112496 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_4112496 : Nat := 118140960795 + 4112496 * 2 ^ 59
def prefixEnd_4112496 : Nat := 4983230072969 + 3 ^ 40 * 4112496 * 2
def baseEnd_4112496 : Nat := 2111687137692647074186981

theorem tailTrace_4112496 : CollatzResearch.WordTrace tailWord_4112496 prefixEnd_4112496 2111687137692647074186981 := by
  unfold tailWord_4112496
  simp only [CollatzResearch.WordTrace]
  refine ⟨74997525854568412622150671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99996701139424550162867561 74997525854568412622150671)
  ·
    refine ⟨112496288781852618933226007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74997525854568412622150671 112496288781852618933226007)
    ·
      refine ⟨168744433172778928399839011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112496288781852618933226007 168744433172778928399839011)
      ·
        refine ⟨253116649759168392599758517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168744433172778928399839011 253116649759168392599758517)
        ·
          refine ⟨23729685914922036806227361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253116649759168392599758517 23729685914922036806227361)
          ·
            refine ⟨17797264436191527604670521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23729685914922036806227361 17797264436191527604670521)
            ·
              refine ⟨13347948327143645703502891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17797264436191527604670521 13347948327143645703502891)
              ·
                refine ⟨20021922490715468555254337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13347948327143645703502891 20021922490715468555254337)
                ·
                  refine ⟨15016441868036601416440753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20021922490715468555254337 15016441868036601416440753)
                  ·
                    refine ⟨11262331401027451062330565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15016441868036601416440753 11262331401027451062330565)
                    ·
                      refine ⟨2111687137692647074186981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11262331401027451062330565 2111687137692647074186981)
                      ·
                        rfl

theorem cell23_4112496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_4112496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112496 prefixEnd_4112496 := by exact prefixLift 4112496
  have htrace : WordTrace (prefixWord ++ tailWord_4112496) baseStart_4112496 baseEnd_4112496 := by
    simpa [prefixWord, tailWord_4112496, baseEnd_4112496] using wordTrace_append hprefix tailTrace_4112496
  have hstable : (prefixWord ++ tailWord_4112496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112496).length < 2 ^ (prefixWord ++ tailWord_4112496).sum := by decide
  have hdescent : baseEnd_4112496 < baseStart_4112496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112529 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_4112529 : Nat := 118140960795 + 4112529 * 2 ^ 59
def prefixEnd_4112529 : Nat := 4983230072969 + 3 ^ 40 * 4112529 * 2
def baseEnd_4112529 : Nat := 2111704082554245445074329

theorem tailTrace_4112529 : CollatzResearch.WordTrace tailWord_4112529 prefixEnd_4112529 2111704082554245445074329 := by
  unfold tailWord_4112529
  simp only [CollatzResearch.WordTrace]
  refine ⟨149996255318017271880252641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99997503545344847920168427 149996255318017271880252641)
  ·
    refine ⟨112497191488512953910189481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149996255318017271880252641 112497191488512953910189481)
    ·
      refine ⟨84372893616384715432642111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112497191488512953910189481 84372893616384715432642111)
      ·
        refine ⟨126559340424577073148963167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84372893616384715432642111 126559340424577073148963167)
        ·
          refine ⟨189839010636865609723444751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126559340424577073148963167 189839010636865609723444751)
          ·
            refine ⟨284758515955298414585167127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189839010636865609723444751 284758515955298414585167127)
            ·
              refine ⟨427137773932947621877750691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284758515955298414585167127 427137773932947621877750691)
              ·
                refine ⟨640706660899421432816626037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427137773932947621877750691 640706660899421432816626037)
                ·
                  refine ⟨60066249459320759326558691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 640706660899421432816626037 60066249459320759326558691)
                  ·
                    refine ⟨90099374188981138989838037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60066249459320759326558691 90099374188981138989838037)
                    ·
                      refine ⟨2111704082554245445074329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90099374188981138989838037 2111704082554245445074329)
                      ·
                        rfl

theorem cell23_4112529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_4112529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112529 prefixEnd_4112529 := by exact prefixLift 4112529
  have htrace : WordTrace (prefixWord ++ tailWord_4112529) baseStart_4112529 baseEnd_4112529 := by
    simpa [prefixWord, tailWord_4112529, baseEnd_4112529] using wordTrace_append hprefix tailTrace_4112529
  have hstable : (prefixWord ++ tailWord_4112529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112529).length < 2 ^ (prefixWord ++ tailWord_4112529).sum := by decide
  have hdescent : baseEnd_4112529 < baseStart_4112529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112540 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 5]
def baseStart_4112540 : Nat := 118140960795 + 4112540 * 2 ^ 59
def prefixEnd_4112540 : Nat := 4983230072969 + 3 ^ 40 * 4112540 * 2
def baseEnd_4112540 : Nat := 234634414537938322448531

theorem tailTrace_4112540 : CollatzResearch.WordTrace tailWord_4112540 prefixEnd_4112540 234634414537938322448531 := by
  unfold tailWord_4112540
  simp only [CollatzResearch.WordTrace]
  refine ⟨74998328260488710379451537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99997771013984947172602049 74998328260488710379451537)
  ·
    refine ⟨56248746195366532784588653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74998328260488710379451537 56248746195366532784588653)
    ·
      refine ⟨21093279823262449794220745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56248746195366532784588653 21093279823262449794220745)
      ·
        refine ⟨15819959867446837345665559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21093279823262449794220745 15819959867446837345665559)
        ·
          refine ⟨23729939801170256018498339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15819959867446837345665559 23729939801170256018498339)
          ·
            refine ⟨35594909701755384027747509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23729939801170256018498339 35594909701755384027747509)
            ·
              refine ⟨3337022784539567252601329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35594909701755384027747509 3337022784539567252601329)
              ·
                refine ⟨2502767088404675439450997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337022784539567252601329 2502767088404675439450997)
                ·
                  refine ⟨234634414537938322448531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2502767088404675439450997 234634414537938322448531)
                  ·
                    rfl

theorem cell23_4112540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_4112540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112540 prefixEnd_4112540 := by exact prefixLift 4112540
  have htrace : WordTrace (prefixWord ++ tailWord_4112540) baseStart_4112540 baseEnd_4112540 := by
    simpa [prefixWord, tailWord_4112540, baseEnd_4112540] using wordTrace_append hprefix tailTrace_4112540
  have hstable : (prefixWord ++ tailWord_4112540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112540).length < 2 ^ (prefixWord ++ tailWord_4112540).sum := by decide
  have hdescent : baseEnd_4112540 < baseStart_4112540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112551 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_4112551 : Nat := 118140960795 + 4112551 * 2 ^ 59
def prefixEnd_4112551 : Nat := 4983230072969 + 3 ^ 40 * 4112551 * 2
def baseEnd_4112551 : Nat := 2111715379128644358999229

theorem tailTrace_4112551 : CollatzResearch.WordTrace tailWord_4112551 prefixEnd_4112551 2111715379128644358999229 := by
  unfold tailWord_4112551
  simp only [CollatzResearch.WordTrace]
  refine ⟨149997057723937569637553507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99998038482625046425035671 149997057723937569637553507)
  ·
    refine ⟨224995586585906354456330261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149997057723937569637553507 224995586585906354456330261)
    ·
      refine ⟨10546668121214360365140481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224995586585906354456330261 10546668121214360365140481)
      ·
        refine ⟨7910001090910770273855361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10546668121214360365140481 7910001090910770273855361)
        ·
          refine ⟨5932500818183077705391521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7910001090910770273855361 5932500818183077705391521)
          ·
            refine ⟨4449375613637308279043641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5932500818183077705391521 4449375613637308279043641)
            ·
              refine ⟨3337031710227981209282731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4449375613637308279043641 3337031710227981209282731)
              ·
                refine ⟨5005547565341971813924097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337031710227981209282731 5005547565341971813924097)
                ·
                  refine ⟨3754160674006478860443073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5005547565341971813924097 3754160674006478860443073)
                  ·
                    refine ⟨2815620505504859145332305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3754160674006478860443073 2815620505504859145332305)
                    ·
                      refine ⟨2111715379128644358999229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815620505504859145332305 2111715379128644358999229)
                      ·
                        rfl

theorem cell23_4112551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_4112551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112551 prefixEnd_4112551 := by exact prefixLift 4112551
  have htrace : WordTrace (prefixWord ++ tailWord_4112551) baseStart_4112551 baseEnd_4112551 := by
    simpa [prefixWord, tailWord_4112551, baseEnd_4112551] using wordTrace_append hprefix tailTrace_4112551
  have hstable : (prefixWord ++ tailWord_4112551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112551).length < 2 ^ (prefixWord ++ tailWord_4112551).sum := by decide
  have hdescent : baseEnd_4112551 < baseStart_4112551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112573 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_4112573 : Nat := 118140960795 + 4112573 * 2 ^ 59
def prefixEnd_4112573 : Nat := 4983230072969 + 3 ^ 40 * 4112573 * 2
def baseEnd_4112573 : Nat := 2111726675703043272924127

theorem tailTrace_4112573 : CollatzResearch.WordTrace tailWord_4112573 prefixEnd_4112573 2111726675703043272924127 := by
  unfold tailWord_4112573
  simp only [CollatzResearch.WordTrace]
  refine ⟨149997860129857867394854373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99998573419905244929902915 149997860129857867394854373)
  ·
    refine ⟨28124598774348350136535195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149997860129857867394854373 28124598774348350136535195)
    ·
      refine ⟨42186898161522525204802793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28124598774348350136535195 42186898161522525204802793)
      ·
        refine ⟨31640173621141893903602095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42186898161522525204802793 31640173621141893903602095)
        ·
          refine ⟨47460260431712840855403143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31640173621141893903602095 47460260431712840855403143)
          ·
            refine ⟨71190390647569261283104715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47460260431712840855403143 71190390647569261283104715)
            ·
              refine ⟨106785585971353891924657073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71190390647569261283104715 106785585971353891924657073)
              ·
                refine ⟨80089189478515418943492805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106785585971353891924657073 80089189478515418943492805)
                ·
                  refine ⟨15016723027221641051904901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80089189478515418943492805 15016723027221641051904901)
                  ·
                    refine ⟨2815635567604057697232169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15016723027221641051904901 2815635567604057697232169)
                    ·
                      refine ⟨2111726675703043272924127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815635567604057697232169 2111726675703043272924127)
                      ·
                        rfl

theorem cell23_4112573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_4112573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112573 prefixEnd_4112573 := by exact prefixLift 4112573
  have htrace : WordTrace (prefixWord ++ tailWord_4112573) baseStart_4112573 baseEnd_4112573 := by
    simpa [prefixWord, tailWord_4112573, baseEnd_4112573] using wordTrace_append hprefix tailTrace_4112573
  have hstable : (prefixWord ++ tailWord_4112573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112573).length < 2 ^ (prefixWord ++ tailWord_4112573).sum := by decide
  have hdescent : baseEnd_4112573 < baseStart_4112573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112586 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4112586 : Nat := 118140960795 + 4112586 * 2 ^ 59
def prefixEnd_4112586 : Nat := 4983230072969 + 3 ^ 40 * 4112586 * 2
def baseEnd_4112586 : Nat := 2111733350951551722061567

theorem tailTrace_4112586 : CollatzResearch.WordTrace tailWord_4112586 prefixEnd_4112586 2111733350951551722061567 := by
  unfold tailWord_4112586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37499583569702692653769403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99998889519207180410051741 37499583569702692653769403)
  ·
    refine ⟨56249375354554038980654105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37499583569702692653769403 56249375354554038980654105)
    ·
      refine ⟨42187031515915529235490579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56249375354554038980654105 42187031515915529235490579)
      ·
        refine ⟨63280547273873293853235869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42187031515915529235490579 63280547273873293853235869)
        ·
          refine ⟨23730205227702485194963451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63280547273873293853235869 23730205227702485194963451)
          ·
            refine ⟨35595307841553727792445177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730205227702485194963451 35595307841553727792445177)
            ·
              refine ⟨26696480881165295844333883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35595307841553727792445177 26696480881165295844333883)
              ·
                refine ⟨40044721321747943766500825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26696480881165295844333883 40044721321747943766500825)
                ·
                  refine ⟨30033540991310957824875619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40044721321747943766500825 30033540991310957824875619)
                  ·
                    refine ⟨45050311486966436737313429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30033540991310957824875619 45050311486966436737313429)
                    ·
                      refine ⟨2111733350951551722061567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45050311486966436737313429 2111733350951551722061567)
                      ·
                        rfl

theorem cell23_4112586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4112586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112586 prefixEnd_4112586 := by exact prefixLift 4112586
  have htrace : WordTrace (prefixWord ++ tailWord_4112586) baseStart_4112586 baseEnd_4112586 := by
    simpa [prefixWord, tailWord_4112586, baseEnd_4112586] using wordTrace_append hprefix tailTrace_4112586
  have hstable : (prefixWord ++ tailWord_4112586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112586).length < 2 ^ (prefixWord ++ tailWord_4112586).sum := by decide
  have hdescent : baseEnd_4112586 < baseStart_4112586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112593 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_4112593 : Nat := 118140960795 + 4112593 * 2 ^ 59
def prefixEnd_4112593 : Nat := 4983230072969 + 3 ^ 40 * 4112593 * 2
def baseEnd_4112593 : Nat := 2111736945316133194674035

theorem tailTrace_4112593 : CollatzResearch.WordTrace tailWord_4112593 prefixEnd_4112593 2111736945316133194674035 := by
  unfold tailWord_4112593
  simp only [CollatzResearch.WordTrace]
  refine ⟨149998589589785410810582433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99999059726523607207054955 149998589589785410810582433)
  ·
    refine ⟨112498942192339058107936825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149998589589785410810582433 112498942192339058107936825)
    ·
      refine ⟨84374206644254293580952619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112498942192339058107936825 84374206644254293580952619)
      ·
        refine ⟨126561309966381440371428929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84374206644254293580952619 126561309966381440371428929)
        ·
          refine ⟨94920982474786080278571697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126561309966381440371428929 94920982474786080278571697)
          ·
            refine ⟨71190736856089560208928773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94920982474786080278571697 71190736856089560208928773)
            ·
              refine ⟨13348263160516792539174145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71190736856089560208928773 13348263160516792539174145)
              ·
                refine ⟨10011197370387594404380609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13348263160516792539174145 10011197370387594404380609)
                ·
                  refine ⟨7508398027790695803285457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10011197370387594404380609 7508398027790695803285457)
                  ·
                    refine ⟨5631298520843021852464093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508398027790695803285457 5631298520843021852464093)
                    ·
                      refine ⟨2111736945316133194674035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5631298520843021852464093 2111736945316133194674035)
                      ·
                        rfl

theorem cell23_4112593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_4112593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112593 prefixEnd_4112593 := by exact prefixLift 4112593
  have htrace : WordTrace (prefixWord ++ tailWord_4112593) baseStart_4112593 baseEnd_4112593 := by
    simpa [prefixWord, tailWord_4112593, baseEnd_4112593] using wordTrace_append hprefix tailTrace_4112593
  have hstable : (prefixWord ++ tailWord_4112593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112593).length < 2 ^ (prefixWord ++ tailWord_4112593).sum := by decide
  have hdescent : baseEnd_4112593 < baseStart_4112593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112613 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 6]
def baseStart_4112613 : Nat := 118140960795 + 4112613 * 2 ^ 59
def prefixEnd_4112613 : Nat := 4983230072969 + 3 ^ 40 * 4112613 * 2
def baseEnd_4112613 : Nat := 234638579436580346269327

theorem tailTrace_4112613 : CollatzResearch.WordTrace tailWord_4112613 prefixEnd_4112613 234638579436580346269327 := by
  unfold tailWord_4112613
  simp only [CollatzResearch.WordTrace]
  refine ⟨149999319049712954226310493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99999546033141969484206995 149999319049712954226310493)
  ·
    refine ⟨56249744643642357834866435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149999319049712954226310493 56249744643642357834866435)
    ·
      refine ⟨84374616965463536752299653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56249744643642357834866435 84374616965463536752299653)
      ·
        refine ⟨15820240681024413141056185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84374616965463536752299653 15820240681024413141056185)
        ·
          refine ⟨11865180510768309855792139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15820240681024413141056185 11865180510768309855792139)
          ·
            refine ⟨17797770766152464783688209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865180510768309855792139 17797770766152464783688209)
            ·
              refine ⟨13348328074614348587766157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17797770766152464783688209 13348328074614348587766157)
              ·
                refine ⟨5005623027980380720412309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13348328074614348587766157 5005623027980380720412309)
                ·
                  refine ⟨234638579436580346269327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5005623027980380720412309 234638579436580346269327)
                  ·
                    rfl

theorem cell23_4112613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_4112613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112613 prefixEnd_4112613 := by exact prefixLift 4112613
  have htrace : WordTrace (prefixWord ++ tailWord_4112613) baseStart_4112613 baseEnd_4112613 := by
    simpa [prefixWord, tailWord_4112613, baseEnd_4112613] using wordTrace_append hprefix tailTrace_4112613
  have hstable : (prefixWord ++ tailWord_4112613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112613).length < 2 ^ (prefixWord ++ tailWord_4112613).sum := by decide
  have hdescent : baseEnd_4112613 < baseStart_4112613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112643 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 1, 5]
def baseStart_4112643 : Nat := 118140960795 + 4112643 * 2 ^ 59
def prefixEnd_4112643 : Nat := 4983230072969 + 3 ^ 40 * 4112643 * 2
def baseEnd_4112643 : Nat := 703920873116285999682935

theorem tailTrace_4112643 : CollatzResearch.WordTrace tailWord_4112643 prefixEnd_4112643 703920873116285999682935 := by
  unfold tailWord_4112643
  simp only [CollatzResearch.WordTrace]
  refine ⟨150000413239604269349902583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100000275493069512899935055 150000413239604269349902583)
  ·
    refine ⟨225000619859406404024853875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150000413239604269349902583 225000619859406404024853875)
    ·
      refine ⟨337500929789109606037280813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225000619859406404024853875 337500929789109606037280813)
      ·
        refine ⟨126562848670916102263980305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337500929789109606037280813 126562848670916102263980305)
        ·
          refine ⟨94922136503187076697985229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126562848670916102263980305 94922136503187076697985229)
          ·
            refine ⟨35595801188695153761744461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94922136503187076697985229 35595801188695153761744461)
            ·
              refine ⟨13348425445760682660654173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35595801188695153761744461 13348425445760682660654173)
              ·
                refine ⟨5005659542160255997745315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13348425445760682660654173 5005659542160255997745315)
                ·
                  refine ⟨7508489313240383996617973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005659542160255997745315 7508489313240383996617973)
                  ·
                    refine ⟨703920873116285999682935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7508489313240383996617973 703920873116285999682935)
                    ·
                      rfl

theorem cell23_4112643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 5].length) (baseStart_4112643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112643 prefixEnd_4112643 := by exact prefixLift 4112643
  have htrace : WordTrace (prefixWord ++ tailWord_4112643) baseStart_4112643 baseEnd_4112643 := by
    simpa [prefixWord, tailWord_4112643, baseEnd_4112643] using wordTrace_append hprefix tailTrace_4112643
  have hstable : (prefixWord ++ tailWord_4112643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112643).length < 2 ^ (prefixWord ++ tailWord_4112643).sum := by decide
  have hdescent : baseEnd_4112643 < baseStart_4112643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112647 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 6]
def baseStart_4112647 : Nat := 118140960795 + 4112647 * 2 ^ 59
def prefixEnd_4112647 : Nat := 4983230072969 + 3 ^ 40 * 4112647 * 2
def baseEnd_4112647 : Nat := 234640519252386220377643

theorem tailTrace_4112647 : CollatzResearch.WordTrace tailWord_4112647 prefixEnd_4112647 234640519252386220377643 := by
  unfold tailWord_4112647
  simp only [CollatzResearch.WordTrace]
  refine ⟨150000559131589778033048195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100000372754393185355365463 150000559131589778033048195)
  ·
    refine ⟨225000838697384667049572293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150000559131589778033048195 225000838697384667049572293)
    ·
      refine ⟨42187657255759625071794805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225000838697384667049572293 42187657255759625071794805)
      ·
        refine ⟨3955092867727464850480763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42187657255759625071794805 3955092867727464850480763)
        ·
          refine ⟨5932639301591197275721145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955092867727464850480763 5932639301591197275721145)
          ·
            refine ⟨4449479476193397956790859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5932639301591197275721145 4449479476193397956790859)
            ·
              refine ⟨6674219214290096935186289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4449479476193397956790859 6674219214290096935186289)
              ·
                refine ⟨5005664410717572701389717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6674219214290096935186289 5005664410717572701389717)
                ·
                  refine ⟨234640519252386220377643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5005664410717572701389717 234640519252386220377643)
                  ·
                    rfl

theorem cell23_4112647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 6].length) (baseStart_4112647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112647 prefixEnd_4112647 := by exact prefixLift 4112647
  have htrace : WordTrace (prefixWord ++ tailWord_4112647) baseStart_4112647 baseEnd_4112647 := by
    simpa [prefixWord, tailWord_4112647, baseEnd_4112647] using wordTrace_append hprefix tailTrace_4112647
  have hstable : (prefixWord ++ tailWord_4112647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112647).length < 2 ^ (prefixWord ++ tailWord_4112647).sum := by decide
  have hdescent : baseEnd_4112647 < baseStart_4112647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112650 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_4112650 : Nat := 118140960795 + 4112650 * 2 ^ 59
def prefixEnd_4112650 : Nat := 4983230072969 + 3 ^ 40 * 4112650 * 2
def baseEnd_4112650 : Nat := 2111766213713439471661273

theorem tailTrace_4112650 : CollatzResearch.WordTrace tailWord_4112650 prefixEnd_4112650 2111766213713439471661273 := by
  unfold tailWord_4112650
  simp only [CollatzResearch.WordTrace]
  refine ⟨37500167137644727386351851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100000445700385939696938269 37500167137644727386351851)
  ·
    refine ⟨56250250706467091079527777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37500167137644727386351851 56250250706467091079527777)
    ·
      refine ⟨42187688029850318309645833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56250250706467091079527777 42187688029850318309645833)
      ·
        refine ⟨31640766022387738732234375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42187688029850318309645833 31640766022387738732234375)
        ·
          refine ⟨47461149033581608098351563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31640766022387738732234375 47461149033581608098351563)
          ·
            refine ⟨71191723550372412147527345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47461149033581608098351563 71191723550372412147527345)
            ·
              refine ⟨53393792662779309110645509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71191723550372412147527345 53393792662779309110645509)
              ·
                refine ⟨10011336124271120458246033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53393792662779309110645509 10011336124271120458246033)
                ·
                  refine ⟨7508502093203340343684525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10011336124271120458246033 7508502093203340343684525)
                  ·
                    refine ⟨2815688284951252628881697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7508502093203340343684525 2815688284951252628881697)
                    ·
                      refine ⟨2111766213713439471661273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815688284951252628881697 2111766213713439471661273)
                      ·
                        rfl

theorem cell23_4112650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_4112650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112650 prefixEnd_4112650 := by exact prefixLift 4112650
  have htrace : WordTrace (prefixWord ++ tailWord_4112650) baseStart_4112650 baseEnd_4112650 := by
    simpa [prefixWord, tailWord_4112650, baseEnd_4112650] using wordTrace_append hprefix tailTrace_4112650
  have hstable : (prefixWord ++ tailWord_4112650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112650).length < 2 ^ (prefixWord ++ tailWord_4112650).sum := by decide
  have hdescent : baseEnd_4112650 < baseStart_4112650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112657 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 1, 1, 3]
def baseStart_4112657 : Nat := 118140960795 + 4112657 * 2 ^ 59
def prefixEnd_4112657 : Nat := 4983230072969 + 3 ^ 40 * 4112657 * 2
def baseEnd_4112657 : Nat := 2111769808078020944273741

theorem tailTrace_4112657 : CollatzResearch.WordTrace tailWord_4112657 prefixEnd_4112657 2111769808078020944273741 := by
  unfold tailWord_4112657
  simp only [CollatzResearch.WordTrace]
  refine ⟨150000923861553549740912225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100000615907702366493941483 150000923861553549740912225)
  ·
    refine ⟨112500692896165162305684169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150000923861553549740912225 112500692896165162305684169)
    ·
      refine ⟨84375519672123871729263127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112500692896165162305684169 84375519672123871729263127)
      ·
        refine ⟨126563279508185807593894691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84375519672123871729263127 126563279508185807593894691)
        ·
          refine ⟨189844919262278711390842037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126563279508185807593894691 189844919262278711390842037)
          ·
            refine ⟨17797961180838629192891441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189844919262278711390842037 17797961180838629192891441)
            ·
              refine ⟨13348470885628971894668581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17797961180838629192891441 13348470885628971894668581)
              ·
                refine ⟨2502838291055432230250359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13348470885628971894668581 2502838291055432230250359)
                ·
                  refine ⟨3754257436583148345375539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502838291055432230250359 3754257436583148345375539)
                  ·
                    refine ⟨5631386154874722518063309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3754257436583148345375539 5631386154874722518063309)
                    ·
                      refine ⟨2111769808078020944273741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5631386154874722518063309 2111769808078020944273741)
                      ·
                        rfl

theorem cell23_4112657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_4112657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112657 prefixEnd_4112657 := by exact prefixLift 4112657
  have htrace : WordTrace (prefixWord ++ tailWord_4112657) baseStart_4112657 baseEnd_4112657 := by
    simpa [prefixWord, tailWord_4112657, baseEnd_4112657] using wordTrace_append hprefix tailTrace_4112657
  have hstable : (prefixWord ++ tailWord_4112657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112657).length < 2 ^ (prefixWord ++ tailWord_4112657).sum := by decide
  have hdescent : baseEnd_4112657 < baseStart_4112657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112673 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 1, 6]
def baseStart_4112673 : Nat := 118140960795 + 4112673 * 2 ^ 59
def prefixEnd_4112673 : Nat := 4983230072969 + 3 ^ 40 * 4112673 * 2
def baseEnd_4112673 : Nat := 703926007922830960557889

theorem tailTrace_4112673 : CollatzResearch.WordTrace tailWord_4112673 prefixEnd_4112673 703926007922830960557889 := by
  unfold tailWord_4112673
  simp only [CollatzResearch.WordTrace]
  refine ⟨150001507429495584473494673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100001004952997056315663115 150001507429495584473494673)
  ·
    refine ⟨112501130572121688355121005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150001507429495584473494673 112501130572121688355121005)
    ·
      refine ⟨42187923964545633133170377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112501130572121688355121005 42187923964545633133170377)
      ·
        refine ⟨31640942973409224849877783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42187923964545633133170377 31640942973409224849877783)
        ·
          refine ⟨47461414460113837274816675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31640942973409224849877783 47461414460113837274816675)
          ·
            refine ⟨71192121690170755912225013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47461414460113837274816675 71192121690170755912225013)
            ·
              refine ⟨6674261408453508366771095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71192121690170755912225013 6674261408453508366771095)
              ·
                refine ⟨10011392112680262550156643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6674261408453508366771095 10011392112680262550156643)
                ·
                  refine ⟨15017088169020393825234965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10011392112680262550156643 15017088169020393825234965)
                  ·
                    refine ⟨703926007922830960557889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15017088169020393825234965 703926007922830960557889)
                    ·
                      rfl

theorem cell23_4112673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_4112673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112673 prefixEnd_4112673 := by exact prefixLift 4112673
  have htrace : WordTrace (prefixWord ++ tailWord_4112673) baseStart_4112673 baseEnd_4112673 := by
    simpa [prefixWord, tailWord_4112673, baseEnd_4112673] using wordTrace_append hprefix tailTrace_4112673
  have hstable : (prefixWord ++ tailWord_4112673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112673).length < 2 ^ (prefixWord ++ tailWord_4112673).sum := by decide
  have hdescent : baseEnd_4112673 < baseStart_4112673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112693 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4112693 : Nat := 118140960795 + 4112693 * 2 ^ 59
def prefixEnd_4112693 : Nat := 4983230072969 + 3 ^ 40 * 4112693 * 2
def baseEnd_4112693 : Nat := 2111788293381582803423575

theorem tailTrace_4112693 : CollatzResearch.WordTrace tailWord_4112693 prefixEnd_4112693 2111788293381582803423575 := by
  unfold tailWord_4112693
  simp only [CollatzResearch.WordTrace]
  refine ⟨150002236889423127889222733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100001491259615418592815155 150002236889423127889222733)
  ·
    refine ⟨56250838833533672958458525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150002236889423127889222733 56250838833533672958458525)
    ·
      refine ⟨21094064562575127359421947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56250838833533672958458525 21094064562575127359421947)
      ·
        refine ⟨31641096843862691039132921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21094064562575127359421947 31641096843862691039132921)
        ·
          refine ⟨23730822632897018279349691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31641096843862691039132921 23730822632897018279349691)
          ·
            refine ⟨35596233949345527419024537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730822632897018279349691 35596233949345527419024537)
            ·
              refine ⟨26697175462009145564268403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35596233949345527419024537 26697175462009145564268403)
              ·
                refine ⟨40045763193013718346402605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26697175462009145564268403 40045763193013718346402605)
                ·
                  refine ⟨15017161197380144379900977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40045763193013718346402605 15017161197380144379900977)
                  ·
                    refine ⟨11262870898035108284925733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15017161197380144379900977 11262870898035108284925733)
                    ·
                      refine ⟨2111788293381582803423575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11262870898035108284925733 2111788293381582803423575)
                      ·
                        rfl

theorem cell23_4112693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4112693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112693 prefixEnd_4112693 := by exact prefixLift 4112693
  have htrace : WordTrace (prefixWord ++ tailWord_4112693) baseStart_4112693 baseEnd_4112693 := by
    simpa [prefixWord, tailWord_4112693, baseEnd_4112693] using wordTrace_append hprefix tailTrace_4112693
  have hstable : (prefixWord ++ tailWord_4112693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112693).length < 2 ^ (prefixWord ++ tailWord_4112693).sum := by decide
  have hdescent : baseEnd_4112693 < baseStart_4112693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112700 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_4112700 : Nat := 118140960795 + 4112700 * 2 ^ 59
def prefixEnd_4112700 : Nat := 4983230072969 + 3 ^ 40 * 4112700 * 2
def baseEnd_4112700 : Nat := 2111791887746164276036043

theorem tailTrace_4112700 : CollatzResearch.WordTrace tailWord_4112700 prefixEnd_4112700 2111791887746164276036043 := by
  unfold tailWord_4112700
  simp only [CollatzResearch.WordTrace]
  refine ⟨75001246100198884042363777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100001661466931845389818369 75001246100198884042363777)
  ·
    refine ⟨56250934575149163031772833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75001246100198884042363777 56250934575149163031772833)
    ·
      refine ⟨42188200931361872273829625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56250934575149163031772833 42188200931361872273829625)
      ·
        refine ⟨31641150698521404205372219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42188200931361872273829625 31641150698521404205372219)
        ·
          refine ⟨47461726047782106308058329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31641150698521404205372219 47461726047782106308058329)
          ·
            refine ⟨35596294535836579731043747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47461726047782106308058329 35596294535836579731043747)
            ·
              refine ⟨53394441803754869596565621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35596294535836579731043747 53394441803754869596565621)
              ·
                refine ⟨5005728919102019024678027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53394441803754869596565621 5005728919102019024678027)
                ·
                  refine ⟨7508593378653028537017041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005728919102019024678027 7508593378653028537017041)
                  ·
                    refine ⟨5631445033989771402762781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7508593378653028537017041 5631445033989771402762781)
                    ·
                      refine ⟨2111791887746164276036043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5631445033989771402762781 2111791887746164276036043)
                      ·
                        rfl

theorem cell23_4112700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_4112700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112700 prefixEnd_4112700 := by exact prefixLift 4112700
  have htrace : WordTrace (prefixWord ++ tailWord_4112700) baseStart_4112700 baseEnd_4112700 := by
    simpa [prefixWord, tailWord_4112700, baseEnd_4112700] using wordTrace_append hprefix tailTrace_4112700
  have hstable : (prefixWord ++ tailWord_4112700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112700).length < 2 ^ (prefixWord ++ tailWord_4112700).sum := by decide
  have hdescent : baseEnd_4112700 < baseStart_4112700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112708 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_4112708 : Nat := 118140960795 + 4112708 * 2 ^ 59
def prefixEnd_4112708 : Nat := 4983230072969 + 3 ^ 40 * 4112708 * 2
def baseEnd_4112708 : Nat := 2111795995591400244736007

theorem tailTrace_4112708 : CollatzResearch.WordTrace tailWord_4112708 prefixEnd_4112708 2111795995591400244736007 := by
  unfold tailWord_4112708
  simp only [CollatzResearch.WordTrace]
  refine ⟨75001391992184392725509389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100001855989579190300679185 75001391992184392725509389)
  ·
    refine ⟨28125521997069147272066021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75001391992184392725509389 28125521997069147272066021)
    ·
      refine ⟨5273535374450465113512379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28125521997069147272066021 5273535374450465113512379)
      ·
        refine ⟨7910303061675697670268569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5273535374450465113512379 7910303061675697670268569)
        ·
          refine ⟨5932727296256773252701427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7910303061675697670268569 5932727296256773252701427)
          ·
            refine ⟨8899090944385159879052141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5932727296256773252701427 8899090944385159879052141)
            ·
              refine ⟨3337159104144434954644553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8899090944385159879052141 3337159104144434954644553)
              ·
                refine ⟨2502869328108326215983415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337159104144434954644553 2502869328108326215983415)
                ·
                  refine ⟨3754303992162489323975123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2502869328108326215983415 3754303992162489323975123)
                  ·
                    refine ⟨5631455988243733985962685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3754303992162489323975123 5631455988243733985962685)
                    ·
                      refine ⟨2111795995591400244736007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5631455988243733985962685 2111795995591400244736007)
                      ·
                        rfl

theorem cell23_4112708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_4112708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112708 prefixEnd_4112708 := by exact prefixLift 4112708
  have htrace : WordTrace (prefixWord ++ tailWord_4112708) baseStart_4112708 baseEnd_4112708 := by
    simpa [prefixWord, tailWord_4112708, baseEnd_4112708] using wordTrace_append hprefix tailTrace_4112708
  have hstable : (prefixWord ++ tailWord_4112708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112708).length < 2 ^ (prefixWord ++ tailWord_4112708).sum := by decide
  have hdescent : baseEnd_4112708 < baseStart_4112708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112724 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_4112724 : Nat := 118140960795 + 4112724 * 2 ^ 59
def prefixEnd_4112724 : Nat := 4983230072969 + 3 ^ 40 * 4112724 * 2
def baseEnd_4112724 : Nat := 703934737093957394045311

theorem tailTrace_4112724 : CollatzResearch.WordTrace tailWord_4112724 prefixEnd_4112724 703934737093957394045311 := by
  unfold tailWord_4112724
  simp only [CollatzResearch.WordTrace]
  refine ⟨75001683776155410091800613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100002245034873880122400817 75001683776155410091800613)
  ·
    refine ⟨14062815708029139392212615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75001683776155410091800613 14062815708029139392212615)
    ·
      refine ⟨21094223562043709088318923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14062815708029139392212615 21094223562043709088318923)
      ·
        refine ⟨31641335343065563632478385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21094223562043709088318923 31641335343065563632478385)
        ·
          refine ⟨23731001507299172724358789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31641335343065563632478385 23731001507299172724358789)
          ·
            refine ⟨4449562782618594885817273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23731001507299172724358789 4449562782618594885817273)
            ·
              refine ⟨3337172086963946164362955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4449562782618594885817273 3337172086963946164362955)
              ·
                refine ⟨5005758130445919246544433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337172086963946164362955 5005758130445919246544433)
                ·
                  refine ⟨3754318597834439434908325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5005758130445919246544433 3754318597834439434908325)
                  ·
                    refine ⟨703934737093957394045311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754318597834439434908325 703934737093957394045311)
                    ·
                      rfl

theorem cell23_4112724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_4112724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112724 prefixEnd_4112724 := by exact prefixLift 4112724
  have htrace : WordTrace (prefixWord ++ tailWord_4112724) baseStart_4112724 baseEnd_4112724 := by
    simpa [prefixWord, tailWord_4112724, baseEnd_4112724] using wordTrace_append hprefix tailTrace_4112724
  have hstable : (prefixWord ++ tailWord_4112724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112724).length < 2 ^ (prefixWord ++ tailWord_4112724).sum := by decide
  have hdescent : baseEnd_4112724 < baseStart_4112724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112793 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 7]
def baseStart_4112793 : Nat := 118140960795 + 4112793 * 2 ^ 59
def prefixEnd_4112793 : Nat := 4983230072969 + 3 ^ 40 * 4112793 * 2
def baseEnd_4112793 : Nat := 234648849049670268019235

theorem tailTrace_4112793 : CollatzResearch.WordTrace tailWord_4112793 prefixEnd_4112793 234648849049670268019235 := by
  unfold tailWord_4112793
  simp only [CollatzResearch.WordTrace]
  refine ⟨150005884189060844967863033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100003922792707229978575355 150005884189060844967863033)
  ·
    refine ⟨112504413141795633725897275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150005884189060844967863033 112504413141795633725897275)
    ·
      refine ⟨168756619712693450588845913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112504413141795633725897275 168756619712693450588845913)
      ·
        refine ⟨126567464784520087941634435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168756619712693450588845913 126567464784520087941634435)
        ·
          refine ⟨189851197176780131912451653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126567464784520087941634435 189851197176780131912451653)
          ·
            refine ⟨35597099470646274733584685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189851197176780131912451653 35597099470646274733584685)
            ·
              refine ⟨13348912301492353025094257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35597099470646274733584685 13348912301492353025094257)
              ·
                refine ⟨10011684226119264768820693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13348912301492353025094257 10011684226119264768820693)
                ·
                  refine ⟨234648849049670268019235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10011684226119264768820693 234648849049670268019235)
                  ·
                    rfl

theorem cell23_4112793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 7].length) (baseStart_4112793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112793 prefixEnd_4112793 := by exact prefixLift 4112793
  have htrace : WordTrace (prefixWord ++ tailWord_4112793) baseStart_4112793 baseEnd_4112793 := by
    simpa [prefixWord, tailWord_4112793, baseEnd_4112793] using wordTrace_append hprefix tailTrace_4112793
  have hstable : (prefixWord ++ tailWord_4112793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112793).length < 2 ^ (prefixWord ++ tailWord_4112793).sum := by decide
  have hdescent : baseEnd_4112793 < baseStart_4112793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112808 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4112808 : Nat := 118140960795 + 4112808 * 2 ^ 59
def prefixEnd_4112808 : Nat := 4983230072969 + 3 ^ 40 * 4112808 * 2
def baseEnd_4112808 : Nat := 2111847343656849853485547

theorem tailTrace_4112808 : CollatzResearch.WordTrace tailWord_4112808 prefixEnd_4112808 2111847343656849853485547 := by
  unfold tailWord_4112808
  simp only [CollatzResearch.WordTrace]
  refine ⟨75003215642003251264829539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100004287522671001686439385 75003215642003251264829539)
  ·
    refine ⟨112504823463004876897244309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75003215642003251264829539 112504823463004876897244309)
    ·
      refine ⟨5273663599828353604558327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112504823463004876897244309 5273663599828353604558327)
      ·
        refine ⟨7910495399742530406837491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5273663599828353604558327 7910495399742530406837491)
        ·
          refine ⟨11865743099613795610256237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910495399742530406837491 11865743099613795610256237)
          ·
            refine ⟨4449653662355173353846089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11865743099613795610256237 4449653662355173353846089)
            ·
              refine ⟨3337240246766380015384567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4449653662355173353846089 3337240246766380015384567)
              ·
                refine ⟨5005860370149570023076851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337240246766380015384567 5005860370149570023076851)
                ·
                  refine ⟨7508790555224355034615277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5005860370149570023076851 7508790555224355034615277)
                  ·
                    refine ⟨2815796458209133137980729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7508790555224355034615277 2815796458209133137980729)
                    ·
                      refine ⟨2111847343656849853485547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815796458209133137980729 2111847343656849853485547)
                      ·
                        rfl

theorem cell23_4112808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4112808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112808 prefixEnd_4112808 := by exact prefixLift 4112808
  have htrace : WordTrace (prefixWord ++ tailWord_4112808) baseStart_4112808 baseEnd_4112808 := by
    simpa [prefixWord, tailWord_4112808, baseEnd_4112808] using wordTrace_append hprefix tailTrace_4112808
  have hstable : (prefixWord ++ tailWord_4112808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112808).length < 2 ^ (prefixWord ++ tailWord_4112808).sum := by decide
  have hdescent : baseEnd_4112808 < baseStart_4112808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112873 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_4112873 : Nat := 118140960795 + 4112873 * 2 ^ 59
def prefixEnd_4112873 : Nat := 4983230072969 + 3 ^ 40 * 4112873 * 2
def baseEnd_4112873 : Nat := 2111880719899392099172747

theorem tailTrace_4112873 : CollatzResearch.WordTrace tailWord_4112873 prefixEnd_4112873 2111880719899392099172747 := by
  unfold tailWord_4112873
  simp only [CollatzResearch.WordTrace]
  refine ⟨150008802028771018630775273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100005868019180679087183515 150008802028771018630775273)
  ·
    refine ⟨112506601521578263973081455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150008802028771018630775273 112506601521578263973081455)
    ·
      refine ⟨168759902282367395959622183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112506601521578263973081455 168759902282367395959622183)
      ·
        refine ⟨253139853423551093939433275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168759902282367395959622183 253139853423551093939433275)
        ·
          refine ⟨379709780135326640909149913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253139853423551093939433275 379709780135326640909149913)
          ·
            refine ⟨284782335101494980681862435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379709780135326640909149913 284782335101494980681862435)
            ·
              refine ⟨427173502652242471022793653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284782335101494980681862435 427173502652242471022793653)
              ·
                refine ⟨40047515873647731658386905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 427173502652242471022793653 40047515873647731658386905)
                ·
                  refine ⟨30035636905235798743790179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40047515873647731658386905 30035636905235798743790179)
                  ·
                    refine ⟨45053455357853698115685269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30035636905235798743790179 45053455357853698115685269)
                    ·
                      refine ⟨2111880719899392099172747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45053455357853698115685269 2111880719899392099172747)
                      ·
                        rfl

theorem cell23_4112873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_4112873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112873 prefixEnd_4112873 := by exact prefixLift 4112873
  have htrace : WordTrace (prefixWord ++ tailWord_4112873) baseStart_4112873 baseEnd_4112873 := by
    simpa [prefixWord, tailWord_4112873, baseEnd_4112873] using wordTrace_append hprefix tailTrace_4112873
  have hstable : (prefixWord ++ tailWord_4112873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112873).length < 2 ^ (prefixWord ++ tailWord_4112873).sum := by decide
  have hdescent : baseEnd_4112873 < baseStart_4112873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112877 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4112877 : Nat := 118140960795 + 4112877 * 2 ^ 59
def prefixEnd_4112877 : Nat := 4983230072969 + 3 ^ 40 * 4112877 * 2
def baseEnd_4112877 : Nat := 2111882773822010083522729

theorem tailTrace_4112877 : CollatzResearch.WordTrace tailWord_4112877 prefixEnd_4112877 2111882773822010083522729 := by
  unfold tailWord_4112877
  simp only [CollatzResearch.WordTrace]
  refine ⟨150008947920756527313920885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100005965280504351542613923 150008947920756527313920885)
  ·
    refine ⟨14063338867570924435680083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 150008947920756527313920885 14063338867570924435680083)
    ·
      refine ⟨21095008301356386653520125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14063338867570924435680083 21095008301356386653520125)
      ·
        refine ⟨7910628113008644995070047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21095008301356386653520125 7910628113008644995070047)
        ·
          refine ⟨11865942169512967492605071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910628113008644995070047 11865942169512967492605071)
          ·
            refine ⟨17798913254269451238907607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11865942169512967492605071 17798913254269451238907607)
            ·
              refine ⟨26698369881404176858361411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17798913254269451238907607 26698369881404176858361411)
              ·
                refine ⟨40047554822106265287542117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26698369881404176858361411 40047554822106265287542117)
                ·
                  refine ⟨7508916529144924741414147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40047554822106265287542117 7508916529144924741414147)
                  ·
                    refine ⟨11263374793717387112121221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7508916529144924741414147 11263374793717387112121221)
                    ·
                      refine ⟨2111882773822010083522729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11263374793717387112121221 2111882773822010083522729)
                      ·
                        rfl

theorem cell23_4112877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4112877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112877 prefixEnd_4112877 := by exact prefixLift 4112877
  have htrace : WordTrace (prefixWord ++ tailWord_4112877) baseStart_4112877 baseEnd_4112877 := by
    simpa [prefixWord, tailWord_4112877, baseEnd_4112877] using wordTrace_append hprefix tailTrace_4112877
  have hstable : (prefixWord ++ tailWord_4112877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112877).length < 2 ^ (prefixWord ++ tailWord_4112877).sum := by decide
  have hdescent : baseEnd_4112877 < baseStart_4112877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112883 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 8]
def baseStart_4112883 : Nat := 118140960795 + 4112883 * 2 ^ 59
def prefixEnd_4112883 : Nat := 4983230072969 + 3 ^ 40 * 4112883 * 2
def baseEnd_4112883 : Nat := 234653983856215228894189

theorem tailTrace_4112883 : CollatzResearch.WordTrace tailWord_4112883 prefixEnd_4112883 234653983856215228894189 := by
  unfold tailWord_4112883
  simp only [CollatzResearch.WordTrace]
  refine ⟨150009166758734790338639303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100006111172489860225759535 150009166758734790338639303)
  ·
    refine ⟨225013750138102185507958955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150009166758734790338639303 225013750138102185507958955)
    ·
      refine ⟨337520625207153278261938433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225013750138102185507958955 337520625207153278261938433)
      ·
        refine ⟨253140468905364958696453825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337520625207153278261938433 253140468905364958696453825)
        ·
          refine ⟨189855351679023719022340369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253140468905364958696453825 189855351679023719022340369)
          ·
            refine ⟨142391513759267789266755277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189855351679023719022340369 142391513759267789266755277)
            ·
              refine ⟨53396817659725420975033229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142391513759267789266755277 53396817659725420975033229)
              ·
                refine ⟨20023806622397032865637461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53396817659725420975033229 20023806622397032865637461)
                ·
                  refine ⟨234653983856215228894189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20023806622397032865637461 234653983856215228894189)
                  ·
                    rfl

theorem cell23_4112883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 8].length) (baseStart_4112883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112883 prefixEnd_4112883 := by exact prefixLift 4112883
  have htrace : WordTrace (prefixWord ++ tailWord_4112883) baseStart_4112883 baseEnd_4112883 := by
    simpa [prefixWord, tailWord_4112883, baseEnd_4112883] using wordTrace_append hprefix tailTrace_4112883
  have hstable : (prefixWord ++ tailWord_4112883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112883).length < 2 ^ (prefixWord ++ tailWord_4112883).sum := by decide
  have hdescent : baseEnd_4112883 < baseStart_4112883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112923 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_4112923 : Nat := 118140960795 + 4112923 * 2 ^ 59
def prefixEnd_4112923 : Nat := 4983230072969 + 3 ^ 40 * 4112923 * 2
def baseEnd_4112923 : Nat := 2111906393932116903547517

theorem tailTrace_4112923 : CollatzResearch.WordTrace tailWord_4112923 prefixEnd_4112923 2111906393932116903547517 := by
  unfold tailWord_4112923
  simp only [CollatzResearch.WordTrace]
  refine ⟨150010625678589877170095423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100007083785726584780063615 150010625678589877170095423)
  ·
    refine ⟨225015938517884815755143135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150010625678589877170095423 225015938517884815755143135)
    ·
      refine ⟨337523907776827223632714703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225015938517884815755143135 337523907776827223632714703)
      ·
        refine ⟨506285861665240835449072055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337523907776827223632714703 506285861665240835449072055)
        ·
          refine ⟨759428792497861253173608083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506285861665240835449072055 759428792497861253173608083)
          ·
            refine ⟨1139143188746791879760412125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759428792497861253173608083 1139143188746791879760412125)
            ·
              refine ⟨427178695780046954910154547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1139143188746791879760412125 427178695780046954910154547)
              ·
                refine ⟨640768043670070432365231821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427178695780046954910154547 640768043670070432365231821)
                ·
                  refine ⟨240288016376276412136961933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 640768043670070432365231821 240288016376276412136961933)
                  ·
                    refine ⟨90108006141103654551360725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 240288016376276412136961933 90108006141103654551360725)
                    ·
                      refine ⟨2111906393932116903547517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90108006141103654551360725 2111906393932116903547517)
                      ·
                        rfl

theorem cell23_4112923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_4112923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112923 prefixEnd_4112923 := by exact prefixLift 4112923
  have htrace : WordTrace (prefixWord ++ tailWord_4112923) baseStart_4112923 baseEnd_4112923 := by
    simpa [prefixWord, tailWord_4112923, baseEnd_4112923] using wordTrace_append hprefix tailTrace_4112923
  have hstable : (prefixWord ++ tailWord_4112923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112923).length < 2 ^ (prefixWord ++ tailWord_4112923).sum := by decide
  have hdescent : baseEnd_4112923 < baseStart_4112923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112938 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4112938 : Nat := 118140960795 + 4112938 * 2 ^ 59
def prefixEnd_4112938 : Nat := 4983230072969 + 3 ^ 40 * 4112938 * 2
def baseEnd_4112938 : Nat := 703971365380644781619983

theorem tailTrace_4112938 : CollatzResearch.WordTrace tailWord_4112938 prefixEnd_4112938 703971365380644781619983 := by
  unfold tailWord_4112938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37502793193383883682972867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100007448515690356487927645 37502793193383883682972867)
  ·
    refine ⟨56254189790075825524459301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37502793193383883682972867 56254189790075825524459301)
    ·
      refine ⟨10547660585639217285836119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56254189790075825524459301 10547660585639217285836119)
      ·
        refine ⟨15821490878458825928754179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547660585639217285836119 15821490878458825928754179)
        ·
          refine ⟨23732236317688238893131269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821490878458825928754179 23732236317688238893131269)
          ·
            refine ⟨4449794309566544792462113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23732236317688238893131269 4449794309566544792462113)
            ·
              refine ⟨3337345732174908594346585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4449794309566544792462113 3337345732174908594346585)
              ·
                refine ⟨2503009299131181445759939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337345732174908594346585 2503009299131181445759939)
                ·
                  refine ⟨3754513948696772168639909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503009299131181445759939 3754513948696772168639909)
                  ·
                    refine ⟨703971365380644781619983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754513948696772168639909 703971365380644781619983)
                    ·
                      rfl

theorem cell23_4112938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4112938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112938 prefixEnd_4112938 := by exact prefixLift 4112938
  have htrace : WordTrace (prefixWord ++ tailWord_4112938) baseStart_4112938 baseEnd_4112938 := by
    simpa [prefixWord, tailWord_4112938, baseEnd_4112938] using wordTrace_append hprefix tailTrace_4112938
  have hstable : (prefixWord ++ tailWord_4112938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112938).length < 2 ^ (prefixWord ++ tailWord_4112938).sum := by decide
  have hdescent : baseEnd_4112938 < baseStart_4112938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112960 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 1, 6]
def baseStart_4112960 : Nat := 118140960795 + 4112960 * 2 ^ 59
def prefixEnd_4112960 : Nat := 4983230072969 + 3 ^ 40 * 4112960 * 2
def baseEnd_4112960 : Nat := 703975130905444419594949

theorem tailTrace_4112960 : CollatzResearch.WordTrace tailWord_4112960 prefixEnd_4112960 703975130905444419594949 := by
  unfold tailWord_4112960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75005987589727916244596167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100007983452970554992794889 75005987589727916244596167)
  ·
    refine ⟨112508981384591874366894251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75005987589727916244596167 112508981384591874366894251)
    ·
      refine ⟨168763472076887811550341377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112508981384591874366894251 168763472076887811550341377)
      ·
        refine ⟨126572604057665858662756033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168763472076887811550341377 126572604057665858662756033)
        ·
          refine ⟨94929453043249393997067025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126572604057665858662756033 94929453043249393997067025)
          ·
            refine ⟨71197089782437045497800269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94929453043249393997067025 71197089782437045497800269)
            ·
              refine ⟨26698908668413892061675101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71197089782437045497800269 26698908668413892061675101)
              ·
                refine ⟨10012090750655209523128163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26698908668413892061675101 10012090750655209523128163)
                ·
                  refine ⟨15018136125982814284692245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10012090750655209523128163 15018136125982814284692245)
                  ·
                    refine ⟨703975130905444419594949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15018136125982814284692245 703975130905444419594949)
                    ·
                      rfl

theorem cell23_4112960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_4112960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112960 prefixEnd_4112960 := by exact prefixLift 4112960
  have htrace : WordTrace (prefixWord ++ tailWord_4112960) baseStart_4112960 baseEnd_4112960 := by
    simpa [prefixWord, tailWord_4112960, baseEnd_4112960] using wordTrace_append hprefix tailTrace_4112960
  have hstable : (prefixWord ++ tailWord_4112960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112960).length < 2 ^ (prefixWord ++ tailWord_4112960).sum := by decide
  have hdescent : baseEnd_4112960 < baseStart_4112960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112967 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_4112967 : Nat := 118140960795 + 4112967 * 2 ^ 59
def prefixEnd_4112967 : Nat := 4983230072969 + 3 ^ 40 * 4112967 * 2
def baseEnd_4112967 : Nat := 2111928987080914731397315

theorem tailTrace_4112967 : CollatzResearch.WordTrace tailWord_4112967 prefixEnd_4112967 2111928987080914731397315 := by
  unfold tailWord_4112967
  simp only [CollatzResearch.WordTrace]
  refine ⟨150012230490430472684697155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100008153660286981789798103 150012230490430472684697155)
  ·
    refine ⟨225018345735645709027045733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150012230490430472684697155 225018345735645709027045733)
    ·
      refine ⟨42190939825433570442571075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225018345735645709027045733 42190939825433570442571075)
      ·
        refine ⟨63286409738150355663856613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42190939825433570442571075 63286409738150355663856613)
        ·
          refine ⟨11866201825903191686973115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63286409738150355663856613 11866201825903191686973115)
          ·
            refine ⟨17799302738854787530459673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866201825903191686973115 17799302738854787530459673)
            ·
              refine ⟨13349477054141090647844755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17799302738854787530459673 13349477054141090647844755)
              ·
                refine ⟨20024215581211635971767133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349477054141090647844755 20024215581211635971767133)
                ·
                  refine ⟨7509080842954363489412675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20024215581211635971767133 7509080842954363489412675)
                  ·
                    refine ⟨11263621264431545234119013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509080842954363489412675 11263621264431545234119013)
                    ·
                      refine ⟨2111928987080914731397315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11263621264431545234119013 2111928987080914731397315)
                      ·
                        rfl

theorem cell23_4112967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_4112967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112967 prefixEnd_4112967 := by exact prefixLift 4112967
  have htrace : WordTrace (prefixWord ++ tailWord_4112967) baseStart_4112967 baseEnd_4112967 := by
    simpa [prefixWord, tailWord_4112967, baseEnd_4112967] using wordTrace_append hprefix tailTrace_4112967
  have hstable : (prefixWord ++ tailWord_4112967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112967).length < 2 ^ (prefixWord ++ tailWord_4112967).sum := by decide
  have hdescent : baseEnd_4112967 < baseStart_4112967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4112984 : List Nat := [2, 1, 2, 2, 1, 2, 6, 1, 1, 1, 4]
def baseStart_4112984 : Nat := 118140960795 + 4112984 * 2 ^ 59
def prefixEnd_4112984 : Nat := 4983230072969 + 3 ^ 40 * 4112984 * 2
def baseEnd_4112984 : Nat := 2111937716252041164884737

theorem tailTrace_4112984 : CollatzResearch.WordTrace tailWord_4112984 prefixEnd_4112984 2111937716252041164884737 := by
  unfold tailWord_4112984
  simp only [CollatzResearch.WordTrace]
  refine ⟨75006425265684442294033003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100008567020912589725377337 75006425265684442294033003)
  ·
    refine ⟨112509637898526663441049505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75006425265684442294033003 112509637898526663441049505)
    ·
      refine ⟨84382228423894997580787129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112509637898526663441049505 84382228423894997580787129)
      ·
        refine ⟨63286671317921248185590347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84382228423894997580787129 63286671317921248185590347)
        ·
          refine ⟨94930006976881872278385521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63286671317921248185590347 94930006976881872278385521)
          ·
            refine ⟨71197505232661404208789141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94930006976881872278385521 71197505232661404208789141)
            ·
              refine ⟨3337383057781003322286991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71197505232661404208789141 3337383057781003322286991)
              ·
                refine ⟨5006074586671504983430487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337383057781003322286991 5006074586671504983430487)
                ·
                  refine ⟨7509111880007257475145731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006074586671504983430487 7509111880007257475145731)
                  ·
                    refine ⟨11263667820010886212718597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509111880007257475145731 11263667820010886212718597)
                    ·
                      refine ⟨2111937716252041164884737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11263667820010886212718597 2111937716252041164884737)
                      ·
                        rfl

theorem cell23_4112984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_4112984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4112984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4112984 prefixEnd_4112984 := by exact prefixLift 4112984
  have htrace : WordTrace (prefixWord ++ tailWord_4112984) baseStart_4112984 baseEnd_4112984 := by
    simpa [prefixWord, tailWord_4112984, baseEnd_4112984] using wordTrace_append hprefix tailTrace_4112984
  have hstable : (prefixWord ++ tailWord_4112984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4112984).length < 2 ^ (prefixWord ++ tailWord_4112984).sum := by decide
  have hdescent : baseEnd_4112984 < baseStart_4112984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4112984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113014 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4113014 : Nat := 118140960795 + 4113014 * 2 ^ 59
def prefixEnd_4113014 : Nat := 4983230072969 + 3 ^ 40 * 4113014 * 2
def baseEnd_4113014 : Nat := 2111953120671676047509599

theorem tailTrace_4113014 : CollatzResearch.WordTrace tailWord_4113014 prefixEnd_4113014 2111953120671676047509599 := by
  unfold tailWord_4113014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9375871545078762481978631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100009296480840133141105397 9375871545078762481978631)
  ·
    refine ⟨14063807317618143722967947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9375871545078762481978631 14063807317618143722967947)
    ·
      refine ⟨21095710976427215584451921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14063807317618143722967947 21095710976427215584451921)
      ·
        refine ⟨15821783232320411688338941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21095710976427215584451921 15821783232320411688338941)
        ·
          refine ⟨5933168712120154383127103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15821783232320411688338941 5933168712120154383127103)
          ·
            refine ⟨8899753068180231574690655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933168712120154383127103 8899753068180231574690655)
            ·
              refine ⟨13349629602270347362035983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899753068180231574690655 13349629602270347362035983)
              ·
                refine ⟨20024444403405521043053975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349629602270347362035983 20024444403405521043053975)
                ·
                  refine ⟨30036666605108281564580963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20024444403405521043053975 30036666605108281564580963)
                  ·
                    refine ⟨45054999907662422346871445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30036666605108281564580963 45054999907662422346871445)
                    ·
                      refine ⟨2111953120671676047509599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45054999907662422346871445 2111953120671676047509599)
                      ·
                        rfl

theorem cell23_4113014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4113014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113014 prefixEnd_4113014 := by exact prefixLift 4113014
  have htrace : WordTrace (prefixWord ++ tailWord_4113014) baseStart_4113014 baseEnd_4113014 := by
    simpa [prefixWord, tailWord_4113014, baseEnd_4113014] using wordTrace_append hprefix tailTrace_4113014
  have hstable : (prefixWord ++ tailWord_4113014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113014).length < 2 ^ (prefixWord ++ tailWord_4113014).sum := by decide
  have hdescent : baseEnd_4113014 < baseStart_4113014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113020 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_4113020 : Nat := 118140960795 + 4113020 * 2 ^ 59
def prefixEnd_4113020 : Nat := 4983230072969 + 3 ^ 40 * 4113020 * 2
def baseEnd_4113020 : Nat := 703985400518534341344857

theorem tailTrace_4113020 : CollatzResearch.WordTrace tailWord_4113020 prefixEnd_4113020 703985400518534341344857 := by
  unfold tailWord_4113020
  simp only [CollatzResearch.WordTrace]
  refine ⟨75007081779619231368188257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100009442372825641824251009 75007081779619231368188257)
  ·
    refine ⟨56255311334714423526141193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75007081779619231368188257 56255311334714423526141193)
    ·
      refine ⟨42191483501035817644605895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56255311334714423526141193 42191483501035817644605895)
      ·
        refine ⟨63287225251553726466908843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42191483501035817644605895 63287225251553726466908843)
        ·
          refine ⟨94930837877330589700363265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63287225251553726466908843 94930837877330589700363265)
          ·
            refine ⟨71198128407997942275272449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94930837877330589700363265 71198128407997942275272449)
            ·
              refine ⟨53398596305998456706454337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71198128407997942275272449 53398596305998456706454337)
              ·
                refine ⟨40048947229498842529840753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53398596305998456706454337 40048947229498842529840753)
                ·
                  refine ⟨30036710422124131897380565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40048947229498842529840753 30036710422124131897380565)
                  ·
                    refine ⟨703985400518534341344857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30036710422124131897380565 703985400518534341344857)
                    ·
                      rfl

theorem cell23_4113020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_4113020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113020 prefixEnd_4113020 := by exact prefixLift 4113020
  have htrace : WordTrace (prefixWord ++ tailWord_4113020) baseStart_4113020 baseEnd_4113020 := by
    simpa [prefixWord, tailWord_4113020, baseEnd_4113020] using wordTrace_append hprefix tailTrace_4113020
  have hstable : (prefixWord ++ tailWord_4113020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113020).length < 2 ^ (prefixWord ++ tailWord_4113020).sum := by decide
  have hdescent : baseEnd_4113020 < baseStart_4113020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113021 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_4113021 : Nat := 118140960795 + 4113021 * 2 ^ 59
def prefixEnd_4113021 : Nat := 4983230072969 + 3 ^ 40 * 4113021 * 2
def baseEnd_4113021 : Nat := 2111956715036257520122067

theorem tailTrace_4113021 : CollatzResearch.WordTrace tailWord_4113021 prefixEnd_4113021 2111956715036257520122067 := by
  unfold tailWord_4113021
  simp only [CollatzResearch.WordTrace]
  refine ⟨150014200032234839907162917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100009466688156559938108611 150014200032234839907162917)
  ·
    refine ⟨28127662506044032482593047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 150014200032234839907162917 28127662506044032482593047)
    ·
      refine ⟨42191493759066048723889571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28127662506044032482593047 42191493759066048723889571)
      ·
        refine ⟨63287240638599073085834357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42191493759066048723889571 63287240638599073085834357)
        ·
          refine ⟨5933178809868663101796971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63287240638599073085834357 5933178809868663101796971)
          ·
            refine ⟨8899768214802994652695457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933178809868663101796971 8899768214802994652695457)
            ·
              refine ⟨6674826161102245989521593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8899768214802994652695457 6674826161102245989521593)
              ·
                refine ⟨5006119620826684492141195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6674826161102245989521593 5006119620826684492141195)
                ·
                  refine ⟨7509179431240026738211793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006119620826684492141195 7509179431240026738211793)
                  ·
                    refine ⟨5631884573430020053658845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7509179431240026738211793 5631884573430020053658845)
                    ·
                      refine ⟨2111956715036257520122067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5631884573430020053658845 2111956715036257520122067)
                      ·
                        rfl

theorem cell23_4113021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_4113021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113021 prefixEnd_4113021 := by exact prefixLift 4113021
  have htrace : WordTrace (prefixWord ++ tailWord_4113021) baseStart_4113021 baseEnd_4113021 := by
    simpa [prefixWord, tailWord_4113021, baseEnd_4113021] using wordTrace_append hprefix tailTrace_4113021
  have hstable : (prefixWord ++ tailWord_4113021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113021).length < 2 ^ (prefixWord ++ tailWord_4113021).sum := by decide
  have hdescent : baseEnd_4113021 < baseStart_4113021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113040 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_4113040 : Nat := 118140960795 + 4113040 * 2 ^ 59
def prefixEnd_4113040 : Nat := 4983230072969 + 3 ^ 40 * 4113040 * 2
def baseEnd_4113040 : Nat := 2111966471168692945784479

theorem tailTrace_4113040 : CollatzResearch.WordTrace tailWord_4113040 prefixEnd_4113040 2111966471168692945784479 := by
  unfold tailWord_4113040
  simp only [CollatzResearch.WordTrace]
  refine ⟨75007446509583003076052287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100009928679444004101403049 75007446509583003076052287)
  ·
    refine ⟨112511169764374504614078431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75007446509583003076052287 112511169764374504614078431)
    ·
      refine ⟨168766754646561756921117647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112511169764374504614078431 168766754646561756921117647)
      ·
        refine ⟨253150131969842635381676471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168766754646561756921117647 253150131969842635381676471)
        ·
          refine ⟨379725197954763953072514707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253150131969842635381676471 379725197954763953072514707)
          ·
            refine ⟨569587796932145929608772061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379725197954763953072514707 569587796932145929608772061)
            ·
              refine ⟨213595423849554723603289523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569587796932145929608772061 213595423849554723603289523)
              ·
                refine ⟨320393135774332085404934285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213595423849554723603289523 320393135774332085404934285)
                ·
                  refine ⟨120147425915374532026850357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320393135774332085404934285 120147425915374532026850357)
                  ·
                    refine ⟨11263821179566362377517221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 120147425915374532026850357 11263821179566362377517221)
                    ·
                      refine ⟨2111966471168692945784479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11263821179566362377517221 2111966471168692945784479)
                      ·
                        rfl

theorem cell23_4113040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_4113040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113040 prefixEnd_4113040 := by exact prefixLift 4113040
  have htrace : WordTrace (prefixWord ++ tailWord_4113040) baseStart_4113040 baseEnd_4113040 := by
    simpa [prefixWord, tailWord_4113040, baseEnd_4113040] using wordTrace_append hprefix tailTrace_4113040
  have hstable : (prefixWord ++ tailWord_4113040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113040).length < 2 ^ (prefixWord ++ tailWord_4113040).sum := by decide
  have hdescent : baseEnd_4113040 < baseStart_4113040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113074 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_4113074 : Nat := 118140960795 + 4113074 * 2 ^ 59
def prefixEnd_4113074 : Nat := 4983230072969 + 3 ^ 40 * 4113074 * 2
def baseEnd_4113074 : Nat := 2111983929510945812759323

theorem tailTrace_4113074 : CollatzResearch.WordTrace tailWord_4113074 prefixEnd_4113074 2111983929510945812759323 := by
  unfold tailWord_4113074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37504033275260707489710569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100010755400695219972561517 37504033275260707489710569)
  ·
    refine ⟨28128024956445530617282927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37504033275260707489710569 28128024956445530617282927)
    ·
      refine ⟨42192037434668295925924391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28128024956445530617282927 42192037434668295925924391)
      ·
        refine ⟨63288056152002443888886587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42192037434668295925924391 63288056152002443888886587)
        ·
          refine ⟨94932084228003665833329881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63288056152002443888886587 94932084228003665833329881)
          ·
            refine ⟨71199063171002749374997411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94932084228003665833329881 71199063171002749374997411)
            ·
              refine ⟨106798594756504124062496117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71199063171002749374997411 106798594756504124062496117)
              ·
                refine ⟨10012368258422261630859011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106798594756504124062496117 10012368258422261630859011)
                ·
                  refine ⟨15018552387633392446288517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10012368258422261630859011 15018552387633392446288517)
                  ·
                    refine ⟨2815978572681261083679097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15018552387633392446288517 2815978572681261083679097)
                    ·
                      refine ⟨2111983929510945812759323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2815978572681261083679097 2111983929510945812759323)
                      ·
                        rfl

theorem cell23_4113074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_4113074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113074 prefixEnd_4113074 := by exact prefixLift 4113074
  have htrace : WordTrace (prefixWord ++ tailWord_4113074) baseStart_4113074 baseEnd_4113074 := by
    simpa [prefixWord, tailWord_4113074, baseEnd_4113074] using wordTrace_append hprefix tailTrace_4113074
  have hstable : (prefixWord ++ tailWord_4113074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113074).length < 2 ^ (prefixWord ++ tailWord_4113074).sum := by decide
  have hdescent : baseEnd_4113074 < baseStart_4113074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113114 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_4113114 : Nat := 118140960795 + 4113114 * 2 ^ 59
def prefixEnd_4113114 : Nat := 4983230072969 + 3 ^ 40 * 4113114 * 2
def baseEnd_4113114 : Nat := 234667163193013961806571

theorem tailTrace_4113114 : CollatzResearch.WordTrace tailWord_4113114 prefixEnd_4113114 234667163193013961806571 := by
  unfold tailWord_4113114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37504398005224479197574599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100011728013931944526865597 37504398005224479197574599)
  ·
    refine ⟨56256597007836718796361899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37504398005224479197574599 56256597007836718796361899)
    ·
      refine ⟨84384895511755078194542849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56256597007836718796361899 84384895511755078194542849)
      ·
        refine ⟨63288671633816308645907137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84384895511755078194542849 63288671633816308645907137)
        ·
          refine ⟨47466503725362231484430353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63288671633816308645907137 47466503725362231484430353)
          ·
            refine ⟨35599877794021673613322765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47466503725362231484430353 35599877794021673613322765)
            ·
              refine ⟨13349954172758127604996037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35599877794021673613322765 13349954172758127604996037)
              ·
                refine ⟨2503116407392148925936757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13349954172758127604996037 2503116407392148925936757)
                ·
                  refine ⟨234667163193013961806571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2503116407392148925936757 234667163193013961806571)
                  ·
                    rfl

theorem cell23_4113114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_4113114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113114 prefixEnd_4113114 := by exact prefixLift 4113114
  have htrace : WordTrace (prefixWord ++ tailWord_4113114) baseStart_4113114 baseEnd_4113114 := by
    simpa [prefixWord, tailWord_4113114, baseEnd_4113114] using wordTrace_append hprefix tailTrace_4113114
  have hstable : (prefixWord ++ tailWord_4113114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113114).length < 2 ^ (prefixWord ++ tailWord_4113114).sum := by decide
  have hdescent : baseEnd_4113114 < baseStart_4113114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113124 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_4113124 : Nat := 118140960795 + 4113124 * 2 ^ 59
def prefixEnd_4113124 : Nat := 4983230072969 + 3 ^ 40 * 4113124 * 2
def baseEnd_4113124 : Nat := 2112009603543670617134093

theorem tailTrace_4113124 : CollatzResearch.WordTrace tailWord_4113124 prefixEnd_4113124 2112009603543670617134093 := by
  unfold tailWord_4113124
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008978375430844249081213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100011971167241125665441617 75008978375430844249081213)
  ·
    refine ⟨28128366890786566593405455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75008978375430844249081213 28128366890786566593405455)
    ·
      refine ⟨42192550336179849890108183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28128366890786566593405455 42192550336179849890108183)
      ·
        refine ⟨63288825504269774835162275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42192550336179849890108183 63288825504269774835162275)
        ·
          refine ⟨94933238256404662252743413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63288825504269774835162275 94933238256404662252743413)
          ·
            refine ⟨8899991086537937086194695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94933238256404662252743413 8899991086537937086194695)
            ·
              refine ⟨13349986629806905629292043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8899991086537937086194695 13349986629806905629292043)
              ·
                refine ⟨20024979944710358443938065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13349986629806905629292043 20024979944710358443938065)
                ·
                  refine ⟨15018734958532768832953549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20024979944710358443938065 15018734958532768832953549)
                  ·
                    refine ⟨5632025609449788312357581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15018734958532768832953549 5632025609449788312357581)
                    ·
                      refine ⟨2112009603543670617134093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632025609449788312357581 2112009603543670617134093)
                      ·
                        rfl

theorem cell23_4113124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_4113124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113124 prefixEnd_4113124 := by exact prefixLift 4113124
  have htrace : WordTrace (prefixWord ++ tailWord_4113124) baseStart_4113124 baseEnd_4113124 := by
    simpa [prefixWord, tailWord_4113124, baseEnd_4113124] using wordTrace_append hprefix tailTrace_4113124
  have hstable : (prefixWord ++ tailWord_4113124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113124).length < 2 ^ (prefixWord ++ tailWord_4113124).sum := by decide
  have hdescent : baseEnd_4113124 < baseStart_4113124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113184 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4113184 : Nat := 118140960795 + 4113184 * 2 ^ 59
def prefixEnd_4113184 : Nat := 4983230072969 + 3 ^ 40 * 4113184 * 2
def baseEnd_4113184 : Nat := 2112040412382940382383817

theorem tailTrace_4113184 : CollatzResearch.WordTrace tailWord_4113184 prefixEnd_4113184 2112040412382940382383817 := by
  unfold tailWord_4113184
  simp only [CollatzResearch.WordTrace]
  refine ⟨75010072565322159372673303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100013430087096212496897737 75010072565322159372673303)
  ·
    refine ⟨112515108847983239059009955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75010072565322159372673303 112515108847983239059009955)
    ·
      refine ⟨168772663271974858588514933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112515108847983239059009955 168772663271974858588514933)
      ·
        refine ⟨15822437181747642992673275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168772663271974858588514933 15822437181747642992673275)
        ·
          refine ⟨23733655772621464489009913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15822437181747642992673275 23733655772621464489009913)
          ·
            refine ⟨17800241829466098366757435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23733655772621464489009913 17800241829466098366757435)
            ·
              refine ⟨26700362744199147550136153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17800241829466098366757435 26700362744199147550136153)
              ·
                refine ⟨20025272058149360662602115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26700362744199147550136153 20025272058149360662602115)
                ·
                  refine ⟨30037908087224040993903173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20025272058149360662602115 30037908087224040993903173)
                  ·
                    refine ⟨5632107766354507686356845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30037908087224040993903173 5632107766354507686356845)
                    ·
                      refine ⟨2112040412382940382383817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632107766354507686356845 2112040412382940382383817)
                      ·
                        rfl

theorem cell23_4113184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4113184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113184 prefixEnd_4113184 := by exact prefixLift 4113184
  have htrace : WordTrace (prefixWord ++ tailWord_4113184) baseStart_4113184 baseEnd_4113184 := by
    simpa [prefixWord, tailWord_4113184, baseEnd_4113184] using wordTrace_append hprefix tailTrace_4113184
  have hstable : (prefixWord ++ tailWord_4113184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113184).length < 2 ^ (prefixWord ++ tailWord_4113184).sum := by decide
  have hdescent : baseEnd_4113184 < baseStart_4113184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113234 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4113234 : Nat := 118140960795 + 4113234 * 2 ^ 59
def prefixEnd_4113234 : Nat := 4983230072969 + 3 ^ 40 * 4113234 * 2
def baseEnd_4113234 : Nat := 704022028805221728919529

theorem tailTrace_4113234 : CollatzResearch.WordTrace tailWord_4113234 prefixEnd_4113234 704022028805221728919529 := by
  unfold tailWord_4113234
  simp only [CollatzResearch.WordTrace]
  refine ⟨37505492195115794321166689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100014645853642118189777837 37505492195115794321166689)
  ·
    refine ⟨28129119146336845740875017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37505492195115794321166689 28129119146336845740875017)
    ·
      refine ⟨21096839359752634305656263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28129119146336845740875017 21096839359752634305656263)
      ·
        refine ⟨31645259039628951458484395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21096839359752634305656263 31645259039628951458484395)
        ·
          refine ⟨47467888559443427187726593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31645259039628951458484395 47467888559443427187726593)
          ·
            refine ⟨35600916419582570390794945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47467888559443427187726593 35600916419582570390794945)
            ·
              refine ⟨26700687314686927793096209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35600916419582570390794945 26700687314686927793096209)
              ·
                refine ⟨20025515486015195844822157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26700687314686927793096209 20025515486015195844822157)
                ·
                  refine ⟨7509568307255698441808309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20025515486015195844822157 7509568307255698441808309)
                  ·
                    refine ⟨704022028805221728919529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7509568307255698441808309 704022028805221728919529)
                    ·
                      rfl

theorem cell23_4113234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4113234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113234 prefixEnd_4113234 := by exact prefixLift 4113234
  have htrace : WordTrace (prefixWord ++ tailWord_4113234) baseStart_4113234 baseEnd_4113234 := by
    simpa [prefixWord, tailWord_4113234, baseEnd_4113234] using wordTrace_append hprefix tailTrace_4113234
  have hstable : (prefixWord ++ tailWord_4113234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113234).length < 2 ^ (prefixWord ++ tailWord_4113234).sum := by decide
  have hdescent : baseEnd_4113234 < baseStart_4113234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113251 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 1, 5]
def baseStart_4113251 : Nat := 118140960795 + 4113251 * 2 ^ 59
def prefixEnd_4113251 : Nat := 4983230072969 + 3 ^ 40 * 4113251 * 2
def baseEnd_4113251 : Nat := 704024938528930540082003

theorem tailTrace_4113251 : CollatzResearch.WordTrace tailWord_4113251 prefixEnd_4113251 704024938528930540082003 := by
  unfold tailWord_4113251
  simp only [CollatzResearch.WordTrace]
  refine ⟨150022588821401589188035607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100015059214267726125357071 150022588821401589188035607)
  ·
    refine ⟨225033883232102383782053411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150022588821401589188035607 225033883232102383782053411)
    ·
      refine ⟨337550824848153575673080117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225033883232102383782053411 337550824848153575673080117)
      ·
        refine ⟨31645389829514397719351261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 337550824848153575673080117 31645389829514397719351261)
        ·
          refine ⟨11867021186067899144756723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31645389829514397719351261 11867021186067899144756723)
          ·
            refine ⟨17800531779101848717135085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867021186067899144756723 17800531779101848717135085)
            ·
              refine ⟨6675199417163193268925657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17800531779101848717135085 6675199417163193268925657)
              ·
                refine ⟨5006399562872394951694243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6675199417163193268925657 5006399562872394951694243)
                ·
                  refine ⟨7509599344308592427541365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5006399562872394951694243 7509599344308592427541365)
                  ·
                    refine ⟨704024938528930540082003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7509599344308592427541365 704024938528930540082003)
                    ·
                      rfl

theorem cell23_4113251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 5].length) (baseStart_4113251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113251 prefixEnd_4113251 := by exact prefixLift 4113251
  have htrace : WordTrace (prefixWord ++ tailWord_4113251) baseStart_4113251 baseEnd_4113251 := by
    simpa [prefixWord, tailWord_4113251, baseEnd_4113251] using wordTrace_append hprefix tailTrace_4113251
  have hstable : (prefixWord ++ tailWord_4113251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113251).length < 2 ^ (prefixWord ++ tailWord_4113251).sum := by decide
  have hdescent : baseEnd_4113251 < baseStart_4113251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113257 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_4113257 : Nat := 118140960795 + 4113257 * 2 ^ 59
def prefixEnd_4113257 : Nat := 4983230072969 + 3 ^ 40 * 4113257 * 2
def baseEnd_4113257 : Nat := 2112077896470718596770981

theorem tailTrace_4113257 : CollatzResearch.WordTrace tailWord_4113257 prefixEnd_4113257 2112077896470718596770981 := by
  unfold tailWord_4113257
  simp only [CollatzResearch.WordTrace]
  refine ⟨150022807659379852212754025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100015205106253234808502683 150022807659379852212754025)
  ·
    refine ⟨112517105744534889159565519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150022807659379852212754025 112517105744534889159565519)
    ·
      refine ⟨168775658616802333739348279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112517105744534889159565519 168775658616802333739348279)
      ·
        refine ⟨253163487925203500609022419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168775658616802333739348279 253163487925203500609022419)
        ·
          refine ⟨379745231887805250913533629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253163487925203500609022419 379745231887805250913533629)
          ·
            refine ⟨142404461957926969092575111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 379745231887805250913533629 142404461957926969092575111)
            ·
              refine ⟨213606692936890453638862667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142404461957926969092575111 213606692936890453638862667)
              ·
                refine ⟨320410039405335680458294001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213606692936890453638862667 320410039405335680458294001)
                ·
                  refine ⟨240307529554001760343720501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 320410039405335680458294001 240307529554001760343720501)
                  ·
                    refine ⟨22528830895687665032223797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 240307529554001760343720501 22528830895687665032223797)
                    ·
                      refine ⟨2112077896470718596770981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22528830895687665032223797 2112077896470718596770981)
                      ·
                        rfl

theorem cell23_4113257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_4113257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113257 prefixEnd_4113257 := by exact prefixLift 4113257
  have htrace : WordTrace (prefixWord ++ tailWord_4113257) baseStart_4113257 baseEnd_4113257 := by
    simpa [prefixWord, tailWord_4113257, baseEnd_4113257] using wordTrace_append hprefix tailTrace_4113257
  have hstable : (prefixWord ++ tailWord_4113257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113257).length < 2 ^ (prefixWord ++ tailWord_4113257).sum := by decide
  have hdescent : baseEnd_4113257 < baseStart_4113257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113264 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 6, 4]
def baseStart_4113264 : Nat := 118140960795 + 4113264 * 2 ^ 59
def prefixEnd_4113264 : Nat := 4983230072969 + 3 ^ 40 * 4113264 * 2
def baseEnd_4113264 : Nat := 704027163611766689794483

theorem tailTrace_4113264 : CollatzResearch.WordTrace tailWord_4113264 prefixEnd_4113264 704027163611766689794483 := by
  unfold tailWord_4113264
  simp only [CollatzResearch.WordTrace]
  refine ⟨75011531485177246204129423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100015375313569661605505897 75011531485177246204129423)
  ·
    refine ⟨112517297227765869306194135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75011531485177246204129423 112517297227765869306194135)
    ·
      refine ⟨168775945841648803959291203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112517297227765869306194135 168775945841648803959291203)
      ·
        refine ⟨253163918762473205938936805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168775945841648803959291203 253163918762473205938936805)
        ·
          refine ⟨47468234767963726113550651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 253163918762473205938936805 47468234767963726113550651)
          ·
            refine ⟨71202352151945589170325977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47468234767963726113550651 71202352151945589170325977)
            ·
              refine ⟨53401764113959191877744483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71202352151945589170325977 53401764113959191877744483)
              ·
                refine ⟨80102646170938787816616725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53401764113959191877744483 80102646170938787816616725)
                ·
                  refine ⟨3754811539262755678903909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80102646170938787816616725 3754811539262755678903909)
                  ·
                    refine ⟨704027163611766689794483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754811539262755678903909 704027163611766689794483)
                    ·
                      rfl

theorem cell23_4113264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_4113264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113264 prefixEnd_4113264 := by exact prefixLift 4113264
  have htrace : WordTrace (prefixWord ++ tailWord_4113264) baseStart_4113264 baseEnd_4113264 := by
    simpa [prefixWord, tailWord_4113264, baseEnd_4113264] using wordTrace_append hprefix tailTrace_4113264
  have hstable : (prefixWord ++ tailWord_4113264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113264).length < 2 ^ (prefixWord ++ tailWord_4113264).sum := by decide
  have hdescent : baseEnd_4113264 < baseStart_4113264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113284 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4113284 : Nat := 118140960795 + 4113284 * 2 ^ 59
def prefixEnd_4113284 : Nat := 4983230072969 + 3 ^ 40 * 4113284 * 2
def baseEnd_4113284 : Nat := 2112091760448389991133357

theorem tailTrace_4113284 : CollatzResearch.WordTrace tailWord_4113284 prefixEnd_4113284 2112091760448389991133357 := by
  unfold tailWord_4113284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75011896215141017911993453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100015861620188023882657937 75011896215141017911993453)
  ·
    refine ⟨28129461080677881716997545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75011896215141017911993453 28129461080677881716997545)
    ·
      refine ⟨21097095810508411287748159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28129461080677881716997545 21097095810508411287748159)
      ·
        refine ⟨31645643715762616931622239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097095810508411287748159 31645643715762616931622239)
        ·
          refine ⟨47468465573643925397433359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31645643715762616931622239 47468465573643925397433359)
          ·
            refine ⟨71202698360465888096150039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47468465573643925397433359 71202698360465888096150039)
            ·
              refine ⟨106804047540698832144225059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71202698360465888096150039 106804047540698832144225059)
              ·
                refine ⟨160206071311048248216337589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106804047540698832144225059 160206071311048248216337589)
                ·
                  refine ⟨15019319185410773270281649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 160206071311048248216337589 15019319185410773270281649)
                  ·
                    refine ⟨11264489389058079952711237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15019319185410773270281649 11264489389058079952711237)
                    ·
                      refine ⟨2112091760448389991133357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11264489389058079952711237 2112091760448389991133357)
                      ·
                        rfl

theorem cell23_4113284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4113284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113284 prefixEnd_4113284 := by exact prefixLift 4113284
  have htrace : WordTrace (prefixWord ++ tailWord_4113284) baseStart_4113284 baseEnd_4113284 := by
    simpa [prefixWord, tailWord_4113284, baseEnd_4113284] using wordTrace_append hprefix tailTrace_4113284
  have hstable : (prefixWord ++ tailWord_4113284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113284).length < 2 ^ (prefixWord ++ tailWord_4113284).sum := by decide
  have hdescent : baseEnd_4113284 < baseStart_4113284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113298 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4113298 : Nat := 118140960795 + 4113298 * 2 ^ 59
def prefixEnd_4113298 : Nat := 4983230072969 + 3 ^ 40 * 4113298 * 2
def baseEnd_4113298 : Nat := 704032983059184312119431

theorem tailTrace_4113298 : CollatzResearch.WordTrace tailWord_4113298 prefixEnd_4113298 704032983059184312119431 := by
  unfold tailWord_4113298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37506075763057829053749137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100016202034820877476664365 37506075763057829053749137)
  ·
    refine ⟨28129556822293371790311853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37506075763057829053749137 28129556822293371790311853)
    ·
      refine ⟨10548583808360014421366945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28129556822293371790311853 10548583808360014421366945)
      ·
        refine ⟨7911437856270010816025209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10548583808360014421366945 7911437856270010816025209)
        ·
          refine ⟨5933578392202508112018907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7911437856270010816025209 5933578392202508112018907)
          ·
            refine ⟨8900367588303762168028361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933578392202508112018907 8900367588303762168028361)
            ·
              refine ⟨6675275691227821626021271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8900367588303762168028361 6675275691227821626021271)
              ·
                refine ⟨10012913536841732439031907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675275691227821626021271 10012913536841732439031907)
                ·
                  refine ⟨15019370305262598658547861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10012913536841732439031907 15019370305262598658547861)
                  ·
                    refine ⟨704032983059184312119431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15019370305262598658547861 704032983059184312119431)
                    ·
                      rfl

theorem cell23_4113298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4113298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113298 prefixEnd_4113298 := by exact prefixLift 4113298
  have htrace : WordTrace (prefixWord ++ tailWord_4113298) baseStart_4113298 baseEnd_4113298 := by
    simpa [prefixWord, tailWord_4113298, baseEnd_4113298] using wordTrace_append hprefix tailTrace_4113298
  have hstable : (prefixWord ++ tailWord_4113298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113298).length < 2 ^ (prefixWord ++ tailWord_4113298).sum := by decide
  have hdescent : baseEnd_4113298 < baseStart_4113298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113301 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_4113301 : Nat := 118140960795 + 4113301 * 2 ^ 59
def prefixEnd_4113301 : Nat := 4983230072969 + 3 ^ 40 * 4113301 * 2
def baseEnd_4113301 : Nat := 2112100489619516424620779

theorem tailTrace_4113301 : CollatzResearch.WordTrace tailWord_4113301 prefixEnd_4113301 2112100489619516424620779 := by
  unfold tailWord_4113301
  simp only [CollatzResearch.WordTrace]
  refine ⟨150024412471220447727355757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100016274980813631818237171 150024412471220447727355757)
  ·
    refine ⟨56259154676707667897758409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150024412471220447727355757 56259154676707667897758409)
    ·
      refine ⟨42194366007530750923318807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56259154676707667897758409 42194366007530750923318807)
      ·
        refine ⟨63291549011296126384978211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42194366007530750923318807 63291549011296126384978211)
        ·
          refine ⟨94937323516944189577467317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63291549011296126384978211 94937323516944189577467317)
          ·
            refine ⟨8900374079713517772887561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94937323516944189577467317 8900374079713517772887561)
            ·
              refine ⟨6675280559785138329665671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8900374079713517772887561 6675280559785138329665671)
              ·
                refine ⟨10012920839677707494498507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675280559785138329665671 10012920839677707494498507)
                ·
                  refine ⟨15019381259516561241747761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10012920839677707494498507 15019381259516561241747761)
                  ·
                    refine ⟨11264535944637420931310821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15019381259516561241747761 11264535944637420931310821)
                    ·
                      refine ⟨2112100489619516424620779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11264535944637420931310821 2112100489619516424620779)
                      ·
                        rfl

theorem cell23_4113301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_4113301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113301 prefixEnd_4113301 := by exact prefixLift 4113301
  have htrace : WordTrace (prefixWord ++ tailWord_4113301) baseStart_4113301 baseEnd_4113301 := by
    simpa [prefixWord, tailWord_4113301, baseEnd_4113301] using wordTrace_append hprefix tailTrace_4113301
  have hstable : (prefixWord ++ tailWord_4113301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113301).length < 2 ^ (prefixWord ++ tailWord_4113301).sum := by decide
  have hdescent : baseEnd_4113301 < baseStart_4113301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113311 : List Nat := [1, 1, 2, 5, 2, 2, 3, 7]
def baseStart_4113311 : Nat := 118140960795 + 4113311 * 2 ^ 59
def prefixEnd_4113311 : Nat := 4983230072969 + 3 ^ 40 * 4113311 * 2
def baseEnd_4113311 : Nat := 78226134238002273536879

theorem tailTrace_4113311 : CollatzResearch.WordTrace tailWord_4113311 prefixEnd_4113311 78226134238002273536879 := by
  unfold tailWord_4113311
  simp only [CollatzResearch.WordTrace]
  refine ⟨150024777201184219435219787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100016518134122812956813191 150024777201184219435219787)
  ·
    refine ⟨225037165801776329152829681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150024777201184219435219787 225037165801776329152829681)
    ·
      refine ⟨168777874351332246864622261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225037165801776329152829681 168777874351332246864622261)
      ·
        refine ⟨15822925720437398143558337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168777874351332246864622261 15822925720437398143558337)
        ·
          refine ⟨11867194290328048607668753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15822925720437398143558337 11867194290328048607668753)
          ·
            refine ⟨8900395717746036455751565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11867194290328048607668753 8900395717746036455751565)
            ·
              refine ⟨3337648394154763670906837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8900395717746036455751565 3337648394154763670906837)
              ·
                refine ⟨78226134238002273536879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3337648394154763670906837 78226134238002273536879)
                ·
                  rfl

theorem cell23_4113311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 7].length) (baseStart_4113311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113311 prefixEnd_4113311 := by exact prefixLift 4113311
  have htrace : WordTrace (prefixWord ++ tailWord_4113311) baseStart_4113311 baseEnd_4113311 := by
    simpa [prefixWord, tailWord_4113311, baseEnd_4113311] using wordTrace_append hprefix tailTrace_4113311
  have hstable : (prefixWord ++ tailWord_4113311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113311).length < 2 ^ (prefixWord ++ tailWord_4113311).sum := by decide
  have hdescent : baseEnd_4113311 < baseStart_4113311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113321 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 3]
def baseStart_4113321 : Nat := 118140960795 + 4113321 * 2 ^ 59
def prefixEnd_4113321 : Nat := 4983230072969 + 3 ^ 40 * 4113321 * 2
def baseEnd_4113321 : Nat := 2112110759232606346370687

theorem tailTrace_4113321 : CollatzResearch.WordTrace tailWord_4113321 prefixEnd_4113321 2112110759232606346370687 := by
  unfold tailWord_4113321
  simp only [CollatzResearch.WordTrace]
  refine ⟨150025141931147991143083817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100016761287431994095389211 150025141931147991143083817)
  ·
    refine ⟨112518856448360993357312863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150025141931147991143083817 112518856448360993357312863)
    ·
      refine ⟨168778284672541490035969295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112518856448360993357312863 168778284672541490035969295)
      ·
        refine ⟨253167427008812235053953943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168778284672541490035969295 253167427008812235053953943)
        ·
          refine ⟨379751140513218352580930915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253167427008812235053953943 379751140513218352580930915)
          ·
            refine ⟨569626710769827528871396373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379751140513218352580930915 569626710769827528871396373)
            ·
              refine ⟨26701252067335665415846705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 569626710769827528871396373 26701252067335665415846705)
              ·
                refine ⟨20025939050501749061885029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26701252067335665415846705 20025939050501749061885029)
                ·
                  refine ⟨3754863571969077949103443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20025939050501749061885029 3754863571969077949103443)
                  ·
                    refine ⟨5632295357953616923655165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3754863571969077949103443 5632295357953616923655165)
                    ·
                      refine ⟨2112110759232606346370687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632295357953616923655165 2112110759232606346370687)
                      ·
                        rfl

theorem cell23_4113321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_4113321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113321 prefixEnd_4113321 := by exact prefixLift 4113321
  have htrace : WordTrace (prefixWord ++ tailWord_4113321) baseStart_4113321 baseEnd_4113321 := by
    simpa [prefixWord, tailWord_4113321, baseEnd_4113321] using wordTrace_append hprefix tailTrace_4113321
  have hstable : (prefixWord ++ tailWord_4113321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113321).length < 2 ^ (prefixWord ++ tailWord_4113321).sum := by decide
  have hdescent : baseEnd_4113321 < baseStart_4113321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113331 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 5, 3, 2]
def baseStart_4113331 : Nat := 118140960795 + 4113331 * 2 ^ 59
def prefixEnd_4113331 : Nat := 4983230072969 + 3 ^ 40 * 4113331 * 2
def baseEnd_4113331 : Nat := 2112115894039151307245641

theorem tailTrace_4113331 : CollatzResearch.WordTrace tailWord_4113331 prefixEnd_4113331 2112115894039151307245641 := by
  unfold tailWord_4113331
  simp only [CollatzResearch.WordTrace]
  refine ⟨150025506661111762850947847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100017004440741175233965231 150025506661111762850947847)
  ·
    refine ⟨225038259991667644276421771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150025506661111762850947847 225038259991667644276421771)
    ·
      refine ⟨337557389987501466414632657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225038259991667644276421771 337557389987501466414632657)
      ·
        refine ⟨253168042490626099810974493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337557389987501466414632657 253168042490626099810974493)
        ·
          refine ⟨94938015933984787429115435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253168042490626099810974493 94938015933984787429115435)
          ·
            refine ⟨142407023900977181143673153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94938015933984787429115435 142407023900977181143673153)
            ·
              refine ⟨106805267925732885857754865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142407023900977181143673153 106805267925732885857754865)
              ·
                refine ⟨80103950944299664393316149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106805267925732885857754865 80103950944299664393316149)
                ·
                  refine ⟨7509745401028093536873389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80103950944299664393316149 7509745401028093536873389)
                  ·
                    refine ⟨2816154525385535076327521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7509745401028093536873389 2816154525385535076327521)
                    ·
                      refine ⟨2112115894039151307245641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816154525385535076327521 2112115894039151307245641)
                      ·
                        rfl

theorem cell23_4113331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3, 2].length) (baseStart_4113331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113331 prefixEnd_4113331 := by exact prefixLift 4113331
  have htrace : WordTrace (prefixWord ++ tailWord_4113331) baseStart_4113331 baseEnd_4113331 := by
    simpa [prefixWord, tailWord_4113331, baseEnd_4113331] using wordTrace_append hprefix tailTrace_4113331
  have hstable : (prefixWord ++ tailWord_4113331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113331).length < 2 ^ (prefixWord ++ tailWord_4113331).sum := by decide
  have hdescent : baseEnd_4113331 < baseStart_4113331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113332 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4113332 : Nat := 118140960795 + 4113332 * 2 ^ 59
def prefixEnd_4113332 : Nat := 4983230072969 + 3 ^ 40 * 4113332 * 2
def baseEnd_4113332 : Nat := 704038802506601934444379

theorem tailTrace_4113332 : CollatzResearch.WordTrace tailWord_4113332 prefixEnd_4113332 704038802506601934444379 := by
  unfold tailWord_4113332
  simp only [CollatzResearch.WordTrace]
  refine ⟨75012771567054070010867125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100017028756072093347822833 75012771567054070010867125)
  ·
    refine ⟨7032447334411319063518793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75012771567054070010867125 7032447334411319063518793)
    ·
      refine ⟨5274335500808489297639095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7032447334411319063518793 5274335500808489297639095)
      ·
        refine ⟨7911503251212733946458643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5274335500808489297639095 7911503251212733946458643)
        ·
          refine ⟨11867254876819100919687965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911503251212733946458643 11867254876819100919687965)
          ·
            refine ⟨4450220578807162844882987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11867254876819100919687965 4450220578807162844882987)
            ·
              refine ⟨6675330868210744267324481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450220578807162844882987 6675330868210744267324481)
              ·
                refine ⟨5006498151158058200493361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6675330868210744267324481 5006498151158058200493361)
                ·
                  refine ⟨3754873613368543650370021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006498151158058200493361 3754873613368543650370021)
                  ·
                    refine ⟨704038802506601934444379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3754873613368543650370021 704038802506601934444379)
                    ·
                      rfl

theorem cell23_4113332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4113332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113332 prefixEnd_4113332 := by exact prefixLift 4113332
  have htrace : WordTrace (prefixWord ++ tailWord_4113332) baseStart_4113332 baseEnd_4113332 := by
    simpa [prefixWord, tailWord_4113332, baseEnd_4113332] using wordTrace_append hprefix tailTrace_4113332
  have hstable : (prefixWord ++ tailWord_4113332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113332).length < 2 ^ (prefixWord ++ tailWord_4113332).sum := by decide
  have hdescent : baseEnd_4113332 < baseStart_4113332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113355 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 2, 1, 3]
def baseStart_4113355 : Nat := 118140960795 + 4113355 * 2 ^ 59
def prefixEnd_4113355 : Nat := 4983230072969 + 3 ^ 40 * 4113355 * 2
def baseEnd_4113355 : Nat := 2112128217574859213345531

theorem tailTrace_4113355 : CollatzResearch.WordTrace tailWord_4113355 prefixEnd_4113355 2112128217574859213345531 := by
  unfold tailWord_4113355
  simp only [CollatzResearch.WordTrace]
  refine ⟨150026382013024814949821519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100017588008683209966547679 150026382013024814949821519)
  ·
    refine ⟨225039573019537222424732279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150026382013024814949821519 225039573019537222424732279)
    ·
      refine ⟨337559359529305833637098419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225039573019537222424732279 337559359529305833637098419)
      ·
        refine ⟨506339039293958750455647629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337559359529305833637098419 506339039293958750455647629)
        ·
          refine ⟨189877139735234531420867861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506339039293958750455647629 189877139735234531420867861)
          ·
            refine ⟨8900490925089118660353181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189877139735234531420867861 8900490925089118660353181)
            ·
              refine ⟨3337684096908419497632443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8900490925089118660353181 3337684096908419497632443)
              ·
                refine ⟨5006526145362629246448665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337684096908419497632443 5006526145362629246448665)
                ·
                  refine ⟨3754894609021971934836499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006526145362629246448665 3754894609021971934836499)
                  ·
                    refine ⟨5632341913532957902254749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3754894609021971934836499 5632341913532957902254749)
                    ·
                      refine ⟨2112128217574859213345531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632341913532957902254749 2112128217574859213345531)
                      ·
                        rfl

theorem cell23_4113355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 1, 3].length) (baseStart_4113355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113355 prefixEnd_4113355 := by exact prefixLift 4113355
  have htrace : WordTrace (prefixWord ++ tailWord_4113355) baseStart_4113355 baseEnd_4113355 := by
    simpa [prefixWord, tailWord_4113355, baseEnd_4113355] using wordTrace_append hprefix tailTrace_4113355
  have hstable : (prefixWord ++ tailWord_4113355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113355).length < 2 ^ (prefixWord ++ tailWord_4113355).sum := by decide
  have hdescent : baseEnd_4113355 < baseStart_4113355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113384 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 9]
def baseStart_4113384 : Nat := 118140960795 + 4113384 * 2 ^ 59
def prefixEnd_4113384 : Nat := 4983230072969 + 3 ^ 40 * 4113384 * 2
def baseEnd_4113384 : Nat := 234682567612648844431433

theorem tailTrace_4113384 : CollatzResearch.WordTrace tailWord_4113384 prefixEnd_4113384 234682567612648844431433 := by
  unfold tailWord_4113384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75013719864959876451313603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100018293153279835268418137 75013719864959876451313603)
  ·
    refine ⟨112520579797439814676970405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75013719864959876451313603 112520579797439814676970405)
    ·
      refine ⟨21097608712019965251931951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112520579797439814676970405 21097608712019965251931951)
      ·
        refine ⟨31646413068029947877897927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21097608712019965251931951 31646413068029947877897927)
        ·
          refine ⟨47469619602044921816846891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31646413068029947877897927 47469619602044921816846891)
          ·
            refine ⟨71204429403067382725270337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47469619602044921816846891 71204429403067382725270337)
            ·
              refine ⟨53403322052300537043952753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71204429403067382725270337 53403322052300537043952753)
              ·
                refine ⟨40052491539225402782964565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53403322052300537043952753 40052491539225402782964565)
                ·
                  refine ⟨234682567612648844431433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40052491539225402782964565 234682567612648844431433)
                  ·
                    rfl

theorem cell23_4113384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_4113384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113384 prefixEnd_4113384 := by exact prefixLift 4113384
  have htrace : WordTrace (prefixWord ++ tailWord_4113384) baseStart_4113384 baseEnd_4113384 := by
    simpa [prefixWord, tailWord_4113384, baseEnd_4113384] using wordTrace_append hprefix tailTrace_4113384
  have hstable : (prefixWord ++ tailWord_4113384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113384).length < 2 ^ (prefixWord ++ tailWord_4113384).sum := by decide
  have hdescent : baseEnd_4113384 < baseStart_4113384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113406 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_4113406 : Nat := 118140960795 + 4113406 * 2 ^ 59
def prefixEnd_4113406 : Nat := 4983230072969 + 3 ^ 40 * 4113406 * 2
def baseEnd_4113406 : Nat := 2112154405088238513807797

theorem tailTrace_4113406 : CollatzResearch.WordTrace tailWord_4113406 prefixEnd_4113406 2112154405088238513807797 := by
  unfold tailWord_4113406
  simp only [CollatzResearch.WordTrace]
  refine ⟨18753530266980006332491009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100018828090560033773285381 18753530266980006332491009)
  ·
    refine ⟨14065147700235004749368257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18753530266980006332491009 14065147700235004749368257)
    ·
      refine ⟨10548860775176253562026193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14065147700235004749368257 10548860775176253562026193)
      ·
        refine ⟨7911645581382190171519645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10548860775176253562026193 7911645581382190171519645)
        ·
          refine ⟨2966867093018321314319867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7911645581382190171519645 2966867093018321314319867)
          ·
            refine ⟨4450300639527481971479801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2966867093018321314319867 4450300639527481971479801)
            ·
              refine ⟨3337725479645611478609851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450300639527481971479801 3337725479645611478609851)
              ·
                refine ⟨5006588219468417217914777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3337725479645611478609851 5006588219468417217914777)
                ·
                  refine ⟨3754941164601312913436083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006588219468417217914777 3754941164601312913436083)
                  ·
                    refine ⟨5632411746901969370154125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3754941164601312913436083 5632411746901969370154125)
                    ·
                      refine ⟨2112154405088238513807797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632411746901969370154125 2112154405088238513807797)
                      ·
                        rfl

theorem cell23_4113406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_4113406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113406 prefixEnd_4113406 := by exact prefixLift 4113406
  have htrace : WordTrace (prefixWord ++ tailWord_4113406) baseStart_4113406 baseEnd_4113406 := by
    simpa [prefixWord, tailWord_4113406, baseEnd_4113406] using wordTrace_append hprefix tailTrace_4113406
  have hstable : (prefixWord ++ tailWord_4113406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113406).length < 2 ^ (prefixWord ++ tailWord_4113406).sum := by decide
  have hdescent : baseEnd_4113406 < baseStart_4113406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113424 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_4113424 : Nat := 118140960795 + 4113424 * 2 ^ 59
def prefixEnd_4113424 : Nat := 4983230072969 + 3 ^ 40 * 4113424 * 2
def baseEnd_4113424 : Nat := 2112163647740019443382713

theorem tailTrace_4113424 : CollatzResearch.WordTrace tailWord_4113424 prefixEnd_4113424 2112163647740019443382713 := by
  unfold tailWord_4113424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75014449324887419867041663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100019265766516559822722217 75014449324887419867041663)
  ·
    refine ⟨112521673987331129800562495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75014449324887419867041663 112521673987331129800562495)
    ·
      refine ⟨168782510980996694700843743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112521673987331129800562495 168782510980996694700843743)
      ·
        refine ⟨253173766471495042051265615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168782510980996694700843743 253173766471495042051265615)
        ·
          refine ⟨379760649707242563076898423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253173766471495042051265615 379760649707242563076898423)
          ·
            refine ⟨569640974560863844615347635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379760649707242563076898423 569640974560863844615347635)
            ·
              refine ⟨854461461841295766923021453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569640974560863844615347635 854461461841295766923021453)
              ·
                refine ⟨320423048190485912596133045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 854461461841295766923021453 320423048190485912596133045)
                ·
                  refine ⟨30039660767858054305887473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320423048190485912596133045 30039660767858054305887473)
                  ·
                    refine ⟨22529745575893540729415605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30039660767858054305887473 22529745575893540729415605)
                    ·
                      refine ⟨2112163647740019443382713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22529745575893540729415605 2112163647740019443382713)
                      ·
                        rfl

theorem cell23_4113424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_4113424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113424 prefixEnd_4113424 := by exact prefixLift 4113424
  have htrace : WordTrace (prefixWord ++ tailWord_4113424) baseStart_4113424 baseEnd_4113424 := by
    simpa [prefixWord, tailWord_4113424, baseEnd_4113424] using wordTrace_append hprefix tailTrace_4113424
  have hstable : (prefixWord ++ tailWord_4113424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113424).length < 2 ^ (prefixWord ++ tailWord_4113424).sum := by decide
  have hdescent : baseEnd_4113424 < baseStart_4113424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113441 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4113441 : Nat := 118140960795 + 4113441 * 2 ^ 59
def prefixEnd_4113441 : Nat := 4983230072969 + 3 ^ 40 * 4113441 * 2
def baseEnd_4113441 : Nat := 2112172376911145876870135

theorem tailTrace_4113441 : CollatzResearch.WordTrace tailWord_4113441 prefixEnd_4113441 2112172376911145876870135 := by
  unfold tailWord_4113441
  simp only [CollatzResearch.WordTrace]
  refine ⟨150029518690713251637452177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100019679127142167758301451 150029518690713251637452177)
  ·
    refine ⟨112522139018034938728089133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150029518690713251637452177 112522139018034938728089133)
    ·
      refine ⟨42195802131763102023033425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112522139018034938728089133 42195802131763102023033425)
      ·
        refine ⟨31646851598822326517275069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42195802131763102023033425 31646851598822326517275069)
        ·
          refine ⟨11867569349558372443978151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31646851598822326517275069 11867569349558372443978151)
          ·
            refine ⟨17801354024337558665967227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867569349558372443978151 17801354024337558665967227)
            ·
              refine ⟨26702031036506337998950841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17801354024337558665967227 26702031036506337998950841)
              ·
                refine ⟨20026523277379753499213131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26702031036506337998950841 20026523277379753499213131)
                ·
                  refine ⟨30039784916069630248819697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20026523277379753499213131 30039784916069630248819697)
                  ·
                    refine ⟨22529838687052222686614773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30039784916069630248819697 22529838687052222686614773)
                    ·
                      refine ⟨2112172376911145876870135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22529838687052222686614773 2112172376911145876870135)
                      ·
                        rfl

theorem cell23_4113441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4113441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113441 prefixEnd_4113441 := by exact prefixLift 4113441
  have htrace : WordTrace (prefixWord ++ tailWord_4113441) baseStart_4113441 baseEnd_4113441 := by
    simpa [prefixWord, tailWord_4113441, baseEnd_4113441] using wordTrace_append hprefix tailTrace_4113441
  have hstable : (prefixWord ++ tailWord_4113441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113441).length < 2 ^ (prefixWord ++ tailWord_4113441).sum := by decide
  have hdescent : baseEnd_4113441 < baseStart_4113441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113451 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 4]
def baseStart_4113451 : Nat := 118140960795 + 4113451 * 2 ^ 59
def prefixEnd_4113451 : Nat := 4983230072969 + 3 ^ 40 * 4113451 * 2
def baseEnd_4113451 : Nat := 2112177511717690837745089

theorem tailTrace_4113451 : CollatzResearch.WordTrace tailWord_4113451 prefixEnd_4113451 2112177511717690837745089 := by
  unfold tailWord_4113451
  simp only [CollatzResearch.WordTrace]
  refine ⟨150029883420677023345316207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100019922280451348896877471 150029883420677023345316207)
  ·
    refine ⟨225044825131015535017974311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150029883420677023345316207 225044825131015535017974311)
    ·
      refine ⟨337567237696523302526961467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225044825131015535017974311 337567237696523302526961467)
      ·
        refine ⟨506350856544784953790442201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337567237696523302526961467 506350856544784953790442201)
        ·
          refine ⟨379763142408588715342831651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 506350856544784953790442201 379763142408588715342831651)
          ·
            refine ⟨569644713612883073014247477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379763142408588715342831651 569644713612883073014247477)
            ·
              refine ⟨53404191901207788095085701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 569644713612883073014247477 53404191901207788095085701)
              ·
                refine ⟨10013285981476460267828569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53404191901207788095085701 10013285981476460267828569)
                ·
                  refine ⟨7509964486107345200871427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013285981476460267828569 7509964486107345200871427)
                  ·
                    refine ⟨11264946729161017801307141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7509964486107345200871427 11264946729161017801307141)
                    ·
                      refine ⟨2112177511717690837745089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11264946729161017801307141 2112177511717690837745089)
                      ·
                        rfl

theorem cell23_4113451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 4].length) (baseStart_4113451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113451 prefixEnd_4113451 := by exact prefixLift 4113451
  have htrace : WordTrace (prefixWord ++ tailWord_4113451) baseStart_4113451 baseEnd_4113451 := by
    simpa [prefixWord, tailWord_4113451, baseEnd_4113451] using wordTrace_append hprefix tailTrace_4113451
  have hstable : (prefixWord ++ tailWord_4113451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113451).length < 2 ^ (prefixWord ++ tailWord_4113451).sum := by decide
  have hdescent : baseEnd_4113451 < baseStart_4113451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113468 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 6, 2]
def baseStart_4113468 : Nat := 118140960795 + 4113468 * 2 ^ 59
def prefixEnd_4113468 : Nat := 4983230072969 + 3 ^ 40 * 4113468 * 2
def baseEnd_4113468 : Nat := 2112186240888817271232511

theorem tailTrace_4113468 : CollatzResearch.WordTrace tailWord_4113468 prefixEnd_4113468 2112186240888817271232511 := by
  unfold tailWord_4113468
  simp only [CollatzResearch.WordTrace]
  refine ⟨75015251730807717624342529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100020335641076956832456705 75015251730807717624342529)
  ·
    refine ⟨56261438798105788218256897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75015251730807717624342529 56261438798105788218256897)
    ·
      refine ⟨42196079098579341163692673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56261438798105788218256897 42196079098579341163692673)
      ·
        refine ⟨31647059323934505872769505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42196079098579341163692673 31647059323934505872769505)
        ·
          refine ⟨23735294492950879404577129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31647059323934505872769505 23735294492950879404577129)
          ·
            refine ⟨17801470869713159553432847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23735294492950879404577129 17801470869713159553432847)
            ·
              refine ⟨26702206304569739330149271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17801470869713159553432847 26702206304569739330149271)
              ·
                refine ⟨40053309456854608995223907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26702206304569739330149271 40053309456854608995223907)
                ·
                  refine ⟨60079964185281913492835861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40053309456854608995223907 60079964185281913492835861)
                  ·
                    refine ⟨2816248321185089694976681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60079964185281913492835861 2816248321185089694976681)
                    ·
                      refine ⟨2112186240888817271232511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816248321185089694976681 2112186240888817271232511)
                      ·
                        rfl

theorem cell23_4113468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_4113468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113468 prefixEnd_4113468 := by exact prefixLift 4113468
  have htrace : WordTrace (prefixWord ++ tailWord_4113468) baseStart_4113468 baseEnd_4113468 := by
    simpa [prefixWord, tailWord_4113468, baseEnd_4113468] using wordTrace_append hprefix tailTrace_4113468
  have hstable : (prefixWord ++ tailWord_4113468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113468).length < 2 ^ (prefixWord ++ tailWord_4113468).sum := by decide
  have hdescent : baseEnd_4113468 < baseStart_4113468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113471 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_4113471 : Nat := 118140960795 + 4113471 * 2 ^ 59
def prefixEnd_4113471 : Nat := 4983230072969 + 3 ^ 40 * 4113471 * 2
def baseEnd_4113471 : Nat := 2112187781330780759494997

theorem tailTrace_4113471 : CollatzResearch.WordTrace tailWord_4113471 prefixEnd_4113471 2112187781330780759494997 := by
  unfold tailWord_4113471
  simp only [CollatzResearch.WordTrace]
  refine ⟨150030612880604566761044267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100020408587069711174029511 150030612880604566761044267)
  ·
    refine ⟨225045919320906850141566401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150030612880604566761044267 225045919320906850141566401)
    ·
      refine ⟨168784439490680137606174801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225045919320906850141566401 168784439490680137606174801)
      ·
        refine ⟨126588329618010103204631101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168784439490680137606174801 126588329618010103204631101)
        ·
          refine ⟨47470623606753788701736663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126588329618010103204631101 47470623606753788701736663)
          ·
            refine ⟨71205935410130683052604995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47470623606753788701736663 71205935410130683052604995)
            ·
              refine ⟨106808903115196024578907493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71205935410130683052604995 106808903115196024578907493)
              ·
                refine ⟨20026669334099254608545155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106808903115196024578907493 20026669334099254608545155)
                ·
                  refine ⟨30040004001148881912817733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20026669334099254608545155 30040004001148881912817733)
                  ·
                    refine ⟨5632500750215415358653325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30040004001148881912817733 5632500750215415358653325)
                    ·
                      refine ⟨2112187781330780759494997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632500750215415358653325 2112187781330780759494997)
                      ·
                        rfl

theorem cell23_4113471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_4113471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113471 prefixEnd_4113471 := by exact prefixLift 4113471
  have htrace : WordTrace (prefixWord ++ tailWord_4113471) baseStart_4113471 baseEnd_4113471 := by
    simpa [prefixWord, tailWord_4113471, baseEnd_4113471] using wordTrace_append hprefix tailTrace_4113471
  have hstable : (prefixWord ++ tailWord_4113471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113471).length < 2 ^ (prefixWord ++ tailWord_4113471).sum := by decide
  have hdescent : baseEnd_4113471 < baseStart_4113471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113485 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4113485 : Nat := 118140960795 + 4113485 * 2 ^ 59
def prefixEnd_4113485 : Nat := 4983230072969 + 3 ^ 40 * 4113485 * 2
def baseEnd_4113485 : Nat := 2112194970059943704719933

theorem tailTrace_4113485 : CollatzResearch.WordTrace tailWord_4113485 prefixEnd_4113485 2112194970059943704719933 := by
  unfold tailWord_4113485
  simp only [CollatzResearch.WordTrace]
  refine ⟨150031123502553847152053909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100020749001702564768035939 150031123502553847152053909)
  ·
    refine ⟨7032708914182211585252527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 150031123502553847152053909 7032708914182211585252527)
    ·
      refine ⟨10549063371273317377878791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032708914182211585252527 10549063371273317377878791)
      ·
        refine ⟨15823595056909976066818187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10549063371273317377878791 15823595056909976066818187)
        ·
          refine ⟨23735392585364964100227281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15823595056909976066818187 23735392585364964100227281)
          ·
            refine ⟨17801544439023723075170461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23735392585364964100227281 17801544439023723075170461)
            ·
              refine ⟨6675579164633896153188923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17801544439023723075170461 6675579164633896153188923)
              ·
                refine ⟨10013368746950844229783385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675579164633896153188923 10013368746950844229783385)
                ·
                  refine ⟨7510026560213133172337539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013368746950844229783385 7510026560213133172337539)
                  ·
                    refine ⟨11265039840319699758506309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7510026560213133172337539 11265039840319699758506309)
                    ·
                      refine ⟨2112194970059943704719933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11265039840319699758506309 2112194970059943704719933)
                      ·
                        rfl

theorem cell23_4113485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4113485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113485 prefixEnd_4113485 := by exact prefixLift 4113485
  have htrace : WordTrace (prefixWord ++ tailWord_4113485) baseStart_4113485 baseEnd_4113485 := by
    simpa [prefixWord, tailWord_4113485, baseEnd_4113485] using wordTrace_append hprefix tailTrace_4113485
  have hstable : (prefixWord ++ tailWord_4113485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113485).length < 2 ^ (prefixWord ++ tailWord_4113485).sum := by decide
  have hdescent : baseEnd_4113485 < baseStart_4113485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113511 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_4113511 : Nat := 118140960795 + 4113511 * 2 ^ 59
def prefixEnd_4113511 : Nat := 4983230072969 + 3 ^ 40 * 4113511 * 2
def baseEnd_4113511 : Nat := 2112208320556960602994813

theorem tailTrace_4113511 : CollatzResearch.WordTrace tailWord_4113511 prefixEnd_4113511 2112208320556960602994813 := by
  unfold tailWord_4113511
  simp only [CollatzResearch.WordTrace]
  refine ⟨150032071800459653592500387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100021381200306435728333591 150032071800459653592500387)
  ·
    refine ⟨225048107700689480388750581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150032071800459653592500387 225048107700689480388750581)
    ·
      refine ⟨21098260096939638786445367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 225048107700689480388750581 21098260096939638786445367)
      ·
        refine ⟨31647390145409458179668051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21098260096939638786445367 31647390145409458179668051)
        ·
          refine ⟨47471085218114187269502077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31647390145409458179668051 47471085218114187269502077)
          ·
            refine ⟨17801656956792820226063279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47471085218114187269502077 17801656956792820226063279)
            ·
              refine ⟨26702485435189230339094919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17801656956792820226063279 26702485435189230339094919)
              ·
                refine ⟨40053728152783845508642379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26702485435189230339094919 40053728152783845508642379)
                ·
                  refine ⟨60080592229175768262963569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40053728152783845508642379 60080592229175768262963569)
                  ·
                    refine ⟨45060444171881826197222677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60080592229175768262963569 45060444171881826197222677)
                    ·
                      refine ⟨2112208320556960602994813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45060444171881826197222677 2112208320556960602994813)
                      ·
                        rfl

theorem cell23_4113511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_4113511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113511 prefixEnd_4113511 := by exact prefixLift 4113511
  have htrace : WordTrace (prefixWord ++ tailWord_4113511) baseStart_4113511 baseEnd_4113511 := by
    simpa [prefixWord, tailWord_4113511, baseEnd_4113511] using wordTrace_append hprefix tailTrace_4113511
  have hstable : (prefixWord ++ tailWord_4113511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113511).length < 2 ^ (prefixWord ++ tailWord_4113511).sum := by decide
  have hdescent : baseEnd_4113511 < baseStart_4113511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113512 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 3, 4]
def baseStart_4113512 : Nat := 118140960795 + 4113512 * 2 ^ 59
def prefixEnd_4113512 : Nat := 4983230072969 + 3 ^ 40 * 4113512 * 2
def baseEnd_4113512 : Nat := 704069611345871699694103

theorem tailTrace_4113512 : CollatzResearch.WordTrace tailWord_4113512 prefixEnd_4113512 704069611345871699694103 := by
  unfold tailWord_4113512
  simp only [CollatzResearch.WordTrace]
  refine ⟨75016054136728015381643395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100021405515637353842191193 75016054136728015381643395)
  ·
    refine ⟨112524081205092023072465093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75016054136728015381643395 112524081205092023072465093)
    ·
      refine ⟨21098265225954754326087205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112524081205092023072465093 21098265225954754326087205)
      ·
        refine ⟨3955924729866516436141351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21098265225954754326087205 3955924729866516436141351)
        ·
          refine ⟨5933887094799774654212027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955924729866516436141351 5933887094799774654212027)
          ·
            refine ⟨8900830642199661981318041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933887094799774654212027 8900830642199661981318041)
            ·
              refine ⟨6675622981649746485988531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8900830642199661981318041 6675622981649746485988531)
              ·
                refine ⟨10013434472474619728982797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6675622981649746485988531 10013434472474619728982797)
                ·
                  refine ⟨3755037927177982398368549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10013434472474619728982797 3755037927177982398368549)
                  ·
                    refine ⟨704069611345871699694103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755037927177982398368549 704069611345871699694103)
                    ·
                      rfl

theorem cell23_4113512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_4113512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113512 prefixEnd_4113512 := by exact prefixLift 4113512
  have htrace : WordTrace (prefixWord ++ tailWord_4113512) baseStart_4113512 baseEnd_4113512 := by
    simpa [prefixWord, tailWord_4113512, baseEnd_4113512] using wordTrace_append hprefix tailTrace_4113512
  have hstable : (prefixWord ++ tailWord_4113512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113512).length < 2 ^ (prefixWord ++ tailWord_4113512).sum := by decide
  have hdescent : baseEnd_4113512 < baseStart_4113512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113521 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_4113521 : Nat := 118140960795 + 4113521 * 2 ^ 59
def prefixEnd_4113521 : Nat := 4983230072969 + 3 ^ 40 * 4113521 * 2
def baseEnd_4113521 : Nat := 704071151787835187956589

theorem tailTrace_4113521 : CollatzResearch.WordTrace tailWord_4113521 prefixEnd_4113521 704071151787835187956589 := by
  unfold tailWord_4113521
  simp only [CollatzResearch.WordTrace]
  refine ⟨150032436530423425300364417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100021624353615616866909611 150032436530423425300364417)
  ·
    refine ⟨112524327397817568975273313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150032436530423425300364417 112524327397817568975273313)
    ·
      refine ⟨84393245548363176731454985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112524327397817568975273313 84393245548363176731454985)
      ·
        refine ⟨63294934161272382548591239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84393245548363176731454985 63294934161272382548591239)
        ·
          refine ⟨94942401241908573822886859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63294934161272382548591239 94942401241908573822886859)
          ·
            refine ⟨142413601862862860734330289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94942401241908573822886859 142413601862862860734330289)
            ·
              refine ⟨106810201397147145550747717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142413601862862860734330289 106810201397147145550747717)
              ·
                refine ⟨20026912761965089790765197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106810201397147145550747717 20026912761965089790765197)
                ·
                  refine ⟨7510092285736908671536949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20026912761965089790765197 7510092285736908671536949)
                  ·
                    refine ⟨704071151787835187956589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7510092285736908671536949 704071151787835187956589)
                    ·
                      rfl

theorem cell23_4113521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_4113521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113521 prefixEnd_4113521 := by exact prefixLift 4113521
  have htrace : WordTrace (prefixWord ++ tailWord_4113521) baseStart_4113521 baseEnd_4113521 := by
    simpa [prefixWord, tailWord_4113521, baseEnd_4113521] using wordTrace_append hprefix tailTrace_4113521
  have hstable : (prefixWord ++ tailWord_4113521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113521).length < 2 ^ (prefixWord ++ tailWord_4113521).sum := by decide
  have hdescent : baseEnd_4113521 < baseStart_4113521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113528 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 1, 5, 2]
def baseStart_4113528 : Nat := 118140960795 + 4113528 * 2 ^ 59
def prefixEnd_4113528 : Nat := 4983230072969 + 3 ^ 40 * 4113528 * 2
def baseEnd_4113528 : Nat := 2112217049728087036482235

theorem tailTrace_4113528 : CollatzResearch.WordTrace tailWord_4113528 prefixEnd_4113528 2112217049728087036482235 := by
  unfold tailWord_4113528
  simp only [CollatzResearch.WordTrace]
  refine ⟨75016345920699032747934619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100021794560932043663912825 75016345920699032747934619)
  ·
    refine ⟨112524518881048549121901929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75016345920699032747934619 112524518881048549121901929)
    ·
      refine ⟨84393389160786411841426447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112524518881048549121901929 84393389160786411841426447)
      ·
        refine ⟨126590083741179617762139671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84393389160786411841426447 126590083741179617762139671)
        ·
          refine ⟨189885125611769426643209507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126590083741179617762139671 189885125611769426643209507)
          ·
            refine ⟨284827688417654139964814261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189885125611769426643209507 284827688417654139964814261)
            ·
              refine ⟨26702595789155075621701337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284827688417654139964814261 26702595789155075621701337)
              ·
                refine ⟨20026946841866306716276003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26702595789155075621701337 20026946841866306716276003)
                ·
                  refine ⟨30040420262799460074414005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20026946841866306716276003 30040420262799460074414005)
                  ·
                    refine ⟨2816289399637449381976313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30040420262799460074414005 2816289399637449381976313)
                    ·
                      refine ⟨2112217049728087036482235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816289399637449381976313 2112217049728087036482235)
                      ·
                        rfl

theorem cell23_4113528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 5, 2].length) (baseStart_4113528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113528 prefixEnd_4113528 := by exact prefixLift 4113528
  have htrace : WordTrace (prefixWord ++ tailWord_4113528) baseStart_4113528 baseEnd_4113528 := by
    simpa [prefixWord, tailWord_4113528, baseEnd_4113528] using wordTrace_append hprefix tailTrace_4113528
  have hstable : (prefixWord ++ tailWord_4113528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113528).length < 2 ^ (prefixWord ++ tailWord_4113528).sum := by decide
  have hdescent : baseEnd_4113528 < baseStart_4113528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113562 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2]
def baseStart_4113562 : Nat := 118140960795 + 4113562 * 2 ^ 59
def prefixEnd_4113562 : Nat := 4983230072969 + 3 ^ 40 * 4113562 * 2
def baseEnd_4113562 : Nat := 2112234508070339903457079

theorem tailTrace_4113562 : CollatzResearch.WordTrace tailWord_4113562 prefixEnd_4113562 2112234508070339903457079 := by
  unfold tailWord_4113562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37508482980818722325651735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100022621282183259535071293 37508482980818722325651735)
  ·
    refine ⟨56262724471228083488477603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37508482980818722325651735 56262724471228083488477603)
    ·
      refine ⟨84394086706842125232716405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56262724471228083488477603 84394086706842125232716405)
      ·
        refine ⟨7911945628766449240567163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84394086706842125232716405 7911945628766449240567163)
        ·
          refine ⟨11867918443149673860850745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911945628766449240567163 11867918443149673860850745)
          ·
            refine ⟨8900938832362255395638059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11867918443149673860850745 8900938832362255395638059)
            ·
              refine ⟨13351408248543383093457089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900938832362255395638059 13351408248543383093457089)
              ·
                refine ⟨10013556186407537320092817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13351408248543383093457089 10013556186407537320092817)
                ·
                  refine ⟨7510167139805652990069613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013556186407537320092817 7510167139805652990069613)
                  ·
                    refine ⟨2816312677427119871276105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7510167139805652990069613 2816312677427119871276105)
                    ·
                      refine ⟨2112234508070339903457079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816312677427119871276105 2112234508070339903457079)
                      ·
                        rfl

theorem cell23_4113562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_4113562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113562 prefixEnd_4113562 := by exact prefixLift 4113562
  have htrace : WordTrace (prefixWord ++ tailWord_4113562) baseStart_4113562 baseEnd_4113562 := by
    simpa [prefixWord, tailWord_4113562, baseEnd_4113562] using wordTrace_append hprefix tailTrace_4113562
  have hstable : (prefixWord ++ tailWord_4113562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113562).length < 2 ^ (prefixWord ++ tailWord_4113562).sum := by decide
  have hdescent : baseEnd_4113562 < baseStart_4113562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113568 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 4, 4]
def baseStart_4113568 : Nat := 118140960795 + 4113568 * 2 ^ 59
def prefixEnd_4113568 : Nat := 4983230072969 + 3 ^ 40 * 4113568 * 2
def baseEnd_4113568 : Nat := 704079196318088959994017

theorem tailTrace_4113568 : CollatzResearch.WordTrace tailWord_4113568 prefixEnd_4113568 704079196318088959994017 := by
  unfold tailWord_4113568
  simp only [CollatzResearch.WordTrace]
  refine ⟨75017075380626576163662679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100022767174168768218216905 75017075380626576163662679)
  ·
    refine ⟨112525613070939864245494019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75017075380626576163662679 112525613070939864245494019)
    ·
      refine ⟨168788419606409796368241029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112525613070939864245494019 168788419606409796368241029)
      ·
        refine ⟨31647828676201836819045193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168788419606409796368241029 31647828676201836819045193)
        ·
          refine ⟨23735871507151377614283895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31647828676201836819045193 23735871507151377614283895)
          ·
            refine ⟨35603807260727066421425843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23735871507151377614283895 35603807260727066421425843)
            ·
              refine ⟨53405710891090599632138765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35603807260727066421425843 53405710891090599632138765)
              ·
                refine ⟨20027141584158974862052037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53405710891090599632138765 20027141584158974862052037)
                ·
                  refine ⟨3755089047029807786634757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20027141584158974862052037 3755089047029807786634757)
                  ·
                    refine ⟨704079196318088959994017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755089047029807786634757 704079196318088959994017)
                    ·
                      rfl

theorem cell23_4113568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 4].length) (baseStart_4113568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113568 prefixEnd_4113568 := by exact prefixLift 4113568
  have htrace : WordTrace (prefixWord ++ tailWord_4113568) baseStart_4113568 baseEnd_4113568 := by
    simpa [prefixWord, tailWord_4113568, baseEnd_4113568] using wordTrace_append hprefix tailTrace_4113568
  have hstable : (prefixWord ++ tailWord_4113568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113568).length < 2 ^ (prefixWord ++ tailWord_4113568).sum := by decide
  have hdescent : baseEnd_4113568 < baseStart_4113568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113569 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4113569 : Nat := 118140960795 + 4113569 * 2 ^ 59
def prefixEnd_4113569 : Nat := 4983230072969 + 3 ^ 40 * 4113569 * 2
def baseEnd_4113569 : Nat := 2112238102434921376069547

theorem tailTrace_4113569 : CollatzResearch.WordTrace tailWord_4113569 prefixEnd_4113569 2112238102434921376069547 := by
  unfold tailWord_4113569
  simp only [CollatzResearch.WordTrace]
  refine ⟨150034187234249529498111761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100022791489499686332074507 150034187234249529498111761)
  ·
    refine ⟨112525640425687147123583821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150034187234249529498111761 112525640425687147123583821)
    ·
      refine ⟨42197115159632680171343933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112525640425687147123583821 42197115159632680171343933)
      ·
        refine ⟨15823918184862255064253975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42197115159632680171343933 15823918184862255064253975)
        ·
          refine ⟨23735877277293382596380963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15823918184862255064253975 23735877277293382596380963)
          ·
            refine ⟨35603815915940073894571445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23735877277293382596380963 35603815915940073894571445)
            ·
              refine ⟨3337857742119381927616073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35603815915940073894571445 3337857742119381927616073)
              ·
                refine ⟨2503393306589536445712055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337857742119381927616073 2503393306589536445712055)
                ·
                  refine ⟨3755089959884304668568083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503393306589536445712055 3755089959884304668568083)
                  ·
                    refine ⟨5632634939826457002852125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3755089959884304668568083 5632634939826457002852125)
                    ·
                      refine ⟨2112238102434921376069547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632634939826457002852125 2112238102434921376069547)
                      ·
                        rfl

theorem cell23_4113569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4113569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113569 prefixEnd_4113569 := by exact prefixLift 4113569
  have htrace : WordTrace (prefixWord ++ tailWord_4113569) baseStart_4113569 baseEnd_4113569 := by
    simpa [prefixWord, tailWord_4113569, baseEnd_4113569] using wordTrace_append hprefix tailTrace_4113569
  have hstable : (prefixWord ++ tailWord_4113569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113569).length < 2 ^ (prefixWord ++ tailWord_4113569).sum := by decide
  have hdescent : baseEnd_4113569 < baseStart_4113569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113598 : List Nat := [4, 2, 1, 1, 3, 1, 2, 9]
def baseStart_4113598 : Nat := 118140960795 + 4113598 * 2 ^ 59
def prefixEnd_4113598 : Nat := 4983230072969 + 3 ^ 40 * 4113598 * 2
def baseEnd_4113598 : Nat := 78231592347181546763219

theorem tailTrace_4113598 : CollatzResearch.WordTrace tailWord_4113598 prefixEnd_4113598 78231592347181546763219 := by
  unfold tailWord_4113598
  simp only [CollatzResearch.WordTrace]
  refine ⟨18754405618893058431364681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100023496634096311633944965 18754405618893058431364681)
  ·
    refine ⟨14065804214169793823523511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18754405618893058431364681 14065804214169793823523511)
    ·
      refine ⟨21098706321254690735285267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14065804214169793823523511 21098706321254690735285267)
      ·
        refine ⟨31648059481882036102927901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21098706321254690735285267 31648059481882036102927901)
        ·
          refine ⟨11868022305705763538597963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31648059481882036102927901 11868022305705763538597963)
          ·
            refine ⟨17802033458558645307896945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868022305705763538597963 17802033458558645307896945)
            ·
              refine ⟨13351525093918983980922709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17802033458558645307896945 13351525093918983980922709)
              ·
                refine ⟨78231592347181546763219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13351525093918983980922709 78231592347181546763219)
                ·
                  rfl

theorem cell23_4113598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_4113598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113598 prefixEnd_4113598 := by exact prefixLift 4113598
  have htrace : WordTrace (prefixWord ++ tailWord_4113598) baseStart_4113598 baseEnd_4113598 := by
    simpa [prefixWord, tailWord_4113598, baseEnd_4113598] using wordTrace_append hprefix tailTrace_4113598
  have hstable : (prefixWord ++ tailWord_4113598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113598).length < 2 ^ (prefixWord ++ tailWord_4113598).sum := by decide
  have hdescent : baseEnd_4113598 < baseStart_4113598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113608 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 3, 3, 3]
def baseStart_4113608 : Nat := 118140960795 + 4113608 * 2 ^ 59
def prefixEnd_4113608 : Nat := 4983230072969 + 3 ^ 40 * 4113608 * 2
def baseEnd_4113608 : Nat := 2112258128180446723481867

theorem tailTrace_4113608 : CollatzResearch.WordTrace tailWord_4113608 prefixEnd_4113608 2112258128180446723481867 := by
  unfold tailWord_4113608
  simp only [CollatzResearch.WordTrace]
  refine ⟨75017804840554119579390739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100023739787405492772520985 75017804840554119579390739)
  ·
    refine ⟨112526707260831179369086109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75017804840554119579390739 112526707260831179369086109)
    ·
      refine ⟨42197515222811692263407291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112526707260831179369086109 42197515222811692263407291)
      ·
        refine ⟨63296272834217538395110937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42197515222811692263407291 63296272834217538395110937)
        ·
          refine ⟨47472204625663153796333203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63296272834217538395110937 47472204625663153796333203)
          ·
            refine ⟨71208306938494730694499805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47472204625663153796333203 71208306938494730694499805)
            ·
              refine ⟨26703115101935524010437427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71208306938494730694499805 26703115101935524010437427)
              ·
                refine ⟨40054672652903286015656141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26703115101935524010437427 40054672652903286015656141)
                ·
                  refine ⟨15020502244838732255871053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40054672652903286015656141 15020502244838732255871053)
                  ·
                    refine ⟨5632688341814524595951645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15020502244838732255871053 5632688341814524595951645)
                    ·
                      refine ⟨2112258128180446723481867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632688341814524595951645 2112258128180446723481867)
                      ·
                        rfl

theorem cell23_4113608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_4113608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113608 prefixEnd_4113608 := by exact prefixLift 4113608
  have htrace : WordTrace (prefixWord ++ tailWord_4113608) baseStart_4113608 baseEnd_4113608 := by
    simpa [prefixWord, tailWord_4113608, baseEnd_4113608] using wordTrace_append hprefix tailTrace_4113608
  have hstable : (prefixWord ++ tailWord_4113608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113608).length < 2 ^ (prefixWord ++ tailWord_4113608).sum := by decide
  have hdescent : baseEnd_4113608 < baseStart_4113608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113620 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4113620 : Nat := 118140960795 + 4113620 * 2 ^ 59
def prefixEnd_4113620 : Nat := 4983230072969 + 3 ^ 40 * 4113620 * 2
def baseEnd_4113620 : Nat := 2112264289948300676531813

theorem tailTrace_4113620 : CollatzResearch.WordTrace tailWord_4113620 prefixEnd_4113620 2112264289948300676531813 := by
  unfold tailWord_4113620
  simp only [CollatzResearch.WordTrace]
  refine ⟨75018023678532382604109157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100024031571376510138812209 75018023678532382604109157)
  ·
    refine ⟨14065879439724821738270467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75018023678532382604109157 14065879439724821738270467)
    ·
      refine ⟨21098819159587232607405701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14065879439724821738270467 21098819159587232607405701)
      ·
        refine ⟨3956028592422606113888569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21098819159587232607405701 3956028592422606113888569)
        ·
          refine ⟨2967021444316954585416427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3956028592422606113888569 2967021444316954585416427)
          ·
            refine ⟨4450532166475431878124641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967021444316954585416427 4450532166475431878124641)
            ·
              refine ⟨3337899124856573908593481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450532166475431878124641 3337899124856573908593481)
              ·
                refine ⟨2503424343642430431445111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337899124856573908593481 2503424343642430431445111)
                ·
                  refine ⟨3755136515463645647167667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503424343642430431445111 3755136515463645647167667)
                  ·
                    refine ⟨5632704773195468470751501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3755136515463645647167667 5632704773195468470751501)
                    ·
                      refine ⟨2112264289948300676531813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632704773195468470751501 2112264289948300676531813)
                      ·
                        rfl

theorem cell23_4113620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4113620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113620 prefixEnd_4113620 := by exact prefixLift 4113620
  have htrace : WordTrace (prefixWord ++ tailWord_4113620) baseStart_4113620 baseEnd_4113620 := by
    simpa [prefixWord, tailWord_4113620, baseEnd_4113620] using wordTrace_append hprefix tailTrace_4113620
  have hstable : (prefixWord ++ tailWord_4113620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113620).length < 2 ^ (prefixWord ++ tailWord_4113620).sum := by decide
  have hdescent : baseEnd_4113620 < baseStart_4113620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113642 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_4113642 : Nat := 118140960795 + 4113642 * 2 ^ 59
def prefixEnd_4113642 : Nat := 4983230072969 + 3 ^ 40 * 4113642 * 2
def baseEnd_4113642 : Nat := 2112275586522699590456711

theorem tailTrace_4113642 : CollatzResearch.WordTrace tailWord_4113642 prefixEnd_4113642 2112275586522699590456711 := by
  unfold tailWord_4113642
  simp only [CollatzResearch.WordTrace]
  refine ⟨37509212440746265741379795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100024566508656708643679453 37509212440746265741379795)
  ·
    refine ⟨56263818661119398612069693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37509212440746265741379795 56263818661119398612069693)
    ·
      refine ⟨21098931997919774479526135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56263818661119398612069693 21098931997919774479526135)
      ·
        refine ⟨31648397996879661719289203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21098931997919774479526135 31648397996879661719289203)
        ·
          refine ⟨47472596995319492578933805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31648397996879661719289203 47472596995319492578933805)
          ·
            refine ⟨17802223873244809717100177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47472596995319492578933805 17802223873244809717100177)
            ·
              refine ⟨13351667904933607287825133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17802223873244809717100177 13351667904933607287825133)
              ·
                refine ⟨5006875464350102732934425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13351667904933607287825133 5006875464350102732934425)
                ·
                  refine ⟨3755156598262577049700819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5006875464350102732934425 3755156598262577049700819)
                  ·
                    refine ⟨5632734897393865574551229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3755156598262577049700819 5632734897393865574551229)
                    ·
                      refine ⟨2112275586522699590456711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5632734897393865574551229 2112275586522699590456711)
                      ·
                        rfl

theorem cell23_4113642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_4113642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113642 prefixEnd_4113642 := by exact prefixLift 4113642
  have htrace : WordTrace (prefixWord ++ tailWord_4113642) baseStart_4113642 baseEnd_4113642 := by
    simpa [prefixWord, tailWord_4113642, baseEnd_4113642] using wordTrace_append hprefix tailTrace_4113642
  have hstable : (prefixWord ++ tailWord_4113642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113642).length < 2 ^ (prefixWord ++ tailWord_4113642).sum := by decide
  have hdescent : baseEnd_4113642 < baseStart_4113642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113688 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 7]
def baseStart_4113688 : Nat := 118140960795 + 4113688 * 2 ^ 59
def prefixEnd_4113688 : Nat := 4983230072969 + 3 ^ 40 * 4113688 * 2
def baseEnd_4113688 : Nat := 234699911848089601164611

theorem tailTrace_4113688 : CollatzResearch.WordTrace tailWord_4113688 prefixEnd_4113688 234699911848089601164611 := by
  unfold tailWord_4113688
  simp only [CollatzResearch.WordTrace]
  refine ⟨75019263760409206410846859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100025685013878941881129145 75019263760409206410846859)
  ·
    refine ⟨112528895640613809616270289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75019263760409206410846859 112528895640613809616270289)
    ·
      refine ⟨84396671730460357212202717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112528895640613809616270289 84396671730460357212202717)
      ·
        refine ⟨31648751898922633954576019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84396671730460357212202717 31648751898922633954576019)
        ·
          refine ⟨47473127848383950931864029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31648751898922633954576019 47473127848383950931864029)
          ·
            refine ⟨17802422943143981599449011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47473127848383950931864029 17802422943143981599449011)
            ·
              refine ⟨26703634414715972399173517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17802422943143981599449011 26703634414715972399173517)
              ·
                refine ⟨10013862905518489649690069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26703634414715972399173517 10013862905518489649690069)
                ·
                  refine ⟨234699911848089601164611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10013862905518489649690069 234699911848089601164611)
                  ·
                    rfl

theorem cell23_4113688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 7].length) (baseStart_4113688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113688 prefixEnd_4113688 := by exact prefixLift 4113688
  have htrace : WordTrace (prefixWord ++ tailWord_4113688) baseStart_4113688 baseEnd_4113688 := by
    simpa [prefixWord, tailWord_4113688, baseEnd_4113688] using wordTrace_append hprefix tailTrace_4113688
  have hstable : (prefixWord ++ tailWord_4113688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113688).length < 2 ^ (prefixWord ++ tailWord_4113688).sum := by decide
  have hdescent : baseEnd_4113688 < baseStart_4113688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113728 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_4113728 : Nat := 118140960795 + 4113728 * 2 ^ 59
def prefixEnd_4113728 : Nat := 4983230072969 + 3 ^ 40 * 4113728 * 2
def baseEnd_4113728 : Nat := 2112319745858986253981315

theorem tailTrace_4113728 : CollatzResearch.WordTrace tailWord_4113728 prefixEnd_4113728 2112319745858986253981315 := by
  unfold tailWord_4113728
  simp only [CollatzResearch.WordTrace]
  refine ⟨75019993220336749826574919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100026657627115666435433225 75019993220336749826574919)
  ·
    refine ⟨112529989830505124739862379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75019993220336749826574919 112529989830505124739862379)
    ·
      refine ⟨168794984745757687109793569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112529989830505124739862379 168794984745757687109793569)
      ·
        refine ⟨126596238559318265332345177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168794984745757687109793569 126596238559318265332345177)
        ·
          refine ⟨94947178919488698999258883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126596238559318265332345177 94947178919488698999258883)
          ·
            refine ⟨142420768379233048498888325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94947178919488698999258883 142420768379233048498888325)
            ·
              refine ⟨26703894071106196593541561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142420768379233048498888325 26703894071106196593541561)
              ·
                refine ⟨20027920553329647445156171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26703894071106196593541561 20027920553329647445156171)
                ·
                  refine ⟨30041880829994471167734257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20027920553329647445156171 30041880829994471167734257)
                  ·
                    refine ⟨22531410622495853375800693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30041880829994471167734257 22531410622495853375800693)
                    ·
                      refine ⟨2112319745858986253981315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22531410622495853375800693 2112319745858986253981315)
                      ·
                        rfl

theorem cell23_4113728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_4113728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113728 prefixEnd_4113728 := by exact prefixLift 4113728
  have htrace : WordTrace (prefixWord ++ tailWord_4113728) baseStart_4113728 baseEnd_4113728 := by
    simpa [prefixWord, tailWord_4113728, baseEnd_4113728] using wordTrace_append hprefix tailTrace_4113728
  have hstable : (prefixWord ++ tailWord_4113728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113728).length < 2 ^ (prefixWord ++ tailWord_4113728).sum := by decide
  have hdescent : baseEnd_4113728 < baseStart_4113728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113735 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 2, 5]
def baseStart_4113735 : Nat := 118140960795 + 4113735 * 2 ^ 59
def prefixEnd_4113735 : Nat := 4983230072969 + 3 ^ 40 * 4113735 * 2
def baseEnd_4113735 : Nat := 704107780074522575531261

theorem tailTrace_4113735 : CollatzResearch.WordTrace tailWord_4113735 prefixEnd_4113735 704107780074522575531261 := by
  unfold tailWord_4113735
  simp only [CollatzResearch.WordTrace]
  refine ⟨150040241751648139848654659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100026827834432093232436439 150040241751648139848654659)
  ·
    refine ⟨225060362627472209772981989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150040241751648139848654659 225060362627472209772981989)
    ·
      refine ⟨42198817992651039332434123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225060362627472209772981989 42198817992651039332434123)
      ·
        refine ⟨63298226988976558998651185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42198817992651039332434123 63298226988976558998651185)
        ·
          refine ⟨47473670241732419248988389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63298226988976558998651185 47473670241732419248988389)
          ·
            refine ⟨8901313170324828609185323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47473670241732419248988389 8901313170324828609185323)
            ·
              refine ⟨13351969755487242913777985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901313170324828609185323 13351969755487242913777985)
              ·
                refine ⟨10013977316615432185333489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13351969755487242913777985 10013977316615432185333489)
                ·
                  refine ⟨7510482987461574139000117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10013977316615432185333489 7510482987461574139000117)
                  ·
                    refine ⟨704107780074522575531261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7510482987461574139000117 704107780074522575531261)
                    ·
                      rfl

theorem cell23_4113735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_4113735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113735 prefixEnd_4113735 := by exact prefixLift 4113735
  have htrace : WordTrace (prefixWord ++ tailWord_4113735) baseStart_4113735 baseEnd_4113735 := by
    simpa [prefixWord, tailWord_4113735, baseEnd_4113735] using wordTrace_append hprefix tailTrace_4113735
  have hstable : (prefixWord ++ tailWord_4113735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113735).length < 2 ^ (prefixWord ++ tailWord_4113735).sum := by decide
  have hdescent : baseEnd_4113735 < baseStart_4113735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113765 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_4113765 : Nat := 118140960795 + 4113765 * 2 ^ 59
def prefixEnd_4113765 : Nat := 4983230072969 + 3 ^ 40 * 4113765 * 2
def baseEnd_4113765 : Nat := 704112914881067536406215

theorem tailTrace_4113765 : CollatzResearch.WordTrace tailWord_4113765 prefixEnd_4113765 704112914881067536406215 := by
  unfold tailWord_4113765
  simp only [CollatzResearch.WordTrace]
  refine ⟨150041335941539454972246749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100027557294359636648164499 150041335941539454972246749)
  ·
    refine ⟨56265500978077295614592531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150041335941539454972246749 56265500978077295614592531)
    ·
      refine ⟨84398251467115943421888797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56265500978077295614592531 84398251467115943421888797)
      ·
        refine ⟨31649344300168478783208299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84398251467115943421888797 31649344300168478783208299)
        ·
          refine ⟨47474016450252718174812449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31649344300168478783208299 47474016450252718174812449)
          ·
            refine ⟨35605512337689538631109337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47474016450252718174812449 35605512337689538631109337)
            ·
              refine ⟨26704134253267153973332003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35605512337689538631109337 26704134253267153973332003)
              ·
                refine ⟨40056201379900730959998005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26704134253267153973332003 40056201379900730959998005)
                ·
                  refine ⟨3755268879365693527499813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40056201379900730959998005 3755268879365693527499813)
                  ·
                    refine ⟨704112914881067536406215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755268879365693527499813 704112914881067536406215)
                    ·
                      rfl

theorem cell23_4113765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_4113765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113765 prefixEnd_4113765 := by exact prefixLift 4113765
  have htrace : WordTrace (prefixWord ++ tailWord_4113765) baseStart_4113765 baseEnd_4113765 := by
    simpa [prefixWord, tailWord_4113765, baseEnd_4113765] using wordTrace_append hprefix tailTrace_4113765
  have hstable : (prefixWord ++ tailWord_4113765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113765).length < 2 ^ (prefixWord ++ tailWord_4113765).sum := by decide
  have hdescent : baseEnd_4113765 < baseStart_4113765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113772 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_4113772 : Nat := 118140960795 + 4113772 * 2 ^ 59
def prefixEnd_4113772 : Nat := 4983230072969 + 3 ^ 40 * 4113772 * 2
def baseEnd_4113772 : Nat := 2112342339007784081831113

theorem tailTrace_4113772 : CollatzResearch.WordTrace tailWord_4113772 prefixEnd_4113772 2112342339007784081831113 := by
  unfold tailWord_4113772
  simp only [CollatzResearch.WordTrace]
  refine ⟨75020795626257047583875785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100027727501676063445167713 75020795626257047583875785)
  ·
    refine ⟨56265596719692785687906839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75020795626257047583875785 56265596719692785687906839)
    ·
      refine ⟨84398395079539178531860259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56265596719692785687906839 84398395079539178531860259)
      ·
        refine ⟨126597592619308767797790389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84398395079539178531860259 126597592619308767797790389)
        ·
          refine ⟨11868524308060196981042849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126597592619308767797790389 11868524308060196981042849)
          ·
            refine ⟨8901393231045147735782137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11868524308060196981042849 8901393231045147735782137)
            ·
              refine ⟨6676044923283860801836603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8901393231045147735782137 6676044923283860801836603)
              ·
                refine ⟨10014067384925791202754905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676044923283860801836603 10014067384925791202754905)
                ·
                  refine ⟨7510550538694343402066179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10014067384925791202754905 7510550538694343402066179)
                  ·
                    refine ⟨11265825808041515103099269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7510550538694343402066179 11265825808041515103099269)
                    ·
                      refine ⟨2112342339007784081831113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11265825808041515103099269 2112342339007784081831113)
                      ·
                        rfl

theorem cell23_4113772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_4113772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113772 prefixEnd_4113772 := by exact prefixLift 4113772
  have htrace : WordTrace (prefixWord ++ tailWord_4113772) baseStart_4113772 baseEnd_4113772 := by
    simpa [prefixWord, tailWord_4113772, baseEnd_4113772] using wordTrace_append hprefix tailTrace_4113772
  have hstable : (prefixWord ++ tailWord_4113772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113772).length < 2 ^ (prefixWord ++ tailWord_4113772).sum := by decide
  have hdescent : baseEnd_4113772 < baseStart_4113772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113790 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_4113790 : Nat := 118140960795 + 4113790 * 2 ^ 59
def prefixEnd_4113790 : Nat := 4983230072969 + 3 ^ 40 * 4113790 * 2
def baseEnd_4113790 : Nat := 234705731295507223489559

theorem tailTrace_4113790 : CollatzResearch.WordTrace tailWord_4113790 prefixEnd_4113790 234705731295507223489559 := by
  unfold tailWord_4113790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755280970806110530238353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100028165177632589494604549 18755280970806110530238353)
  ·
    refine ⟨14066460728104582897678765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18755280970806110530238353 14066460728104582897678765)
    ·
      refine ⟨5274922773039218586629537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14066460728104582897678765 5274922773039218586629537)
      ·
        refine ⟨3956192079779413939972153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5274922773039218586629537 3956192079779413939972153)
        ·
          refine ⟨2967144059834560454979115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3956192079779413939972153 2967144059834560454979115)
          ·
            refine ⟨4450716089751840682468673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967144059834560454979115 4450716089751840682468673)
            ·
              refine ⟨3338037067313880511851505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4450716089751840682468673 3338037067313880511851505)
              ·
                refine ⟨2503527800485410383888629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338037067313880511851505 2503527800485410383888629)
                ·
                  refine ⟨234705731295507223489559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2503527800485410383888629 234705731295507223489559)
                  ·
                    rfl

theorem cell23_4113790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_4113790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113790 prefixEnd_4113790 := by exact prefixLift 4113790
  have htrace : WordTrace (prefixWord ++ tailWord_4113790) baseStart_4113790 baseEnd_4113790 := by
    simpa [prefixWord, tailWord_4113790, baseEnd_4113790] using wordTrace_append hprefix tailTrace_4113790
  have hstable : (prefixWord ++ tailWord_4113790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113790).length < 2 ^ (prefixWord ++ tailWord_4113790).sum := by decide
  have hdescent : baseEnd_4113790 < baseStart_4113790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113795 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 6]
def baseStart_4113795 : Nat := 118140960795 + 4113795 * 2 ^ 59
def prefixEnd_4113795 : Nat := 4983230072969 + 3 ^ 40 * 4113795 * 2
def baseEnd_4113795 : Nat := 234706016562537499093723

theorem tailTrace_4113795 : CollatzResearch.WordTrace tailWord_4113795 prefixEnd_4113795 234706016562537499093723 := by
  unfold tailWord_4113795
  simp only [CollatzResearch.WordTrace]
  refine ⟨150042430131430770095838839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100028286754287180063892559 150042430131430770095838839)
  ·
    refine ⟨225063645197146155143758259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150042430131430770095838839 225063645197146155143758259)
    ·
      refine ⟨337595467795719232715637389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225063645197146155143758259 337595467795719232715637389)
      ·
        refine ⟨126598300423394712268364021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337595467795719232715637389 126598300423394712268364021)
        ·
          refine ⟨11868590664693254275159127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126598300423394712268364021 11868590664693254275159127)
          ·
            refine ⟨17802885997039881412738691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868590664693254275159127 17802885997039881412738691)
            ·
              refine ⟨26704328995559822119108037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17802885997039881412738691 26704328995559822119108037)
              ·
                refine ⟨5007061686667466647332757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26704328995559822119108037 5007061686667466647332757)
                ·
                  refine ⟨234706016562537499093723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5007061686667466647332757 234706016562537499093723)
                  ·
                    rfl

theorem cell23_4113795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 6].length) (baseStart_4113795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113795 prefixEnd_4113795 := by exact prefixLift 4113795
  have htrace : WordTrace (prefixWord ++ tailWord_4113795) baseStart_4113795 baseEnd_4113795 := by
    simpa [prefixWord, tailWord_4113795, baseEnd_4113795] using wordTrace_append hprefix tailTrace_4113795
  have hstable : (prefixWord ++ tailWord_4113795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113795).length < 2 ^ (prefixWord ++ tailWord_4113795).sum := by decide
  have hdescent : baseEnd_4113795 < baseStart_4113795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113799 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 1, 4]
def baseStart_4113799 : Nat := 118140960795 + 4113799 * 2 ^ 59
def prefixEnd_4113799 : Nat := 4983230072969 + 3 ^ 40 * 4113799 * 2
def baseEnd_4113799 : Nat := 704118734328485158731163

theorem tailTrace_4113799 : CollatzResearch.WordTrace tailWord_4113799 prefixEnd_4113799 704118734328485158731163 := by
  unfold tailWord_4113799
  simp only [CollatzResearch.WordTrace]
  refine ⟨150042576023416278778984451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100028384015610852519322967 150042576023416278778984451)
  ·
    refine ⟨225063864035124418168476677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150042576023416278778984451 225063864035124418168476677)
    ·
      refine ⟨42199474506585828406589377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 225063864035124418168476677 42199474506585828406589377)
      ·
        refine ⟨31649605879939371304942033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42199474506585828406589377 31649605879939371304942033)
        ·
          refine ⟨23737204409954528478706525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31649605879939371304942033 23737204409954528478706525)
          ·
            refine ⟨8901451653732948179514947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23737204409954528478706525 8901451653732948179514947)
            ·
              refine ⟨13352177480599422269272421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901451653732948179514947 13352177480599422269272421)
              ·
                refine ⟨2503533277612391675488579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13352177480599422269272421 2503533277612391675488579)
                ·
                  refine ⟨3755299916418587513232869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503533277612391675488579 3755299916418587513232869)
                  ·
                    refine ⟨704118734328485158731163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3755299916418587513232869 704118734328485158731163)
                    ·
                      rfl

theorem cell23_4113799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_4113799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113799 prefixEnd_4113799 := by exact prefixLift 4113799
  have htrace : WordTrace (prefixWord ++ tailWord_4113799) baseStart_4113799 baseEnd_4113799 := by
    simpa [prefixWord, tailWord_4113799, baseEnd_4113799] using wordTrace_append hprefix tailTrace_4113799
  have hstable : (prefixWord ++ tailWord_4113799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113799).length < 2 ^ (prefixWord ++ tailWord_4113799).sum := by decide
  have hdescent : baseEnd_4113799 < baseStart_4113799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113812 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 6]
def baseStart_4113812 : Nat := 118140960795 + 4113812 * 2 ^ 59
def prefixEnd_4113812 : Nat := 4983230072969 + 3 ^ 40 * 4113812 * 2
def baseEnd_4113812 : Nat := 234706986470440436147881

theorem tailTrace_4113812 : CollatzResearch.WordTrace tailWord_4113812 prefixEnd_4113812 234706986470440436147881 := by
  unfold tailWord_4113812
  simp only [CollatzResearch.WordTrace]
  refine ⟨75021525086184590999603845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100028700114912787999471793 75021525086184590999603845)
  ·
    refine ⟨14066535953659610812425721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75021525086184590999603845 14066535953659610812425721)
    ·
      refine ⟨10549901965244708109319291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14066535953659610812425721 10549901965244708109319291)
      ·
        refine ⟨15824852947867062163978937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10549901965244708109319291 15824852947867062163978937)
        ·
          refine ⟨11868639710900296622984203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15824852947867062163978937 11868639710900296622984203)
          ·
            refine ⟨17802959566350444934476305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11868639710900296622984203 17802959566350444934476305)
            ·
              refine ⟨13352219674762833700857229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17802959566350444934476305 13352219674762833700857229)
              ·
                refine ⟨5007082378036062637821461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13352219674762833700857229 5007082378036062637821461)
                ·
                  refine ⟨234706986470440436147881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5007082378036062637821461 234706986470440436147881)
                  ·
                    rfl

theorem cell23_4113812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_4113812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113812 prefixEnd_4113812 := by exact prefixLift 4113812
  have htrace : WordTrace (prefixWord ++ tailWord_4113812) baseStart_4113812 baseEnd_4113812 := by
    simpa [prefixWord, tailWord_4113812, baseEnd_4113812] using wordTrace_append hprefix tailTrace_4113812
  have hstable : (prefixWord ++ tailWord_4113812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113812).length < 2 ^ (prefixWord ++ tailWord_4113812).sum := by decide
  have hdescent : baseEnd_4113812 < baseStart_4113812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113929 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 3]
def baseStart_4113929 : Nat := 118140960795 + 4113929 * 2 ^ 59
def prefixEnd_4113929 : Nat := 4983230072969 + 3 ^ 40 * 4113929 * 2
def baseEnd_4113929 : Nat := 2112422955470539967567891

theorem tailTrace_4113929 : CollatzResearch.WordTrace tailWord_4113929 prefixEnd_4113929 2112422955470539967567891 := by
  unfold tailWord_4113929
  simp only [CollatzResearch.WordTrace]
  refine ⟨150047317512945310981216841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100031545008630207320811227 150047317512945310981216841)
  ·
    refine ⟨112535488134708983235912631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150047317512945310981216841 112535488134708983235912631)
    ·
      refine ⟨168803232202063474853868947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112535488134708983235912631 168803232202063474853868947)
      ·
        refine ⟨253204848303095212280803421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168803232202063474853868947 253204848303095212280803421)
        ·
          refine ⟨94951818113660704605301283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253204848303095212280803421 94951818113660704605301283)
          ·
            refine ⟨142427727170491056907951925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94951818113660704605301283 142427727170491056907951925)
            ·
              refine ⟨13352599422233536585120493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142427727170491056907951925 13352599422233536585120493)
              ·
                refine ⟨5007224783337576219420185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13352599422233536585120493 5007224783337576219420185)
                ·
                  refine ⟨3755418587503182164565139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5007224783337576219420185 3755418587503182164565139)
                  ·
                    refine ⟨5633127881254773246847709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3755418587503182164565139 5633127881254773246847709)
                    ·
                      refine ⟨2112422955470539967567891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5633127881254773246847709 2112422955470539967567891)
                      ·
                        rfl

theorem cell23_4113929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_4113929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113929 prefixEnd_4113929 := by exact prefixLift 4113929
  have htrace : WordTrace (prefixWord ++ tailWord_4113929) baseStart_4113929 baseEnd_4113929 := by
    simpa [prefixWord, tailWord_4113929, baseEnd_4113929] using wordTrace_append hprefix tailTrace_4113929
  have hstable : (prefixWord ++ tailWord_4113929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113929).length < 2 ^ (prefixWord ++ tailWord_4113929).sum := by decide
  have hdescent : baseEnd_4113929 < baseStart_4113929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113933 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4113933 : Nat := 118140960795 + 4113933 * 2 ^ 59
def prefixEnd_4113933 : Nat := 4983230072969 + 3 ^ 40 * 4113933 * 2
def baseEnd_4113933 : Nat := 2112425009393157951917873

theorem tailTrace_4113933 : CollatzResearch.WordTrace tailWord_4113933 prefixEnd_4113933 2112425009393157951917873 := by
  unfold tailWord_4113933
  simp only [CollatzResearch.WordTrace]
  refine ⟨150047463404930819664362453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100031642269953879776241635 150047463404930819664362453)
  ·
    refine ⟨3516737423553066085883495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 150047463404930819664362453 3516737423553066085883495)
    ·
      refine ⟨5275106135329599128825243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516737423553066085883495 5275106135329599128825243)
      ·
        refine ⟨7912659202994398693237865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275106135329599128825243 7912659202994398693237865)
        ·
          refine ⟨5934494402245799019928399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7912659202994398693237865 5934494402245799019928399)
          ·
            refine ⟨8901741603368698529892599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934494402245799019928399 8901741603368698529892599)
            ·
              refine ⟨13352612405053047794838899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901741603368698529892599 13352612405053047794838899)
              ·
                refine ⟨20028918607579571692258349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13352612405053047794838899 20028918607579571692258349)
                ·
                  refine ⟨7510844477842339384596881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20028918607579571692258349 7510844477842339384596881)
                  ·
                    refine ⟨5633133358381754538447661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7510844477842339384596881 5633133358381754538447661)
                    ·
                      refine ⟨2112425009393157951917873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5633133358381754538447661 2112425009393157951917873)
                      ·
                        rfl

theorem cell23_4113933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4113933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113933 prefixEnd_4113933 := by exact prefixLift 4113933
  have htrace : WordTrace (prefixWord ++ tailWord_4113933) baseStart_4113933 baseEnd_4113933 := by
    simpa [prefixWord, tailWord_4113933, baseEnd_4113933] using wordTrace_append hprefix tailTrace_4113933
  have hstable : (prefixWord ++ tailWord_4113933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113933).length < 2 ^ (prefixWord ++ tailWord_4113933).sum := by decide
  have hdescent : baseEnd_4113933 < baseStart_4113933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113939 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 3, 3, 2]
def baseStart_4113939 : Nat := 118140960795 + 4113939 * 2 ^ 59
def prefixEnd_4113939 : Nat := 4983230072969 + 3 ^ 40 * 4113939 * 2
def baseEnd_4113939 : Nat := 2112428090277084928442845

theorem tailTrace_4113939 : CollatzResearch.WordTrace tailWord_4113939 prefixEnd_4113939 2112428090277084928442845 := by
  unfold tailWord_4113939
  simp only [CollatzResearch.WordTrace]
  refine ⟨150047682242909082689080871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100031788161939388459387247 150047682242909082689080871)
  ·
    refine ⟨225071523364363624033621307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150047682242909082689080871 225071523364363624033621307)
    ·
      refine ⟨337607285046545436050431961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225071523364363624033621307 337607285046545436050431961)
      ·
        refine ⟨253205463784909077037823971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337607285046545436050431961 253205463784909077037823971)
        ·
          refine ⟨379808195677363615556735957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253205463784909077037823971 379808195677363615556735957)
          ·
            refine ⟨8901754586188209739610999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 379808195677363615556735957 8901754586188209739610999)
            ·
              refine ⟨13352631879282314609416499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901754586188209739610999 13352631879282314609416499)
              ·
                refine ⟨20028947818923471914124749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13352631879282314609416499 20028947818923471914124749)
                ·
                  refine ⟨7510855432096301967796781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20028947818923471914124749 7510855432096301967796781)
                  ·
                    refine ⟨2816570787036113237923793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7510855432096301967796781 2816570787036113237923793)
                    ·
                      refine ⟨2112428090277084928442845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816570787036113237923793 2112428090277084928442845)
                      ·
                        rfl

theorem cell23_4113939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3, 2].length) (baseStart_4113939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113939 prefixEnd_4113939 := by exact prefixLift 4113939
  have htrace : WordTrace (prefixWord ++ tailWord_4113939) baseStart_4113939 baseEnd_4113939 := by
    simpa [prefixWord, tailWord_4113939, baseEnd_4113939] using wordTrace_append hprefix tailTrace_4113939
  have hstable : (prefixWord ++ tailWord_4113939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113939).length < 2 ^ (prefixWord ++ tailWord_4113939).sum := by decide
  have hdescent : baseEnd_4113939 < baseStart_4113939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113950 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4113950 : Nat := 118140960795 + 4113950 * 2 ^ 59
def prefixEnd_4113950 : Nat := 4983230072969 + 3 ^ 40 * 4113950 * 2
def baseEnd_4113950 : Nat := 2112433738564284385405295

theorem tailTrace_4113950 : CollatzResearch.WordTrace tailWord_4113950 prefixEnd_4113950 2112433738564284385405295 := by
  unfold tailWord_4113950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18756010430733653945966413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100032055630579487711820869 18756010430733653945966413)
  ·
    refine ⟨7033503911525120229737405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18756010430733653945966413 7033503911525120229737405)
    ·
      refine ⟨2637563966821920086151527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7033503911525120229737405 2637563966821920086151527)
      ·
        refine ⟨3956345950232880129227291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2637563966821920086151527 3956345950232880129227291)
        ·
          refine ⟨5934518925349320193840937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3956345950232880129227291 5934518925349320193840937)
          ·
            refine ⟨4450889194011990145380703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5934518925349320193840937 4450889194011990145380703)
            ·
              refine ⟨6676333791017985218071055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4450889194011990145380703 6676333791017985218071055)
              ·
                refine ⟨10014500686526977827106583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676333791017985218071055 10014500686526977827106583)
                ·
                  refine ⟨15021751029790466740659875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10014500686526977827106583 15021751029790466740659875)
                  ·
                    refine ⟨22532626544685700110989813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15021751029790466740659875 22532626544685700110989813)
                    ·
                      refine ⟨2112433738564284385405295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22532626544685700110989813 2112433738564284385405295)
                      ·
                        rfl

theorem cell23_4113950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4113950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113950 prefixEnd_4113950 := by exact prefixLift 4113950
  have htrace : WordTrace (prefixWord ++ tailWord_4113950) baseStart_4113950 baseEnd_4113950 := by
    simpa [prefixWord, tailWord_4113950, baseEnd_4113950] using wordTrace_append hprefix tailTrace_4113950
  have hstable : (prefixWord ++ tailWord_4113950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113950).length < 2 ^ (prefixWord ++ tailWord_4113950).sum := by decide
  have hdescent : baseEnd_4113950 < baseStart_4113950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4113962 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4113962 : Nat := 118140960795 + 4113962 * 2 ^ 59
def prefixEnd_4113962 : Nat := 4983230072969 + 3 ^ 40 * 4113962 * 2
def baseEnd_4113962 : Nat := 704146633444046112818413

theorem tailTrace_4113962 : CollatzResearch.WordTrace tailWord_4113962 prefixEnd_4113962 704146633444046112818413 := by
  unfold tailWord_4113962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37512130280456439404292035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100032347414550505078112093 37512130280456439404292035)
  ·
    refine ⟨56268195420684659106438053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37512130280456439404292035 56268195420684659106438053)
    ·
      refine ⟨10550286641378373582457135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56268195420684659106438053 10550286641378373582457135)
      ·
        refine ⟨15825429962067560373685703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10550286641378373582457135 15825429962067560373685703)
        ·
          refine ⟨23738144943101340560528555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15825429962067560373685703 23738144943101340560528555)
          ·
            refine ⟨35607217414652010840792833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23738144943101340560528555 35607217414652010840792833)
            ·
              refine ⟨26705413060989008130594625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35607217414652010840792833 26705413060989008130594625)
              ·
                refine ⟨20029059795741756097945969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26705413060989008130594625 20029059795741756097945969)
                ·
                  refine ⟨15021794846806317073459477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20029059795741756097945969 15021794846806317073459477)
                  ·
                    refine ⟨704146633444046112818413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15021794846806317073459477 704146633444046112818413)
                    ·
                      rfl

theorem cell23_4113962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4113962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4113962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4113962 prefixEnd_4113962 := by exact prefixLift 4113962
  have htrace : WordTrace (prefixWord ++ tailWord_4113962) baseStart_4113962 baseEnd_4113962 := by
    simpa [prefixWord, tailWord_4113962, baseEnd_4113962] using wordTrace_append hprefix tailTrace_4113962
  have hstable : (prefixWord ++ tailWord_4113962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4113962).length < 2 ^ (prefixWord ++ tailWord_4113962).sum := by decide
  have hdescent : baseEnd_4113962 < baseStart_4113962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4113962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114042 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_4114042 : Nat := 118140960795 + 4114042 * 2 ^ 59
def prefixEnd_4114042 : Nat := 4983230072969 + 3 ^ 40 * 4114042 * 2
def baseEnd_4114042 : Nat := 2112480978784498025454871

theorem tailTrace_4114042 : CollatzResearch.WordTrace tailWord_4114042 prefixEnd_4114042 2112480978784498025454871 := by
  unfold tailWord_4114042
  simp only [CollatzResearch.WordTrace]
  refine ⟨37512859740383982820020095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100034292641023954186720253 37512859740383982820020095)
  ·
    refine ⟨56269289610575974230030143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37512859740383982820020095 56269289610575974230030143)
    ·
      refine ⟨84403934415863961345045215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56269289610575974230030143 84403934415863961345045215)
      ·
        refine ⟨126605901623795942017567823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84403934415863961345045215 126605901623795942017567823)
        ·
          refine ⟨189908852435693913026351735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126605901623795942017567823 189908852435693913026351735)
          ·
            refine ⟨284863278653540869539527603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189908852435693913026351735 284863278653540869539527603)
            ·
              refine ⟨427294917980311304309291405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284863278653540869539527603 427294917980311304309291405)
              ·
                refine ⟨160235594242616739115984277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427294917980311304309291405 160235594242616739115984277)
                ·
                  refine ⟨7511043480122659646061763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160235594242616739115984277 7511043480122659646061763)
                  ·
                    refine ⟨11266565220183989469092645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511043480122659646061763 11266565220183989469092645)
                    ·
                      refine ⟨2112480978784498025454871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11266565220183989469092645 2112480978784498025454871)
                      ·
                        rfl

theorem cell23_4114042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_4114042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114042 prefixEnd_4114042 := by exact prefixLift 4114042
  have htrace : WordTrace (prefixWord ++ tailWord_4114042) baseStart_4114042 baseEnd_4114042 := by
    simpa [prefixWord, tailWord_4114042, baseEnd_4114042] using wordTrace_append hprefix tailTrace_4114042
  have hstable : (prefixWord ++ tailWord_4114042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114042).length < 2 ^ (prefixWord ++ tailWord_4114042).sum := by decide
  have hdescent : baseEnd_4114042 < baseStart_4114042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114076 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4114076 : Nat := 118140960795 + 4114076 * 2 ^ 59
def prefixEnd_4114076 : Nat := 4983230072969 + 3 ^ 40 * 4114076 * 2
def baseEnd_4114076 : Nat := 2112498437126750892429715

theorem tailTrace_4114076 : CollatzResearch.WordTrace tailWord_4114076 prefixEnd_4114076 2112498437126750892429715 := by
  unfold tailWord_4114076
  simp only [CollatzResearch.WordTrace]
  refine ⟨75026339521706377543409041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100035119362275170057878721 75026339521706377543409041)
  ·
    refine ⟨56269754641279783157556781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75026339521706377543409041 56269754641279783157556781)
    ·
      refine ⟨21101157990479918684083793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56269754641279783157556781 21101157990479918684083793)
      ·
        refine ⟨15825868492859939013062845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21101157990479918684083793 15825868492859939013062845)
        ·
          refine ⟨5934700684822477129898567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15825868492859939013062845 5934700684822477129898567)
          ·
            refine ⟨8902051027233715694847851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934700684822477129898567 8902051027233715694847851)
            ·
              refine ⟨13353076540850573542271777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8902051027233715694847851 13353076540850573542271777)
              ·
                refine ⟨10014807405637930156703833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13353076540850573542271777 10014807405637930156703833)
                ·
                  refine ⟨7511105554228447617527875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10014807405637930156703833 7511105554228447617527875)
                  ·
                    refine ⟨11266658331342671426291813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511105554228447617527875 11266658331342671426291813)
                    ·
                      refine ⟨2112498437126750892429715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11266658331342671426291813 2112498437126750892429715)
                      ·
                        rfl

theorem cell23_4114076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4114076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114076 prefixEnd_4114076 := by exact prefixLift 4114076
  have htrace : WordTrace (prefixWord ++ tailWord_4114076) baseStart_4114076 baseEnd_4114076 := by
    simpa [prefixWord, tailWord_4114076, baseEnd_4114076] using wordTrace_append hprefix tailTrace_4114076
  have hstable : (prefixWord ++ tailWord_4114076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114076).length < 2 ^ (prefixWord ++ tailWord_4114076).sum := by decide
  have hdescent : baseEnd_4114076 < baseStart_4114076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114136 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 2, 3, 2]
def baseStart_4114136 : Nat := 118140960795 + 4114136 * 2 ^ 59
def prefixEnd_4114136 : Nat := 4983230072969 + 3 ^ 40 * 4114136 * 2
def baseEnd_4114136 : Nat := 2112529245966020657679439

theorem tailTrace_4114136 : CollatzResearch.WordTrace tailWord_4114136 prefixEnd_4114136 2112529245966020657679439 := by
  unfold tailWord_4114136
  simp only [CollatzResearch.WordTrace]
  refine ⟨75027433711597692667001131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100036578282130256889334841 75027433711597692667001131)
  ·
    refine ⟨112541150567396539000501697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75027433711597692667001131 112541150567396539000501697)
    ·
      refine ⟨84405862925547404250376273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112541150567396539000501697 84405862925547404250376273)
      ·
        refine ⟨63304397194160553187782205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84405862925547404250376273 63304397194160553187782205)
        ·
          refine ⟨23739148947810207445418327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63304397194160553187782205 23739148947810207445418327)
          ·
            refine ⟨35608723421715311168127491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23739148947810207445418327 35608723421715311168127491)
            ·
              refine ⟨53413085132572966752191237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35608723421715311168127491 53413085132572966752191237)
              ·
                refine ⟨10014953462357431266035857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53413085132572966752191237 10014953462357431266035857)
                ·
                  refine ⟨7511215096768073449526893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10014953462357431266035857 7511215096768073449526893)
                  ·
                    refine ⟨2816705661288027543572585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7511215096768073449526893 2816705661288027543572585)
                    ·
                      refine ⟨2112529245966020657679439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2816705661288027543572585 2112529245966020657679439)
                      ·
                        rfl

theorem cell23_4114136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_4114136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114136 prefixEnd_4114136 := by exact prefixLift 4114136
  have htrace : WordTrace (prefixWord ++ tailWord_4114136) baseStart_4114136 baseEnd_4114136 := by
    simpa [prefixWord, tailWord_4114136, baseEnd_4114136] using wordTrace_append hprefix tailTrace_4114136
  have hstable : (prefixWord ++ tailWord_4114136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114136).length < 2 ^ (prefixWord ++ tailWord_4114136).sum := by decide
  have hdescent : baseEnd_4114136 < baseStart_4114136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114143 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 1, 1, 3]
def baseStart_4114143 : Nat := 118140960795 + 4114143 * 2 ^ 59
def prefixEnd_4114143 : Nat := 4983230072969 + 3 ^ 40 * 4114143 * 2
def baseEnd_4114143 : Nat := 2112532840330602130291907

theorem tailTrace_4114143 : CollatzResearch.WordTrace tailWord_4114143 prefixEnd_4114143 2112532840330602130291907 := by
  unfold tailWord_4114143
  simp only [CollatzResearch.WordTrace]
  refine ⟨150055122734170025529507083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100036748489446683686338055 150055122734170025529507083)
  ·
    refine ⟨225082684101255038294260625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150055122734170025529507083 225082684101255038294260625)
    ·
      refine ⟨168812013075941278720695469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225082684101255038294260625 168812013075941278720695469)
      ·
        refine ⟨63304504903477979520260801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168812013075941278720695469 63304504903477979520260801)
        ·
          refine ⟨47478378677608484640195601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63304504903477979520260801 47478378677608484640195601)
          ·
            refine ⟨35608784008206363480146701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47478378677608484640195601 35608784008206363480146701)
            ·
              refine ⟨13353294003077386305055013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35608784008206363480146701 13353294003077386305055013)
              ·
                refine ⟨2503742625577009932197815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13353294003077386305055013 2503742625577009932197815)
                ·
                  refine ⟨3755613938365514898296723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2503742625577009932197815 3755613938365514898296723)
                  ·
                    refine ⟨5633420907548272347445085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3755613938365514898296723 5633420907548272347445085)
                    ·
                      refine ⟨2112532840330602130291907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5633420907548272347445085 2112532840330602130291907)
                      ·
                        rfl

theorem cell23_4114143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_4114143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114143 prefixEnd_4114143 := by exact prefixLift 4114143
  have htrace : WordTrace (prefixWord ++ tailWord_4114143) baseStart_4114143 baseEnd_4114143 := by
    simpa [prefixWord, tailWord_4114143, baseEnd_4114143] using wordTrace_append hprefix tailTrace_4114143
  have hstable : (prefixWord ++ tailWord_4114143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114143).length < 2 ^ (prefixWord ++ tailWord_4114143).sum := by decide
  have hdescent : baseEnd_4114143 < baseStart_4114143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114149 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 4]
def baseStart_4114149 : Nat := 118140960795 + 4114149 * 2 ^ 59
def prefixEnd_4114149 : Nat := 4983230072969 + 3 ^ 40 * 4114149 * 2
def baseEnd_4114149 : Nat := 2112535921214529106816879

theorem tailTrace_4114149 : CollatzResearch.WordTrace tailWord_4114149 prefixEnd_4114149 2112535921214529106816879 := by
  unfold tailWord_4114149
  simp only [CollatzResearch.WordTrace]
  refine ⟨150055341572148288554225501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100036894381432192369483667 150055341572148288554225501)
  ·
    refine ⟨56270753089555608207834563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 150055341572148288554225501 56270753089555608207834563)
    ·
      refine ⟨84406129634333412311751845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56270753089555608207834563 84406129634333412311751845)
      ·
        refine ⟨15826149306437514808453471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84406129634333412311751845 15826149306437514808453471)
        ·
          refine ⟨23739223959656272212680207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15826149306437514808453471 23739223959656272212680207)
          ·
            refine ⟨35608835939484408319020311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23739223959656272212680207 35608835939484408319020311)
            ·
              refine ⟨53413253909226612478530467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35608835939484408319020311 53413253909226612478530467)
              ·
                refine ⟨80119880863839918717795701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53413253909226612478530467 80119880863839918717795701)
                ·
                  refine ⟨7511238830984992379793347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80119880863839918717795701 7511238830984992379793347)
                  ·
                    refine ⟨11266858246477488569690021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511238830984992379793347 11266858246477488569690021)
                    ·
                      refine ⟨2112535921214529106816879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11266858246477488569690021 2112535921214529106816879)
                      ·
                        rfl

theorem cell23_4114149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_4114149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114149 prefixEnd_4114149 := by exact prefixLift 4114149
  have htrace : WordTrace (prefixWord ++ tailWord_4114149) baseStart_4114149 baseEnd_4114149 := by
    simpa [prefixWord, tailWord_4114149, baseEnd_4114149] using wordTrace_append hprefix tailTrace_4114149
  have hstable : (prefixWord ++ tailWord_4114149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114149).length < 2 ^ (prefixWord ++ tailWord_4114149).sum := by decide
  have hdescent : baseEnd_4114149 < baseStart_4114149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114159 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 1, 6]
def baseStart_4114159 : Nat := 118140960795 + 4114159 * 2 ^ 59
def prefixEnd_4114159 : Nat := 4983230072969 + 3 ^ 40 * 4114159 * 2
def baseEnd_4114159 : Nat := 704180352007024689230611

theorem tailTrace_4114159 : CollatzResearch.WordTrace tailWord_4114159 prefixEnd_4114159 704180352007024689230611 := by
  unfold tailWord_4114159
  simp only [CollatzResearch.WordTrace]
  refine ⟨150055706302112060262089531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100037137534741373508059687 150055706302112060262089531)
  ·
    refine ⟨225083559453168090393134297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150055706302112060262089531 225083559453168090393134297)
    ·
      refine ⟨168812669589876067794850723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225083559453168090393134297 168812669589876067794850723)
      ·
        refine ⟨253219004384814101692276085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168812669589876067794850723 253219004384814101692276085)
        ·
          refine ⟨23739281661076322033650883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 253219004384814101692276085 23739281661076322033650883)
          ·
            refine ⟨35608922491614483050476325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23739281661076322033650883 35608922491614483050476325)
            ·
              refine ⟨6676672967177715571964311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35608922491614483050476325 6676672967177715571964311)
              ·
                refine ⟨10015009450766573357946467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6676672967177715571964311 10015009450766573357946467)
                ·
                  refine ⟨15022514176149860036919701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015009450766573357946467 15022514176149860036919701)
                  ·
                    refine ⟨704180352007024689230611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15022514176149860036919701 704180352007024689230611)
                    ·
                      rfl

theorem cell23_4114159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_4114159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114159 prefixEnd_4114159 := by exact prefixLift 4114159
  have htrace : WordTrace (prefixWord ++ tailWord_4114159) baseStart_4114159 baseEnd_4114159 := by
    simpa [prefixWord, tailWord_4114159, baseEnd_4114159] using wordTrace_append hprefix tailTrace_4114159
  have hstable : (prefixWord ++ tailWord_4114159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114159).length < 2 ^ (prefixWord ++ tailWord_4114159).sum := by decide
  have hdescent : baseEnd_4114159 < baseStart_4114159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114166 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4114166 : Nat := 118140960795 + 4114166 * 2 ^ 59
def prefixEnd_4114166 : Nat := 4983230072969 + 3 ^ 40 * 4114166 * 2
def baseEnd_4114166 : Nat := 2112544650385655540304301

theorem tailTrace_4114166 : CollatzResearch.WordTrace tailWord_4114166 prefixEnd_4114166 2112544650385655540304301 := by
  unfold tailWord_4114166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378497600817918778599647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100037307742057800305062901 9378497600817918778599647)
  ·
    refine ⟨14067746401226878167899471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9378497600817918778599647 14067746401226878167899471)
    ·
      refine ⟨21101619601840317251849207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14067746401226878167899471 21101619601840317251849207)
      ·
        refine ⟨31652429402760475877773811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21101619601840317251849207 31652429402760475877773811)
        ·
          refine ⟨47478644104140713816660717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31652429402760475877773811 47478644104140713816660717)
          ·
            refine ⟨17804491539052767681247769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47478644104140713816660717 17804491539052767681247769)
            ·
              refine ⟨13353368654289575760935827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17804491539052767681247769 13353368654289575760935827)
              ·
                refine ⟨20030052981434363641403741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13353368654289575760935827 20030052981434363641403741)
                ·
                  refine ⟨7511269868037886365526403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20030052981434363641403741 7511269868037886365526403)
                  ·
                    refine ⟨11266904802056829548289605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7511269868037886365526403 11266904802056829548289605)
                    ·
                      refine ⟨2112544650385655540304301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11266904802056829548289605 2112544650385655540304301)
                      ·
                        rfl

theorem cell23_4114166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4114166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114166 prefixEnd_4114166 := by exact prefixLift 4114166
  have htrace : WordTrace (prefixWord ++ tailWord_4114166) baseStart_4114166 baseEnd_4114166 := by
    simpa [prefixWord, tailWord_4114166, baseEnd_4114166] using wordTrace_append hprefix tailTrace_4114166
  have hstable : (prefixWord ++ tailWord_4114166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114166).length < 2 ^ (prefixWord ++ tailWord_4114166).sum := by decide
  have hdescent : baseEnd_4114166 < baseStart_4114166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4114179 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4]
def baseStart_4114179 : Nat := 118140960795 + 4114179 * 2 ^ 59
def prefixEnd_4114179 : Nat := 4983230072969 + 3 ^ 40 * 4114179 * 2
def baseEnd_4114179 : Nat := 2112551325634163989441741

theorem tailTrace_4114179 : CollatzResearch.WordTrace tailWord_4114179 prefixEnd_4114179 2112551325634163989441741 := by
  unfold tailWord_4114179
  simp only [CollatzResearch.WordTrace]
  refine ⟨150056435762039603677817591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100037623841359735785211727 150056435762039603677817591)
  ·
    refine ⟨225084653643059405516726387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150056435762039603677817591 225084653643059405516726387)
    ·
      refine ⟨337626980464589108275089581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225084653643059405516726387 337626980464589108275089581)
      ·
        refine ⟨126610117674220915603158593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337626980464589108275089581 126610117674220915603158593)
        ·
          refine ⟨94957588255665686702368945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126610117674220915603158593 94957588255665686702368945)
          ·
            refine ⟨71218191191749265026776709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94957588255665686702368945 71218191191749265026776709)
            ·
              refine ⟨13353410848452987192520633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71218191191749265026776709 13353410848452987192520633)
              ·
                refine ⟨10015058136339740394390475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13353410848452987192520633 10015058136339740394390475)
                ·
                  refine ⟨15022587204509610591585713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10015058136339740394390475 15022587204509610591585713)
                  ·
                    refine ⟨11266940403382207943689285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15022587204509610591585713 11266940403382207943689285)
                    ·
                      refine ⟨2112551325634163989441741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11266940403382207943689285 2112551325634163989441741)
                      ·
                        rfl

theorem cell23_4114179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_4114179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4114179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4114179 prefixEnd_4114179 := by exact prefixLift 4114179
  have htrace : WordTrace (prefixWord ++ tailWord_4114179) baseStart_4114179 baseEnd_4114179 := by
    simpa [prefixWord, tailWord_4114179, baseEnd_4114179] using wordTrace_append hprefix tailTrace_4114179
  have hstable : (prefixWord ++ tailWord_4114179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4114179).length < 2 ^ (prefixWord ++ tailWord_4114179).sum := by decide
  have hdescent : baseEnd_4114179 < baseStart_4114179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4114179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
