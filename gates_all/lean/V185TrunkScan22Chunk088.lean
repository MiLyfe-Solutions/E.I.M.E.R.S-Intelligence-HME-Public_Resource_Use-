import V185TrunkScan22Chunk087

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_790626 : List Nat := [3, 3, 2, 2, 3, 1, 1, 7]
def baseStart_790626 : Nat := 118140960795 + 790626 * 2 ^ 59
def prefixEnd_790626 : Nat := 4983230072969 + 3 ^ 40 * 790626 * 2
def baseEnd_790626 : Nat := 30071937477165104136221

theorem tailTrace_790626 : CollatzResearch.WordTrace tailWord_790626 prefixEnd_790626 30071937477165104136221 := by
  unfold tailWord_790626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209124808426126253941933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19224332822469670010511821 7209124808426126253941933)
  ·
    refine ⟨2703421803159797345228225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7209124808426126253941933 2703421803159797345228225)
    ·
      refine ⟨2027566352369848008921169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703421803159797345228225 2027566352369848008921169)
      ·
        refine ⟨1520674764277386006690877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027566352369848008921169 1520674764277386006690877)
        ·
          refine ⟨570253036604019752509079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1520674764277386006690877 570253036604019752509079)
          ·
            refine ⟨855379554906029628763619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570253036604019752509079 855379554906029628763619)
            ·
              refine ⟨1283069332359044443145429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855379554906029628763619 1283069332359044443145429)
              ·
                refine ⟨30071937477165104136221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1283069332359044443145429 30071937477165104136221)
                ·
                  rfl

theorem cell22_790626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 7].length) (baseStart_790626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790626 prefixEnd_790626 := by exact prefixLift 790626
  have htrace : WordTrace (prefixWord ++ tailWord_790626) baseStart_790626 baseEnd_790626 := by
    simpa [prefixWord, tailWord_790626, baseEnd_790626] using wordTrace_append hprefix tailTrace_790626
  have hstable : (prefixWord ++ tailWord_790626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790626).length < 2 ^ (prefixWord ++ tailWord_790626).sum := by decide
  have hdescent : baseEnd_790626 < baseStart_790626 := by decide
  rcases family_descends (prefixWord ++ tailWord_790626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790637 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 5]
def baseStart_790637 : Nat := 118140960795 + 790637 * 2 ^ 59
def prefixEnd_790637 : Nat := 4983230072969 + 3 ^ 40 * 790637 * 2
def baseEnd_790637 : Nat := 90217067606428525066985

theorem tailTrace_790637 : CollatzResearch.WordTrace tailWord_790637 prefixEnd_790637 90217067606428525066985 := by
  unfold tailWord_790637
  simp only [CollatzResearch.WordTrace]
  refine ⟨28836900436664653894418165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19224600291109769262945443 28836900436664653894418165)
  ·
    refine ⟨2703459415937311302601703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28836900436664653894418165 2703459415937311302601703)
    ·
      refine ⟨4055189123905966953902555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703459415937311302601703 4055189123905966953902555)
      ·
        refine ⟨6082783685858950430853833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055189123905966953902555 6082783685858950430853833)
        ·
          refine ⟨4562087764394212823140375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6082783685858950430853833 4562087764394212823140375)
          ·
            refine ⟨6843131646591319234710563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562087764394212823140375 6843131646591319234710563)
            ·
              refine ⟨10264697469886978852065845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6843131646591319234710563 10264697469886978852065845)
              ·
                refine ⟨962315387801904267381173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10264697469886978852065845 962315387801904267381173)
                ·
                  refine ⟨90217067606428525066985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 962315387801904267381173 90217067606428525066985)
                  ·
                    rfl

theorem cell22_790637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_790637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790637 prefixEnd_790637 := by exact prefixLift 790637
  have htrace : WordTrace (prefixWord ++ tailWord_790637) baseStart_790637 baseEnd_790637 := by
    simpa [prefixWord, tailWord_790637, baseEnd_790637] using wordTrace_append hprefix tailTrace_790637
  have hstable : (prefixWord ++ tailWord_790637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790637).length < 2 ^ (prefixWord ++ tailWord_790637).sum := by decide
  have hdescent : baseEnd_790637 < baseStart_790637 := by decide
  rcases family_descends (prefixWord ++ tailWord_790637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790665 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 8]
def baseStart_790665 : Nat := 118140960795 + 790665 * 2 ^ 59
def prefixEnd_790665 : Nat := 4983230072969 + 3 ^ 40 * 790665 * 2
def baseEnd_790665 : Nat := 90220262597167611833623

theorem tailTrace_790665 : CollatzResearch.WordTrace tailWord_790665 prefixEnd_790665 90220262597167611833623 := by
  unfold tailWord_790665
  simp only [CollatzResearch.WordTrace]
  refine ⟨28837921680563214676437449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19225281120375476450958299 28837921680563214676437449)
  ·
    refine ⟨21628441260422411007328087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28837921680563214676437449 21628441260422411007328087)
    ·
      refine ⟨32442661890633616510992131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21628441260422411007328087 32442661890633616510992131)
      ·
        refine ⟨48663992835950424766488197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32442661890633616510992131 48663992835950424766488197)
        ·
          refine ⟨9124498656740704643716537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48663992835950424766488197 9124498656740704643716537)
          ·
            refine ⟨6843373992555528482787403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9124498656740704643716537 6843373992555528482787403)
            ·
              refine ⟨10265060988833292724181105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6843373992555528482787403 10265060988833292724181105)
              ·
                refine ⟨7698795741624969543135829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10265060988833292724181105 7698795741624969543135829)
                ·
                  refine ⟨90220262597167611833623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7698795741624969543135829 90220262597167611833623)
                  ·
                    rfl

theorem cell22_790665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_790665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790665 prefixEnd_790665 := by exact prefixLift 790665
  have htrace : WordTrace (prefixWord ++ tailWord_790665) baseStart_790665 baseEnd_790665 := by
    simpa [prefixWord, tailWord_790665, baseEnd_790665] using wordTrace_append hprefix tailTrace_790665
  have hstable : (prefixWord ++ tailWord_790665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790665).length < 2 ^ (prefixWord ++ tailWord_790665).sum := by decide
  have hdescent : baseEnd_790665 < baseStart_790665 := by decide
  rcases family_descends (prefixWord ++ tailWord_790665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790701 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_790701 : Nat := 118140960795 + 790701 * 2 ^ 59
def prefixEnd_790701 : Nat := 4983230072969 + 3 ^ 40 * 790701 * 2
def baseEnd_790701 : Nat := 270673111327210741600759

theorem tailTrace_790701 : CollatzResearch.WordTrace tailWord_790701 prefixEnd_790701 270673111327210741600759 := by
  unfold tailWord_790701
  simp only [CollatzResearch.WordTrace]
  refine ⟨28839234708432792824747957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19226156472288528549831971 28839234708432792824747957)
  ·
    refine ⟨2703678253915574327320121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28839234708432792824747957 2703678253915574327320121)
    ·
      refine ⟨2027758690436680745490091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703678253915574327320121 2027758690436680745490091)
      ·
        refine ⟨3041638035655021118235137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027758690436680745490091 3041638035655021118235137)
        ·
          refine ⟨2281228526741265838676353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3041638035655021118235137 2281228526741265838676353)
          ·
            refine ⟨1710921395055949379007265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281228526741265838676353 1710921395055949379007265)
            ·
              refine ⟨1283191046291962034255449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710921395055949379007265 1283191046291962034255449)
              ·
                refine ⟨962393284718971525691587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283191046291962034255449 962393284718971525691587)
                ·
                  refine ⟨1443589927078457288537381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962393284718971525691587 1443589927078457288537381)
                  ·
                    refine ⟨270673111327210741600759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443589927078457288537381 270673111327210741600759)
                    ·
                      rfl

theorem cell22_790701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_790701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790701 prefixEnd_790701 := by exact prefixLift 790701
  have htrace : WordTrace (prefixWord ++ tailWord_790701) baseStart_790701 baseEnd_790701 := by
    simpa [prefixWord, tailWord_790701, baseEnd_790701] using wordTrace_append hprefix tailTrace_790701
  have hstable : (prefixWord ++ tailWord_790701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790701).length < 2 ^ (prefixWord ++ tailWord_790701).sum := by decide
  have hdescent : baseEnd_790701 < baseStart_790701 := by decide
  rcases family_descends (prefixWord ++ tailWord_790701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790712 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_790712 : Nat := 118140960795 + 790712 * 2 ^ 59
def prefixEnd_790712 : Nat := 4983230072969 + 3 ^ 40 * 790712 * 2
def baseEnd_790712 : Nat := 270676876852010379575725

theorem tailTrace_790712 : CollatzResearch.WordTrace tailWord_790712 prefixEnd_790712 270676876852010379575725 := by
  unfold tailWord_790712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419817955696470851699195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19226423940928627802265593 14419817955696470851699195)
  ·
    refine ⟨21629726933544706277548793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14419817955696470851699195 21629726933544706277548793)
    ·
      refine ⟨16222295200158529708161595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21629726933544706277548793 16222295200158529708161595)
      ·
        refine ⟨24333442800237794562242393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16222295200158529708161595 24333442800237794562242393)
        ·
          refine ⟨18250082100178345921681795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24333442800237794562242393 18250082100178345921681795)
          ·
            refine ⟨27375123150267518882522693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18250082100178345921681795 27375123150267518882522693)
            ·
              refine ⟨5132835590675159790473005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27375123150267518882522693 5132835590675159790473005)
              ·
                refine ⟨1924813346503184921427377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5132835590675159790473005 1924813346503184921427377)
                ·
                  refine ⟨1443610009877388691070533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1924813346503184921427377 1443610009877388691070533)
                  ·
                    refine ⟨270676876852010379575725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443610009877388691070533 270676876852010379575725)
                    ·
                      rfl

theorem cell22_790712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_790712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790712 prefixEnd_790712 := by exact prefixLift 790712
  have htrace : WordTrace (prefixWord ++ tailWord_790712) baseStart_790712 baseEnd_790712 := by
    simpa [prefixWord, tailWord_790712, baseEnd_790712] using wordTrace_append hprefix tailTrace_790712
  have hstable : (prefixWord ++ tailWord_790712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790712).length < 2 ^ (prefixWord ++ tailWord_790712).sum := by decide
  have hdescent : baseEnd_790712 < baseStart_790712 := by decide
  rcases family_descends (prefixWord ++ tailWord_790712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790787 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_790787 : Nat := 118140960795 + 790787 * 2 ^ 59
def prefixEnd_790787 : Nat := 4983230072969 + 3 ^ 40 * 790787 * 2
def baseEnd_790787 : Nat := 270702550884735183950495

theorem tailTrace_790787 : CollatzResearch.WordTrace tailWord_790787 prefixEnd_790787 270702550884735183950495 := by
  unfold tailWord_790787
  simp only [CollatzResearch.WordTrace]
  refine ⟨28842371386121229512378615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19228247590747486341585743 28842371386121229512378615)
  ·
    refine ⟨43263557079181844268567923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28842371386121229512378615 43263557079181844268567923)
    ·
      refine ⟨64895335618772766402851885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43263557079181844268567923 64895335618772766402851885)
      ·
        refine ⟨24335750857039787401069457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64895335618772766402851885 24335750857039787401069457)
        ·
          refine ⟨18251813142779840550802093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24335750857039787401069457 18251813142779840550802093)
          ·
            refine ⟨6844429928542440206550785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18251813142779840550802093 6844429928542440206550785)
            ·
              refine ⟨5133322446406830154913089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844429928542440206550785 5133322446406830154913089)
              ·
                refine ⟨3849991834805122616184817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133322446406830154913089 3849991834805122616184817)
                ·
                  refine ⟨2887493876103841962138613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3849991834805122616184817 2887493876103841962138613)
                  ·
                    refine ⟨270702550884735183950495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2887493876103841962138613 270702550884735183950495)
                    ·
                      rfl

theorem cell22_790787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_790787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790787 prefixEnd_790787 := by exact prefixLift 790787
  have htrace : WordTrace (prefixWord ++ tailWord_790787) baseStart_790787 baseEnd_790787 := by
    simpa [prefixWord, tailWord_790787, baseEnd_790787] using wordTrace_append hprefix tailTrace_790787
  have hstable : (prefixWord ++ tailWord_790787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790787).length < 2 ^ (prefixWord ++ tailWord_790787).sum := by decide
  have hdescent : baseEnd_790787 < baseStart_790787 := by decide
  rcases family_descends (prefixWord ++ tailWord_790787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790793 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 1, 3]
def baseStart_790793 : Nat := 118140960795 + 790793 * 2 ^ 59
def prefixEnd_790793 : Nat := 4983230072969 + 3 ^ 40 * 790793 * 2
def baseEnd_790793 : Nat := 270704604807353168300477

theorem tailTrace_790793 : CollatzResearch.WordTrace tailWord_790793 prefixEnd_790793 270704604807353168300477 := by
  unfold tailWord_790793
  simp only [CollatzResearch.WordTrace]
  refine ⟨28842590224099492537097033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19228393482732995024731355 28842590224099492537097033)
  ·
    refine ⟨21631942668074619402822775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28842590224099492537097033 21631942668074619402822775)
    ·
      refine ⟨32447914002111929104234163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21631942668074619402822775 32447914002111929104234163)
      ·
        refine ⟨48671871003167893656351245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32447914002111929104234163 48671871003167893656351245)
        ·
          refine ⟨18251951626187960121131717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48671871003167893656351245 18251951626187960121131717)
          ·
            refine ⟨3422240929910242522712197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18251951626187960121131717 3422240929910242522712197)
            ·
              refine ⟨641670174358170473008537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3422240929910242522712197 641670174358170473008537)
              ·
                refine ⟨481252630768627854756403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641670174358170473008537 481252630768627854756403)
                ·
                  refine ⟨721878946152941782134605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481252630768627854756403 721878946152941782134605)
                  ·
                    refine ⟨270704604807353168300477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721878946152941782134605 270704604807353168300477)
                    ·
                      rfl

theorem cell22_790793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 3].length) (baseStart_790793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790793 prefixEnd_790793 := by exact prefixLift 790793
  have htrace : WordTrace (prefixWord ++ tailWord_790793) baseStart_790793 baseEnd_790793 := by
    simpa [prefixWord, tailWord_790793, baseEnd_790793] using wordTrace_append hprefix tailTrace_790793
  have hstable : (prefixWord ++ tailWord_790793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790793).length < 2 ^ (prefixWord ++ tailWord_790793).sum := by decide
  have hdescent : baseEnd_790793 < baseStart_790793 := by decide
  rcases family_descends (prefixWord ++ tailWord_790793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790817 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 8]
def baseStart_790817 : Nat := 118140960795 + 790817 * 2 ^ 59
def prefixEnd_790817 : Nat := 4983230072969 + 3 ^ 40 * 790817 * 2
def baseEnd_790817 : Nat := 90237606832608368566801

theorem tailTrace_790817 : CollatzResearch.WordTrace tailWord_790817 prefixEnd_790817 90237606832608368566801 := by
  unfold tailWord_790817
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843465576012544635970705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19228977050675029757313803 28843465576012544635970705)
  ·
    refine ⟨21632599182009408476978029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28843465576012544635970705 21632599182009408476978029)
    ·
      refine ⟨8112224693253528178866761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21632599182009408476978029 8112224693253528178866761)
      ·
        refine ⟨6084168519940146134150071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8112224693253528178866761 6084168519940146134150071)
        ·
          refine ⟨9126252779910219201225107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6084168519940146134150071 9126252779910219201225107)
          ·
            refine ⟨13689379169865328801837661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126252779910219201225107 13689379169865328801837661)
            ·
              refine ⟨5133517188699498300689123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13689379169865328801837661 5133517188699498300689123)
              ·
                refine ⟨7700275783049247451033685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5133517188699498300689123 7700275783049247451033685)
                ·
                  refine ⟨90237606832608368566801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7700275783049247451033685 90237606832608368566801)
                  ·
                    rfl

theorem cell22_790817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_790817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790817 prefixEnd_790817 := by exact prefixLift 790817
  have htrace : WordTrace (prefixWord ++ tailWord_790817) baseStart_790817 baseEnd_790817 := by
    simpa [prefixWord, tailWord_790817, baseEnd_790817] using wordTrace_append hprefix tailTrace_790817
  have hstable : (prefixWord ++ tailWord_790817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790817).length < 2 ^ (prefixWord ++ tailWord_790817).sum := by decide
  have hdescent : baseEnd_790817 < baseStart_790817 := by decide
  rcases family_descends (prefixWord ++ tailWord_790817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790819 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 1, 4]
def baseStart_790819 : Nat := 118140960795 + 790819 * 2 ^ 59
def prefixEnd_790819 : Nat := 4983230072969 + 3 ^ 40 * 790819 * 2
def baseEnd_790819 : Nat := 270713505138697767150397

theorem tailTrace_790819 : CollatzResearch.WordTrace tailWord_790819 prefixEnd_790819 270713505138697767150397 := by
  unfold tailWord_790819
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843538522005298977543511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19229025681336865985029007 28843538522005298977543511)
  ·
    refine ⟨43265307783007948466315267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28843538522005298977543511 43265307783007948466315267)
    ·
      refine ⟨64897961674511922699472901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43265307783007948466315267 64897961674511922699472901)
      ·
        refine ⟨12168367813970985506151169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64897961674511922699472901 12168367813970985506151169)
        ·
          refine ⟨9126275860478239129613377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12168367813970985506151169 9126275860478239129613377)
          ·
            refine ⟨6844706895358679347210033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9126275860478239129613377 6844706895358679347210033)
            ·
              refine ⟨5133530171519009510407525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844706895358679347210033 5133530171519009510407525)
              ·
                refine ⟨962536907159814283201411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5133530171519009510407525 962536907159814283201411)
                ·
                  refine ⟨1443805360739721424802117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962536907159814283201411 1443805360739721424802117)
                  ·
                    refine ⟨270713505138697767150397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1443805360739721424802117 270713505138697767150397)
                    ·
                      rfl

theorem cell22_790819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 4].length) (baseStart_790819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790819 prefixEnd_790819 := by exact prefixLift 790819
  have htrace : WordTrace (prefixWord ++ tailWord_790819) baseStart_790819 baseEnd_790819 := by
    simpa [prefixWord, tailWord_790819, baseEnd_790819] using wordTrace_append hprefix tailTrace_790819
  have hstable : (prefixWord ++ tailWord_790819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790819).length < 2 ^ (prefixWord ++ tailWord_790819).sum := by decide
  have hdescent : baseEnd_790819 < baseStart_790819 := by decide
  rcases family_descends (prefixWord ++ tailWord_790819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790832 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_790832 : Nat := 118140960795 + 790832 * 2 ^ 59
def prefixEnd_790832 : Nat := 4983230072969 + 3 ^ 40 * 790832 * 2
def baseEnd_790832 : Nat := 270717955304370066575357

theorem tailTrace_790832 : CollatzResearch.WordTrace tailWord_790832 prefixEnd_790832 270717955304370066575357 := by
  unfold tailWord_790832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14422006335479101098883375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19229341780638801465177833 14422006335479101098883375)
  ·
    refine ⟨21633009503218651648325063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14422006335479101098883375 21633009503218651648325063)
    ·
      refine ⟨32449514254827977472487595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21633009503218651648325063 32449514254827977472487595)
      ·
        refine ⟨48674271382241966208731393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32449514254827977472487595 48674271382241966208731393)
        ·
          refine ⟨36505703536681474656548545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48674271382241966208731393 36505703536681474656548545)
          ·
            refine ⟨27379277652511105992411409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36505703536681474656548545 27379277652511105992411409)
            ·
              refine ⟨20534458239383329494308557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27379277652511105992411409 20534458239383329494308557)
              ·
                refine ⟨7700421839768748560365709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20534458239383329494308557 7700421839768748560365709)
                ·
                  refine ⟨2887658189913280710137141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7700421839768748560365709 2887658189913280710137141)
                  ·
                    refine ⟨270717955304370066575357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2887658189913280710137141 270717955304370066575357)
                    ·
                      rfl

theorem cell22_790832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_790832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790832 prefixEnd_790832 := by exact prefixLift 790832
  have htrace : WordTrace (prefixWord ++ tailWord_790832) baseStart_790832 baseEnd_790832 := by
    simpa [prefixWord, tailWord_790832, baseEnd_790832] using wordTrace_append hprefix tailTrace_790832
  have hstable : (prefixWord ++ tailWord_790832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790832).length < 2 ^ (prefixWord ++ tailWord_790832).sum := by decide
  have hdescent : baseEnd_790832 < baseStart_790832 := by decide
  rcases family_descends (prefixWord ++ tailWord_790832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790866 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_790866 : Nat := 118140960795 + 790866 * 2 ^ 59
def prefixEnd_790866 : Nat := 4983230072969 + 3 ^ 40 * 790866 * 2
def baseEnd_790866 : Nat := 270729594199205311225253

theorem tailTrace_790866 : CollatzResearch.WordTrace tailWord_790866 prefixEnd_790866 270729594199205311225253 := by
  unfold tailWord_790866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211313188208756501126113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19230168501890017336336301 7211313188208756501126113)
  ·
    refine ⟨5408484891156567375844585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7211313188208756501126113 5408484891156567375844585)
    ·
      refine ⟨4056363668367425531883439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5408484891156567375844585 4056363668367425531883439)
      ·
        refine ⟨6084545502551138297825159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056363668367425531883439 6084545502551138297825159)
        ·
          refine ⟨9126818253826707446737739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6084545502551138297825159 9126818253826707446737739)
          ·
            refine ⟨13690227380740061170106609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126818253826707446737739 13690227380740061170106609)
            ·
              refine ⟨10267670535555045877579957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13690227380740061170106609 10267670535555045877579957)
              ·
                refine ⟨962594112708285551023121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10267670535555045877579957 962594112708285551023121)
                ·
                  refine ⟨721945584531214163267341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962594112708285551023121 721945584531214163267341)
                  ·
                    refine ⟨270729594199205311225253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721945584531214163267341 270729594199205311225253)
                    ·
                      rfl

theorem cell22_790866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_790866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790866 prefixEnd_790866 := by exact prefixLift 790866
  have htrace : WordTrace (prefixWord ++ tailWord_790866) baseStart_790866 baseEnd_790866 := by
    simpa [prefixWord, tailWord_790866, baseEnd_790866] using wordTrace_append hprefix tailTrace_790866
  have hstable : (prefixWord ++ tailWord_790866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790866).length < 2 ^ (prefixWord ++ tailWord_790866).sum := by decide
  have hdescent : baseEnd_790866 < baseStart_790866 := by decide
  rcases family_descends (prefixWord ++ tailWord_790866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790878 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_790878 : Nat := 118140960795 + 790878 * 2 ^ 59
def prefixEnd_790878 : Nat := 4983230072969 + 3 ^ 40 * 790878 * 2
def baseEnd_790878 : Nat := 270733702044441279925217

theorem tailTrace_790878 : CollatzResearch.WordTrace tailWord_790878 prefixEnd_790878 270733702044441279925217 := by
  unfold tailWord_790878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605711303598944006742661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19230460285861034702627525 3605711303598944006742661)
  ·
    refine ⟨676070869424802001264249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3605711303598944006742661 676070869424802001264249)
    ·
      refine ⟨507053152068601500948187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 676070869424802001264249 507053152068601500948187)
      ·
        refine ⟨760579728102902251422281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507053152068601500948187 760579728102902251422281)
        ·
          refine ⟨570434796077176688566711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760579728102902251422281 570434796077176688566711)
          ·
            refine ⟨855652194115765032850067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570434796077176688566711 855652194115765032850067)
            ·
              refine ⟨1283478291173647549275101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855652194115765032850067 1283478291173647549275101)
              ·
                refine ⟨481304359190117830978163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1283478291173647549275101 481304359190117830978163)
                ·
                  refine ⟨721956538785176746467245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481304359190117830978163 721956538785176746467245)
                  ·
                    refine ⟨270733702044441279925217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 721956538785176746467245 270733702044441279925217)
                    ·
                      rfl

theorem cell22_790878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_790878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790878 prefixEnd_790878 := by exact prefixLift 790878
  have htrace : WordTrace (prefixWord ++ tailWord_790878) baseStart_790878 baseEnd_790878 := by
    simpa [prefixWord, tailWord_790878, baseEnd_790878] using wordTrace_append hprefix tailTrace_790878
  have hstable : (prefixWord ++ tailWord_790878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790878).length < 2 ^ (prefixWord ++ tailWord_790878).sum := by decide
  have hdescent : baseEnd_790878 < baseStart_790878 := by decide
  rcases family_descends (prefixWord ++ tailWord_790878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790879 : List Nat := [1, 1, 2, 3, 1, 2, 6, 6]
def baseStart_790879 : Nat := 118140960795 + 790879 * 2 ^ 59
def prefixEnd_790879 : Nat := 4983230072969 + 3 ^ 40 * 790879 * 2
def baseEnd_790879 : Nat := 30081560484986401183357

theorem tailTrace_790879 : CollatzResearch.WordTrace tailWord_790879 prefixEnd_790879 30081560484986401183357 := by
  unfold tailWord_790879
  simp only [CollatzResearch.WordTrace]
  refine ⟨28845726901787929224727691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19230484601191952816485127 28845726901787929224727691)
  ·
    refine ⟨43268590352681893837091537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28845726901787929224727691 43268590352681893837091537)
    ·
      refine ⟨32451442764511420377818653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43268590352681893837091537 32451442764511420377818653)
      ·
        refine ⟨12169291036691782641681995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32451442764511420377818653 12169291036691782641681995)
        ·
          refine ⟨18253936555037673962522993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12169291036691782641681995 18253936555037673962522993)
          ·
            refine ⟨13690452416278255471892245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18253936555037673962522993 13690452416278255471892245)
            ·
              refine ⟨641739957013043225244949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13690452416278255471892245 641739957013043225244949)
              ·
                refine ⟨30081560484986401183357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 641739957013043225244949 30081560484986401183357)
                ·
                  rfl

theorem cell22_790879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 6].length) (baseStart_790879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790879 prefixEnd_790879 := by exact prefixLift 790879
  have htrace : WordTrace (prefixWord ++ tailWord_790879) baseStart_790879 baseEnd_790879 := by
    simpa [prefixWord, tailWord_790879, baseEnd_790879] using wordTrace_append hprefix tailTrace_790879
  have hstable : (prefixWord ++ tailWord_790879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790879).length < 2 ^ (prefixWord ++ tailWord_790879).sum := by decide
  have hdescent : baseEnd_790879 < baseStart_790879 := by decide
  rcases family_descends (prefixWord ++ tailWord_790879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790902 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_790902 : Nat := 118140960795 + 790902 * 2 ^ 59
def prefixEnd_790902 : Nat := 4983230072969 + 3 ^ 40 * 790902 * 2
def baseEnd_790902 : Nat := 90247305911637739108381

theorem tailTrace_790902 : CollatzResearch.WordTrace tailWord_790902 prefixEnd_790902 90247305911637739108381 := by
  unfold tailWord_790902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802910361294037759550935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19231043853803069435209973 1802910361294037759550935)
  ·
    refine ⟨2704365541941056639326403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802910361294037759550935 2704365541941056639326403)
    ·
      refine ⟨4056548312911584958989605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704365541941056639326403 4056548312911584958989605)
      ·
        refine ⟨760602808670922179810551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4056548312911584958989605 760602808670922179810551)
        ·
          refine ⟨1140904213006383269715827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760602808670922179810551 1140904213006383269715827)
          ·
            refine ⟨1711356319509574904573741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140904213006383269715827 1711356319509574904573741)
            ·
              refine ⟨641758619816090589215153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1711356319509574904573741 641758619816090589215153)
              ·
                refine ⟨481318964862067941911365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641758619816090589215153 481318964862067941911365)
                ·
                  refine ⟨90247305911637739108381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481318964862067941911365 90247305911637739108381)
                  ·
                    rfl

theorem cell22_790902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_790902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_790902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_790902 prefixEnd_790902 := by exact prefixLift 790902
  have htrace : WordTrace (prefixWord ++ tailWord_790902) baseStart_790902 baseEnd_790902 := by
    simpa [prefixWord, tailWord_790902, baseEnd_790902] using wordTrace_append hprefix tailTrace_790902
  have hstable : (prefixWord ++ tailWord_790902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790902).length < 2 ^ (prefixWord ++ tailWord_790902).sum := by decide
  have hdescent : baseEnd_790902 < baseStart_790902 := by decide
  rcases family_descends (prefixWord ++ tailWord_790902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791001 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 4, 3]
def baseStart_791001 : Nat := 118140960795 + 791001 * 2 ^ 59
def prefixEnd_791001 : Nat := 4983230072969 + 3 ^ 40 * 791001 * 2
def baseEnd_791001 : Nat := 270775807458109959099839

theorem tailTrace_791001 : CollatzResearch.WordTrace tailWord_791001 prefixEnd_791001 270775807458109959099839 := by
  unfold tailWord_791001
  simp only [CollatzResearch.WordTrace]
  refine ⟨28850176607345944060668857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19233451071563962707112571 28850176607345944060668857)
  ·
    refine ⟨21637632455509458045501643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28850176607345944060668857 21637632455509458045501643)
    ·
      refine ⟨32456448683264187068252465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21637632455509458045501643 32456448683264187068252465)
      ·
        refine ⟨24342336512448140301189349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32456448683264187068252465 24342336512448140301189349)
        ·
          refine ⟨4564188096084026306473003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24342336512448140301189349 4564188096084026306473003)
          ·
            refine ⟨6846282144126039459709505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564188096084026306473003 6846282144126039459709505)
            ·
              refine ⟨5134711608094529594782129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6846282144126039459709505 5134711608094529594782129)
              ·
                refine ⟨3851033706070897196086597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134711608094529594782129 3851033706070897196086597)
                ·
                  refine ⟨722068819888293224266237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3851033706070897196086597 722068819888293224266237)
                  ·
                    refine ⟨270775807458109959099839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 722068819888293224266237 270775807458109959099839)
                    ·
                      rfl

theorem cell22_791001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 4, 3].length) (baseStart_791001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791001 prefixEnd_791001 := by exact prefixLift 791001
  have htrace : WordTrace (prefixWord ++ tailWord_791001) baseStart_791001 baseEnd_791001 := by
    simpa [prefixWord, tailWord_791001, baseEnd_791001] using wordTrace_append hprefix tailTrace_791001
  have hstable : (prefixWord ++ tailWord_791001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791001).length < 2 ^ (prefixWord ++ tailWord_791001).sum := by decide
  have hdescent : baseEnd_791001 < baseStart_791001 := by decide
  rcases family_descends (prefixWord ++ tailWord_791001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791018 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_791018 : Nat := 118140960795 + 791018 * 2 ^ 59
def prefixEnd_791018 : Nat := 4983230072969 + 3 ^ 40 * 791018 * 2
def baseEnd_791018 : Nat := 270781626905527581424787

theorem tailTrace_791018 : CollatzResearch.WordTrace tailWord_791018 prefixEnd_791018 270781626905527581424787 := by
  unfold tailWord_791018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212699162071088991009427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19233864432189570642691805 7212699162071088991009427)
  ·
    refine ⟨10819048743106633486514141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7212699162071088991009427 10819048743106633486514141)
    ·
      refine ⟨4057143278664987557442803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10819048743106633486514141 4057143278664987557442803)
      ·
        refine ⟨6085714917997481336164205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057143278664987557442803 6085714917997481336164205)
        ·
          refine ⟨2282143094249055501061577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6085714917997481336164205 2282143094249055501061577)
          ·
            refine ⟨1711607320686791625796183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282143094249055501061577 1711607320686791625796183)
            ·
              refine ⟨2567410981030187438694275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711607320686791625796183 2567410981030187438694275)
              ·
                refine ⟨3851116471545281158041413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567410981030187438694275 3851116471545281158041413)
                ·
                  refine ⟨722084338414740217132765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3851116471545281158041413 722084338414740217132765)
                  ·
                    refine ⟨270781626905527581424787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 722084338414740217132765 270781626905527581424787)
                    ·
                      rfl

theorem cell22_791018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_791018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791018 prefixEnd_791018 := by exact prefixLift 791018
  have htrace : WordTrace (prefixWord ++ tailWord_791018) baseStart_791018 baseEnd_791018 := by
    simpa [prefixWord, tailWord_791018, baseEnd_791018] using wordTrace_append hprefix tailTrace_791018
  have hstable : (prefixWord ++ tailWord_791018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791018).length < 2 ^ (prefixWord ++ tailWord_791018).sum := by decide
  have hdescent : baseEnd_791018 < baseStart_791018 := by decide
  rcases family_descends (prefixWord ++ tailWord_791018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791059 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 9]
def baseStart_791059 : Nat := 118140960795 + 791059 * 2 ^ 59
def prefixEnd_791059 : Nat := 4983230072969 + 3 ^ 40 * 791059 * 2
def baseEnd_791059 : Nat := 90265220681139047049887

theorem tailTrace_791059 : CollatzResearch.WordTrace tailWord_791059 prefixEnd_791059 90265220681139047049887 := by
  unfold tailWord_791059
  simp only [CollatzResearch.WordTrace]
  refine ⟨28852292041135819966280231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19234861360757213310853487 28852292041135819966280231)
  ·
    refine ⟨43278438061703729949420347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28852292041135819966280231 43278438061703729949420347)
    ·
      refine ⟨64917657092555594924130521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43278438061703729949420347 64917657092555594924130521)
      ·
        refine ⟨48688242819416696193097891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64917657092555594924130521 48688242819416696193097891)
        ·
          refine ⟨73032364229125044289646837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48688242819416696193097891 73032364229125044289646837)
          ·
            refine ⟨6846784146480472902154391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73032364229125044289646837 6846784146480472902154391)
            ·
              refine ⟨10270176219720709353231587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846784146480472902154391 10270176219720709353231587)
              ·
                refine ⟨15405264329581064029847381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10270176219720709353231587 15405264329581064029847381)
                ·
                  refine ⟨90265220681139047049887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15405264329581064029847381 90265220681139047049887)
                  ·
                    rfl

theorem cell22_791059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_791059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791059 prefixEnd_791059 := by exact prefixLift 791059
  have htrace : WordTrace (prefixWord ++ tailWord_791059) baseStart_791059 baseEnd_791059 := by
    simpa [prefixWord, tailWord_791059, baseEnd_791059] using wordTrace_append hprefix tailTrace_791059
  have hstable : (prefixWord ++ tailWord_791059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791059).length < 2 ^ (prefixWord ++ tailWord_791059).sum := by decide
  have hdescent : baseEnd_791059 < baseStart_791059 := by decide
  rcases family_descends (prefixWord ++ tailWord_791059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791080 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_791080 : Nat := 118140960795 + 791080 * 2 ^ 59
def prefixEnd_791080 : Nat := 4983230072969 + 3 ^ 40 * 791080 * 2
def baseEnd_791080 : Nat := 270802850772580086374597

theorem tailTrace_791080 : CollatzResearch.WordTrace tailWord_791080 prefixEnd_791080 270802850772580086374597 := by
  unfold tailWord_791080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426528987029870276397347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19235371982706493701863129 14426528987029870276397347)
  ·
    refine ⟨21639793480544805414596021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14426528987029870276397347 21639793480544805414596021)
    ·
      refine ⟨2028730638801075507618377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21639793480544805414596021 2028730638801075507618377)
      ·
        refine ⟨1521547979100806630713783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2028730638801075507618377 1521547979100806630713783)
        ·
          refine ⟨2282321968651209946070675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521547979100806630713783 2282321968651209946070675)
          ·
            refine ⟨3423482952976814919106013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282321968651209946070675 3423482952976814919106013)
            ·
              refine ⟨1283806107366305594664755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3423482952976814919106013 1283806107366305594664755)
              ·
                refine ⟨1925709161049458391997133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283806107366305594664755 1925709161049458391997133)
                ·
                  refine ⟨722140935393546896998925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1925709161049458391997133 722140935393546896998925)
                  ·
                    refine ⟨270802850772580086374597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 722140935393546896998925 270802850772580086374597)
                    ·
                      rfl

theorem cell22_791080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_791080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791080 prefixEnd_791080 := by exact prefixLift 791080
  have htrace : WordTrace (prefixWord ++ tailWord_791080) baseStart_791080 baseEnd_791080 := by
    simpa [prefixWord, tailWord_791080, baseEnd_791080] using wordTrace_append hprefix tailTrace_791080
  have hstable : (prefixWord ++ tailWord_791080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791080).length < 2 ^ (prefixWord ++ tailWord_791080).sum := by decide
  have hdescent : baseEnd_791080 < baseStart_791080 := by decide
  rcases family_descends (prefixWord ++ tailWord_791080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791151 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 4, 4]
def baseStart_791151 : Nat := 118140960795 + 791151 * 2 ^ 59
def prefixEnd_791151 : Nat := 4983230072969 + 3 ^ 40 * 791151 * 2
def baseEnd_791151 : Nat := 270827155523559567849379

theorem tailTrace_791151 : CollatzResearch.WordTrace tailWord_791151 prefixEnd_791151 270827155523559567849379 := by
  unfold tailWord_791151
  simp only [CollatzResearch.WordTrace]
  refine ⟨28855647556802519678629307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19237098371201679785752871 28855647556802519678629307)
  ·
    refine ⟨43283471335203779517943961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28855647556802519678629307 43283471335203779517943961)
    ·
      refine ⟨32462603501402834638457971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43283471335203779517943961 32462603501402834638457971)
      ·
        refine ⟨48693905252104251957686957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32462603501402834638457971 48693905252104251957686957)
        ·
          refine ⟨18260214469539094484132609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48693905252104251957686957 18260214469539094484132609)
          ·
            refine ⟨13695160852154320863099457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18260214469539094484132609 13695160852154320863099457)
            ·
              refine ⟨10271370639115740647324593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13695160852154320863099457 10271370639115740647324593)
              ·
                refine ⟨7703527979336805485493445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10271370639115740647324593 7703527979336805485493445)
                ·
                  refine ⟨1444411496125651028530021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7703527979336805485493445 1444411496125651028530021)
                  ·
                    refine ⟨270827155523559567849379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444411496125651028530021 270827155523559567849379)
                    ·
                      rfl

theorem cell22_791151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_791151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791151 prefixEnd_791151 := by exact prefixLift 791151
  have htrace : WordTrace (prefixWord ++ tailWord_791151) baseStart_791151 baseEnd_791151 := by
    simpa [prefixWord, tailWord_791151, baseEnd_791151] using wordTrace_append hprefix tailTrace_791151
  have hstable : (prefixWord ++ tailWord_791151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791151).length < 2 ^ (prefixWord ++ tailWord_791151).sum := by decide
  have hdescent : baseEnd_791151 < baseStart_791151 := by decide
  rcases family_descends (prefixWord ++ tailWord_791151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791168 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_791168 : Nat := 118140960795 + 791168 * 2 ^ 59
def prefixEnd_791168 : Nat := 4983230072969 + 3 ^ 40 * 791168 * 2
def baseEnd_791168 : Nat := 270832974970977190174327

theorem tailTrace_791168 : CollatzResearch.WordTrace tailWord_791168 prefixEnd_791168 270832974970977190174327 := by
  unfold tailWord_791168
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428133798870465790999079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19237511731827287721332105 14428133798870465790999079)
  ·
    refine ⟨21642200698305698686498619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14428133798870465790999079 21642200698305698686498619)
    ·
      refine ⟨32463301047458548029747929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21642200698305698686498619 32463301047458548029747929)
      ·
        refine ⟨24347475785593911022310947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32463301047458548029747929 24347475785593911022310947)
        ·
          refine ⟨36521213678390866533466421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24347475785593911022310947 36521213678390866533466421)
          ·
            refine ⟨3423863782349143737512477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36521213678390866533466421 3423863782349143737512477)
            ·
              refine ⟨1283948918380928901567179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3423863782349143737512477 1283948918380928901567179)
              ·
                refine ⟨1925923377571393352350769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283948918380928901567179 1925923377571393352350769)
                ·
                  refine ⟨1444442533178545014263077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1925923377571393352350769 1444442533178545014263077)
                  ·
                    refine ⟨270832974970977190174327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444442533178545014263077 270832974970977190174327)
                    ·
                      rfl

theorem cell22_791168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_791168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791168 prefixEnd_791168 := by exact prefixLift 791168
  have htrace : WordTrace (prefixWord ++ tailWord_791168) baseStart_791168 baseEnd_791168 := by
    simpa [prefixWord, tailWord_791168, baseEnd_791168] using wordTrace_append hprefix tailTrace_791168
  have hstable : (prefixWord ++ tailWord_791168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791168).length < 2 ^ (prefixWord ++ tailWord_791168).sum := by decide
  have hdescent : baseEnd_791168 < baseStart_791168 := by decide
  rcases family_descends (prefixWord ++ tailWord_791168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791217 : List Nat := [1, 2, 2, 6, 1, 2, 2, 6]
def baseStart_791217 : Nat := 118140960795 + 791217 * 2 ^ 59
def prefixEnd_791217 : Nat := 4983230072969 + 3 ^ 40 * 791217 * 2
def baseEnd_791217 : Nat := 30094416519150821744353

theorem tailTrace_791217 : CollatzResearch.WordTrace tailWord_791217 prefixEnd_791217 30094416519150821744353 := by
  unfold tailWord_791217
  simp only [CollatzResearch.WordTrace]
  refine ⟨28858054774563412950531905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19238703183042275300354603 28858054774563412950531905)
  ·
    refine ⟨21643541080922559712898929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28858054774563412950531905 21643541080922559712898929)
    ·
      refine ⟨16232655810691919784674197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21643541080922559712898929 16232655810691919784674197)
      ·
        refine ⟨760905741126183739906603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16232655810691919784674197 760905741126183739906603)
        ·
          refine ⟨1141358611689275609859905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760905741126183739906603 1141358611689275609859905)
          ·
            refine ⟨856018958766956707394929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141358611689275609859905 856018958766956707394929)
            ·
              refine ⟨642014219075217530546197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856018958766956707394929 642014219075217530546197)
              ·
                refine ⟨30094416519150821744353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 642014219075217530546197 30094416519150821744353)
                ·
                  rfl

theorem cell22_791217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 6].length) (baseStart_791217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791217 prefixEnd_791217 := by exact prefixLift 791217
  have htrace : WordTrace (prefixWord ++ tailWord_791217) baseStart_791217 baseEnd_791217 := by
    simpa [prefixWord, tailWord_791217, baseEnd_791217] using wordTrace_append hprefix tailTrace_791217
  have hstable : (prefixWord ++ tailWord_791217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791217).length < 2 ^ (prefixWord ++ tailWord_791217).sum := by decide
  have hdescent : baseEnd_791217 < baseStart_791217 := by decide
  rcases family_descends (prefixWord ++ tailWord_791217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791232 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 1, 3]
def baseStart_791232 : Nat := 118140960795 + 791232 * 2 ^ 59
def prefixEnd_791232 : Nat := 4983230072969 + 3 ^ 40 * 791232 * 2
def baseEnd_791232 : Nat := 270854883478902356574131

theorem tailTrace_791232 : CollatzResearch.WordTrace tailWord_791232 prefixEnd_791232 270854883478902356574131 := by
  unfold tailWord_791232
  simp only [CollatzResearch.WordTrace]
  refine ⟨14429300934754535256163975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19239067913006047008218633 14429300934754535256163975)
  ·
    refine ⟨21643951402131802884245963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14429300934754535256163975 21643951402131802884245963)
    ·
      refine ⟨32465927103197704326368945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21643951402131802884245963 32465927103197704326368945)
      ·
        refine ⟨24349445327398278244776709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32465927103197704326368945 24349445327398278244776709)
        ·
          refine ⟨4565520998887177170895633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24349445327398278244776709 4565520998887177170895633)
          ·
            refine ⟨3424140749165382878171725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4565520998887177170895633 3424140749165382878171725)
            ·
              refine ⟨1284052780937018579314397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3424140749165382878171725 1284052780937018579314397)
              ·
                refine ⟨481519792851381967242899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1284052780937018579314397 481519792851381967242899)
                ·
                  refine ⟨722279689277072950864349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481519792851381967242899 722279689277072950864349)
                  ·
                    refine ⟨270854883478902356574131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 722279689277072950864349 270854883478902356574131)
                    ·
                      rfl

theorem cell22_791232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_791232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791232 prefixEnd_791232 := by exact prefixLift 791232
  have htrace : WordTrace (prefixWord ++ tailWord_791232) baseStart_791232 baseEnd_791232 := by
    simpa [prefixWord, tailWord_791232, baseEnd_791232] using wordTrace_append hprefix tailTrace_791232
  have hstable : (prefixWord ++ tailWord_791232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791232).length < 2 ^ (prefixWord ++ tailWord_791232).sum := by decide
  have hdescent : baseEnd_791232 < baseStart_791232 := by decide
  rcases family_descends (prefixWord ++ tailWord_791232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791258 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_791258 : Nat := 118140960795 + 791258 * 2 ^ 59
def prefixEnd_791258 : Nat := 4983230072969 + 3 ^ 40 * 791258 * 2
def baseEnd_791258 : Nat := 270863783810246955424051

theorem tailTrace_791258 : CollatzResearch.WordTrace tailWord_791258 prefixEnd_791258 270863783810246955424051 := by
  unfold tailWord_791258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214887541853719238193607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19239700111609917968516285 7214887541853719238193607)
  ·
    refine ⟨10822331312780578857290411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7214887541853719238193607 10822331312780578857290411)
    ·
      refine ⟨16233496969170868285935617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822331312780578857290411 16233496969170868285935617)
      ·
        refine ⟨12175122726878151214451713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16233496969170868285935617 12175122726878151214451713)
        ·
          refine ⟨9131342045158613410838785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12175122726878151214451713 9131342045158613410838785)
          ·
            refine ⟨6848506533868960058129089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9131342045158613410838785 6848506533868960058129089)
            ·
              refine ⟨5136379900401720043596817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848506533868960058129089 5136379900401720043596817)
              ·
                refine ⟨3852284925301290032697613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136379900401720043596817 3852284925301290032697613)
                ·
                  refine ⟨1444606846987983762261605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3852284925301290032697613 1444606846987983762261605)
                  ·
                    refine ⟨270863783810246955424051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444606846987983762261605 270863783810246955424051)
                    ·
                      rfl

theorem cell22_791258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_791258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791258 prefixEnd_791258 := by exact prefixLift 791258
  have htrace : WordTrace (prefixWord ++ tailWord_791258) baseStart_791258 baseEnd_791258 := by
    simpa [prefixWord, tailWord_791258, baseEnd_791258] using wordTrace_append hprefix tailTrace_791258
  have hstable : (prefixWord ++ tailWord_791258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791258).length < 2 ^ (prefixWord ++ tailWord_791258).sum := by decide
  have hdescent : baseEnd_791258 < baseStart_791258 := by decide
  rcases family_descends (prefixWord ++ tailWord_791258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791288 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_791288 : Nat := 118140960795 + 791288 * 2 ^ 59
def prefixEnd_791288 : Nat := 4983230072969 + 3 ^ 40 * 791288 * 2
def baseEnd_791288 : Nat := 270874053423336877173959

theorem tailTrace_791288 : CollatzResearch.WordTrace tailWord_791288 prefixEnd_791288 270874053423336877173959 := by
  unfold tailWord_791288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430322178653096038183259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19240429571537461384244345 14430322178653096038183259)
  ·
    refine ⟨21645483267979644057274889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14430322178653096038183259 21645483267979644057274889)
    ·
      refine ⟨16234112450984733042956167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21645483267979644057274889 16234112450984733042956167)
      ·
        refine ⟨24351168676477099564434251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16234112450984733042956167 24351168676477099564434251)
        ·
          refine ⟨36526753014715649346651377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24351168676477099564434251 36526753014715649346651377)
          ·
            refine ⟨27395064761036737009988533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36526753014715649346651377 27395064761036737009988533)
            ·
              refine ⟨2568287321347194094686425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27395064761036737009988533 2568287321347194094686425)
              ·
                refine ⟨1926215491010395571014819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568287321347194094686425 1926215491010395571014819)
                ·
                  refine ⟨2889323236515593356522229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926215491010395571014819 2889323236515593356522229)
                  ·
                    refine ⟨270874053423336877173959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2889323236515593356522229 270874053423336877173959)
                    ·
                      rfl

theorem cell22_791288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_791288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791288 prefixEnd_791288 := by exact prefixLift 791288
  have htrace : WordTrace (prefixWord ++ tailWord_791288) baseStart_791288 baseEnd_791288 := by
    simpa [prefixWord, tailWord_791288, baseEnd_791288] using wordTrace_append hprefix tailTrace_791288
  have hstable : (prefixWord ++ tailWord_791288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791288).length < 2 ^ (prefixWord ++ tailWord_791288).sum := by decide
  have hdescent : baseEnd_791288 < baseStart_791288 := by decide
  rcases family_descends (prefixWord ++ tailWord_791288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791292 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_791292 : Nat := 118140960795 + 791292 * 2 ^ 59
def prefixEnd_791292 : Nat := 4983230072969 + 3 ^ 40 * 791292 * 2
def baseEnd_791292 : Nat := 270875422705082200073947

theorem tailTrace_791292 : CollatzResearch.WordTrace tailWord_791292 prefixEnd_791292 270875422705082200073947 := by
  unfold tailWord_791292
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430395124645850379756065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19240526832861133839674753 14430395124645850379756065)
  ·
    refine ⟨10822796343484387784817049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14430395124645850379756065 10822796343484387784817049)
    ·
      refine ⟨8117097257613290838612787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10822796343484387784817049 8117097257613290838612787)
      ·
        refine ⟨12175645886419936257919181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8117097257613290838612787 12175645886419936257919181)
        ·
          refine ⟨4565867207407476096719693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12175645886419936257919181 4565867207407476096719693)
          ·
            refine ⟨1712200202777803536269885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4565867207407476096719693 1712200202777803536269885)
            ·
              refine ⟨642075076041676326101207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1712200202777803536269885 642075076041676326101207)
              ·
                refine ⟨963112614062514489151811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642075076041676326101207 963112614062514489151811)
                ·
                  refine ⟨1444668921093771733727717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963112614062514489151811 1444668921093771733727717)
                  ·
                    refine ⟨270875422705082200073947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1444668921093771733727717 270875422705082200073947)
                    ·
                      rfl

theorem cell22_791292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_791292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791292 prefixEnd_791292 := by exact prefixLift 791292
  have htrace : WordTrace (prefixWord ++ tailWord_791292) baseStart_791292 baseEnd_791292 := by
    simpa [prefixWord, tailWord_791292, baseEnd_791292] using wordTrace_append hprefix tailTrace_791292
  have hstable : (prefixWord ++ tailWord_791292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791292).length < 2 ^ (prefixWord ++ tailWord_791292).sum := by decide
  have hdescent : baseEnd_791292 < baseStart_791292 := by decide
  rcases family_descends (prefixWord ++ tailWord_791292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791305 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_791305 : Nat := 118140960795 + 791305 * 2 ^ 59
def prefixEnd_791305 : Nat := 4983230072969 + 3 ^ 40 * 791305 * 2
def baseEnd_791305 : Nat := 270879872870754499498907

theorem tailTrace_791305 : CollatzResearch.WordTrace tailWord_791305 prefixEnd_791305 270879872870754499498907 := by
  unfold tailWord_791305
  simp only [CollatzResearch.WordTrace]
  refine ⟨28861264398244603979735369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19240842932163069319823579 28861264398244603979735369)
  ·
    refine ⟨21645948298683452984801527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28861264398244603979735369 21645948298683452984801527)
    ·
      refine ⟨32468922448025179477202291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21645948298683452984801527 32468922448025179477202291)
      ·
        refine ⟨48703383672037769215803437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32468922448025179477202291 48703383672037769215803437)
        ·
          refine ⟨18263768877014163455926289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48703383672037769215803437 18263768877014163455926289)
          ·
            refine ⟨13697826657760622591944717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18263768877014163455926289 13697826657760622591944717)
            ·
              refine ⟨5136684996660233471979269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13697826657760622591944717 5136684996660233471979269)
              ·
                refine ⟨963128436873793775996113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5136684996660233471979269 963128436873793775996113)
                ·
                  refine ⟨722346327655345331997085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 963128436873793775996113 722346327655345331997085)
                  ·
                    refine ⟨270879872870754499498907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 722346327655345331997085 270879872870754499498907)
                    ·
                      rfl

theorem cell22_791305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_791305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791305 prefixEnd_791305 := by exact prefixLift 791305
  have htrace : WordTrace (prefixWord ++ tailWord_791305) baseStart_791305 baseEnd_791305 := by
    simpa [prefixWord, tailWord_791305, baseEnd_791305] using wordTrace_append hprefix tailTrace_791305
  have hstable : (prefixWord ++ tailWord_791305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791305).length < 2 ^ (prefixWord ++ tailWord_791305).sum := by decide
  have hdescent : baseEnd_791305 < baseStart_791305 := by decide
  rcases family_descends (prefixWord ++ tailWord_791305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791341 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 4]
def baseStart_791341 : Nat := 118140960795 + 791341 * 2 ^ 59
def prefixEnd_791341 : Nat := 4983230072969 + 3 ^ 40 * 791341 * 2
def baseEnd_791341 : Nat := 90297398802154135199599

theorem tailTrace_791341 : CollatzResearch.WordTrace tailWord_791341 prefixEnd_791341 90297398802154135199599 := by
  unfold tailWord_791341
  simp only [CollatzResearch.WordTrace]
  refine ⟨28862577426114182128045877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19241718284076121418697251 28862577426114182128045877)
  ·
    refine ⟨2705866633698204574504301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28862577426114182128045877 2705866633698204574504301)
    ·
      refine ⟨1014699987636826715439113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2705866633698204574504301 1014699987636826715439113)
      ·
        refine ⟨761024990727620036579335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1014699987636826715439113 761024990727620036579335)
        ·
          refine ⟨1141537486091430054869003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761024990727620036579335 1141537486091430054869003)
          ·
            refine ⟨1712306229137145082303505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141537486091430054869003 1712306229137145082303505)
            ·
              refine ⟨1284229671852858811727629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712306229137145082303505 1284229671852858811727629)
              ·
                refine ⟨481586126944822054397861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1284229671852858811727629 481586126944822054397861)
                ·
                  refine ⟨90297398802154135199599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481586126944822054397861 90297398802154135199599)
                  ·
                    rfl

theorem cell22_791341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_791341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791341 prefixEnd_791341 := by exact prefixLift 791341
  have htrace : WordTrace (prefixWord ++ tailWord_791341) baseStart_791341 baseEnd_791341 := by
    simpa [prefixWord, tailWord_791341, baseEnd_791341] using wordTrace_append hprefix tailTrace_791341
  have hstable : (prefixWord ++ tailWord_791341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791341).length < 2 ^ (prefixWord ++ tailWord_791341).sum := by decide
  have hdescent : baseEnd_791341 < baseStart_791341 := by decide
  rcases family_descends (prefixWord ++ tailWord_791341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791363 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 7]
def baseStart_791363 : Nat := 118140960795 + 791363 * 2 ^ 59
def prefixEnd_791363 : Nat := 4983230072969 + 3 ^ 40 * 791363 * 2
def baseEnd_791363 : Nat := 90299909152020560516243

theorem tailTrace_791363 : CollatzResearch.WordTrace tailWord_791363 prefixEnd_791363 90299909152020560516243 := by
  unfold tailWord_791363
  simp only [CollatzResearch.WordTrace]
  refine ⟨28863379832034479885346743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19242253221356319923564495 28863379832034479885346743)
  ·
    refine ⟨43295069748051719828020115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28863379832034479885346743 43295069748051719828020115)
    ·
      refine ⟨64942604622077579742030173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43295069748051719828020115 64942604622077579742030173)
      ·
        refine ⟨24353476733279092403261315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64942604622077579742030173 24353476733279092403261315)
        ·
          refine ⟨36530215099918638604891973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24353476733279092403261315 36530215099918638604891973)
          ·
            refine ⟨6849415331234744738417245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36530215099918638604891973 6849415331234744738417245)
            ·
              refine ⟨2568530749213029276906467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6849415331234744738417245 2568530749213029276906467)
              ·
                refine ⟨3852796123819543915359701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568530749213029276906467 3852796123819543915359701)
                ·
                  refine ⟨90299909152020560516243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3852796123819543915359701 90299909152020560516243)
                  ·
                    rfl

theorem cell22_791363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_791363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791363 prefixEnd_791363 := by exact prefixLift 791363
  have htrace : WordTrace (prefixWord ++ tailWord_791363) baseStart_791363 baseEnd_791363 := by
    simpa [prefixWord, tailWord_791363, baseEnd_791363] using wordTrace_append hprefix tailTrace_791363
  have hstable : (prefixWord ++ tailWord_791363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791363).length < 2 ^ (prefixWord ++ tailWord_791363).sum := by decide
  have hdescent : baseEnd_791363 < baseStart_791363 := by decide
  rcases family_descends (prefixWord ++ tailWord_791363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791408 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_791408 : Nat := 118140960795 + 791408 * 2 ^ 59
def prefixEnd_791408 : Nat := 4983230072969 + 3 ^ 40 * 791408 * 2
def baseEnd_791408 : Nat := 90305043958565521391197

theorem tailTrace_791408 : CollatzResearch.WordTrace tailWord_791408 prefixEnd_791408 90305043958565521391197 := by
  unfold tailWord_791408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14432510558435726285367439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19243347411247635047156585 14432510558435726285367439)
  ·
    refine ⟨21648765837653589428051159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14432510558435726285367439 21648765837653589428051159)
    ·
      refine ⟨32473148756480384142076739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21648765837653589428051159 32473148756480384142076739)
      ·
        refine ⟨48709723134720576213115109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32473148756480384142076739 48709723134720576213115109)
        ·
          refine ⟨9133073087760108039959083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48709723134720576213115109 9133073087760108039959083)
          ·
            refine ⟨13699609631640162059938625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9133073087760108039959083 13699609631640162059938625)
            ·
              refine ⟨10274707223730121544953969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13699609631640162059938625 10274707223730121544953969)
              ·
                refine ⟨7706030417797591158715477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10274707223730121544953969 7706030417797591158715477)
                ·
                  refine ⟨90305043958565521391197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7706030417797591158715477 90305043958565521391197)
                  ·
                    rfl

theorem cell22_791408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_791408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791408 prefixEnd_791408 := by exact prefixLift 791408
  have htrace : WordTrace (prefixWord ++ tailWord_791408) baseStart_791408 baseEnd_791408 := by
    simpa [prefixWord, tailWord_791408, baseEnd_791408] using wordTrace_append hprefix tailTrace_791408
  have hstable : (prefixWord ++ tailWord_791408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791408).length < 2 ^ (prefixWord ++ tailWord_791408).sum := by decide
  have hdescent : baseEnd_791408 < baseStart_791408 := by decide
  rcases family_descends (prefixWord ++ tailWord_791408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791457 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_791457 : Nat := 118140960795 + 791457 * 2 ^ 59
def prefixEnd_791457 : Nat := 4983230072969 + 3 ^ 40 * 791457 * 2
def baseEnd_791457 : Nat := 270931905577076769698441

theorem tailTrace_791457 : CollatzResearch.WordTrace tailWord_791457 prefixEnd_791457 270931905577076769698441 := by
  unfold tailWord_791457
  simp only [CollatzResearch.WordTrace]
  refine ⟨28866808293693933939268625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19244538862462622626179083 28866808293693933939268625)
  ·
    refine ⟨21650106220270450454451469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28866808293693933939268625 21650106220270450454451469)
    ·
      refine ⟨8118789832601418920419301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21650106220270450454451469 8118789832601418920419301)
      ·
        refine ⟨1522273093612766047578619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8118789832601418920419301 1522273093612766047578619)
        ·
          refine ⟨2283409640419149071367929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522273093612766047578619 2283409640419149071367929)
          ·
            refine ⟨1712557230314361803525947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283409640419149071367929 1712557230314361803525947)
            ·
              refine ⟨2568835845471542705288921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712557230314361803525947 2568835845471542705288921)
              ·
                refine ⟨1926626884103657028966691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568835845471542705288921 1926626884103657028966691)
                ·
                  refine ⟨2889940326155485543450037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1926626884103657028966691 2889940326155485543450037)
                  ·
                    refine ⟨270931905577076769698441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2889940326155485543450037 270931905577076769698441)
                    ·
                      rfl

theorem cell22_791457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_791457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791457 prefixEnd_791457 := by exact prefixLift 791457
  have htrace : WordTrace (prefixWord ++ tailWord_791457) baseStart_791457 baseEnd_791457 := by
    simpa [prefixWord, tailWord_791457, baseEnd_791457] using wordTrace_append hprefix tailTrace_791457
  have hstable : (prefixWord ++ tailWord_791457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791457).length < 2 ^ (prefixWord ++ tailWord_791457).sum := by decide
  have hdescent : baseEnd_791457 < baseStart_791457 := by decide
  rcases family_descends (prefixWord ++ tailWord_791457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791476 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 4]
def baseStart_791476 : Nat := 118140960795 + 791476 * 2 ^ 59
def prefixEnd_791476 : Nat := 4983230072969 + 3 ^ 40 * 791476 * 2
def baseEnd_791476 : Nat := 90312803221789017824461

theorem tailTrace_791476 : CollatzResearch.WordTrace tailWord_791476 prefixEnd_791476 90312803221789017824461 := by
  unfold tailWord_791476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433750640312550092105141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19245000853750066789473521 14433750640312550092105141)
  ·
    refine ⟨1353164122529301571134857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14433750640312550092105141 1353164122529301571134857)
    ·
      refine ⟨1014873091896976178351143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1353164122529301571134857 1014873091896976178351143)
      ·
        refine ⟨1522309637845464267526715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014873091896976178351143 1522309637845464267526715)
        ·
          refine ⟨2283464456768196401290073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522309637845464267526715 2283464456768196401290073)
          ·
            refine ⟨1712598342576147300967555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283464456768196401290073 1712598342576147300967555)
            ·
              refine ⟨2568897513864220951451333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712598342576147300967555 2568897513864220951451333)
              ·
                refine ⟨481668283849541428397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2568897513864220951451333 481668283849541428397125)
                ·
                  refine ⟨90312803221789017824461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481668283849541428397125 90312803221789017824461)
                  ·
                    rfl

theorem cell22_791476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_791476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791476 prefixEnd_791476 := by exact prefixLift 791476
  have htrace : WordTrace (prefixWord ++ tailWord_791476) baseStart_791476 baseEnd_791476 := by
    simpa [prefixWord, tailWord_791476, baseEnd_791476] using wordTrace_append hprefix tailTrace_791476
  have hstable : (prefixWord ++ tailWord_791476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791476).length < 2 ^ (prefixWord ++ tailWord_791476).sum := by decide
  have hdescent : baseEnd_791476 < baseStart_791476 := by decide
  rcases family_descends (prefixWord ++ tailWord_791476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791500 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_791500 : Nat := 118140960795 + 791500 * 2 ^ 59
def prefixEnd_791500 : Nat := 4983230072969 + 3 ^ 40 * 791500 * 2
def baseEnd_791500 : Nat := 270946625355838990873309

theorem tailTrace_791500 : CollatzResearch.WordTrace tailWord_791500 prefixEnd_791500 270946625355838990873309 := by
  unfold tailWord_791500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14434188316269076141541977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19245584421692101522055969 14434188316269076141541977)
  ·
    refine ⟨10825641237201807106156483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14434188316269076141541977 10825641237201807106156483)
    ·
      refine ⟨16238461855802710659234725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825641237201807106156483 16238461855802710659234725)
      ·
        refine ⟨3044711597963008248606511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16238461855802710659234725 3044711597963008248606511)
        ·
          refine ⟨4567067396944512372909767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044711597963008248606511 4567067396944512372909767)
          ·
            refine ⟨6850601095416768559364651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4567067396944512372909767 6850601095416768559364651)
            ·
              refine ⟨10275901643125152839046977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6850601095416768559364651 10275901643125152839046977)
              ·
                refine ⟨7706926232343864629285233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10275901643125152839046977 7706926232343864629285233)
                ·
                  refine ⟨5780194674257898471963925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7706926232343864629285233 5780194674257898471963925)
                  ·
                    refine ⟨270946625355838990873309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5780194674257898471963925 270946625355838990873309)
                    ·
                      rfl

theorem cell22_791500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_791500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791500 prefixEnd_791500 := by exact prefixLift 791500
  have htrace : WordTrace (prefixWord ++ tailWord_791500) baseStart_791500 baseEnd_791500 := by
    simpa [prefixWord, tailWord_791500, baseEnd_791500] using wordTrace_append hprefix tailTrace_791500
  have hstable : (prefixWord ++ tailWord_791500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791500).length < 2 ^ (prefixWord ++ tailWord_791500).sum := by decide
  have hdescent : baseEnd_791500 < baseStart_791500 := by decide
  rcases family_descends (prefixWord ++ tailWord_791500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791502 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_791502 : Nat := 118140960795 + 791502 * 2 ^ 59
def prefixEnd_791502 : Nat := 4983230072969 + 3 ^ 40 * 791502 * 2
def baseEnd_791502 : Nat := 270947309996711652323303

theorem tailTrace_791502 : CollatzResearch.WordTrace tailWord_791502 prefixEnd_791502 270947309996711652323303 := by
  unfold tailWord_791502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608556197316363328082095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19245633052353937749771173 3608556197316363328082095)
  ·
    refine ⟨5412834295974544992123143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608556197316363328082095 5412834295974544992123143)
    ·
      refine ⟨8119251443961817488184715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412834295974544992123143 8119251443961817488184715)
      ·
        refine ⟨12178877165942726232277073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119251443961817488184715 12178877165942726232277073)
        ·
          refine ⟨9134157874457044674207805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12178877165942726232277073 9134157874457044674207805)
          ·
            refine ⟨3425309202921391752827927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9134157874457044674207805 3425309202921391752827927)
            ·
              refine ⟨5137963804382087629241891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425309202921391752827927 5137963804382087629241891)
              ·
                refine ⟨7706945706573131443862837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137963804382087629241891 7706945706573131443862837)
                ·
                  refine ⟨722526159991231072862141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7706945706573131443862837 722526159991231072862141)
                  ·
                    refine ⟨270947309996711652323303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 722526159991231072862141 270947309996711652323303)
                    ·
                      rfl

theorem cell22_791502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_791502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791502 prefixEnd_791502 := by exact prefixLift 791502
  have htrace : WordTrace (prefixWord ++ tailWord_791502) baseStart_791502 baseEnd_791502 := by
    simpa [prefixWord, tailWord_791502, baseEnd_791502] using wordTrace_append hprefix tailTrace_791502
  have hstable : (prefixWord ++ tailWord_791502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791502).length < 2 ^ (prefixWord ++ tailWord_791502).sum := by decide
  have hdescent : baseEnd_791502 < baseStart_791502 := by decide
  rcases family_descends (prefixWord ++ tailWord_791502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791635 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_791635 : Nat := 118140960795 + 791635 * 2 ^ 59
def prefixEnd_791635 : Nat := 4983230072969 + 3 ^ 40 * 791635 * 2
def baseEnd_791635 : Nat := 270992838614743638747895

theorem tailTrace_791635 : CollatzResearch.WordTrace tailWord_791635 prefixEnd_791635 270992838614743638747895 := by
  unfold tailWord_791635
  simp only [CollatzResearch.WordTrace]
  refine ⟨28873300487049070339248359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19248866991366046892832239 28873300487049070339248359)
  ·
    refine ⟨43309950730573605508872539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28873300487049070339248359 43309950730573605508872539)
    ·
      refine ⟨64964926095860408263308809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43309950730573605508872539 64964926095860408263308809)
      ·
        refine ⟨48723694571895306197481607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64964926095860408263308809 48723694571895306197481607)
        ·
          refine ⟨73085541857842959296222411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48723694571895306197481607 73085541857842959296222411)
          ·
            refine ⟨109628312786764438944333617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73085541857842959296222411 109628312786764438944333617)
            ·
              refine ⟨82221234590073329208250213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109628312786764438944333617 82221234590073329208250213)
              ·
                refine ⟨15416481485638749226546915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82221234590073329208250213 15416481485638749226546915)
                ·
                  refine ⟨23124722228458123839820373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15416481485638749226546915 23124722228458123839820373)
                  ·
                    refine ⟨270992838614743638747895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23124722228458123839820373 270992838614743638747895)
                    ·
                      rfl

theorem cell22_791635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_791635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791635 prefixEnd_791635 := by exact prefixLift 791635
  have htrace : WordTrace (prefixWord ++ tailWord_791635) baseStart_791635 baseEnd_791635 := by
    simpa [prefixWord, tailWord_791635, baseEnd_791635] using wordTrace_append hprefix tailTrace_791635
  have hstable : (prefixWord ++ tailWord_791635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791635).length < 2 ^ (prefixWord ++ tailWord_791635).sum := by decide
  have hdescent : baseEnd_791635 < baseStart_791635 := by decide
  rcases family_descends (prefixWord ++ tailWord_791635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791645 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 4]
def baseStart_791645 : Nat := 118140960795 + 791645 * 2 ^ 59
def prefixEnd_791645 : Nat := 4983230072969 + 3 ^ 40 * 791645 * 2
def baseEnd_791645 : Nat := 90332087273035648665955

theorem tailTrace_791645 : CollatzResearch.WordTrace tailWord_791645 prefixEnd_791645 90332087273035648665955 := by
  unfold tailWord_791645
  simp only [CollatzResearch.WordTrace]
  refine ⟨28873665217012842047112389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19249110144675228031408259 28873665217012842047112389)
  ·
    refine ⟨5413812228189907883833573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28873665217012842047112389 5413812228189907883833573)
    ·
      refine ⟨1015089792785607728218795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5413812228189907883833573 1015089792785607728218795)
      ·
        refine ⟨1522634689178411592328193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015089792785607728218795 1522634689178411592328193)
        ·
          refine ⟨1141976016883808694246145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1522634689178411592328193 1141976016883808694246145)
          ·
            refine ⟨856482012662856520684609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141976016883808694246145 856482012662856520684609)
            ·
              refine ⟨642361509497142390513457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856482012662856520684609 642361509497142390513457)
              ·
                refine ⟨481771132122856792885093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642361509497142390513457 481771132122856792885093)
                ·
                  refine ⟨90332087273035648665955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481771132122856792885093 90332087273035648665955)
                  ·
                    rfl

theorem cell22_791645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_791645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791645 prefixEnd_791645 := by exact prefixLift 791645
  have htrace : WordTrace (prefixWord ++ tailWord_791645) baseStart_791645 baseEnd_791645 := by
    simpa [prefixWord, tailWord_791645, baseEnd_791645] using wordTrace_append hprefix tailTrace_791645
  have hstable : (prefixWord ++ tailWord_791645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791645).length < 2 ^ (prefixWord ++ tailWord_791645).sum := by decide
  have hdescent : baseEnd_791645 < baseStart_791645 := by decide
  rcases family_descends (prefixWord ++ tailWord_791645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791656 : List Nat := [2, 1, 4, 4, 1, 2, 1, 7]
def baseStart_791656 : Nat := 118140960795 + 791656 * 2 ^ 59
def prefixEnd_791656 : Nat := 4983230072969 + 3 ^ 40 * 791656 * 2
def baseEnd_791656 : Nat := 30111114149322953774759

theorem tailTrace_791656 : CollatzResearch.WordTrace tailWord_791656 prefixEnd_791656 30111114149322953774759 := by
  unfold tailWord_791656
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437033209986495462881411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19249377613315327283841881 14437033209986495462881411)
  ·
    refine ⟨21655549814979743194322117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437033209986495462881411 21655549814979743194322117)
    ·
      refine ⟨4060415590308701848935397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21655549814979743194322117 4060415590308701848935397)
      ·
        refine ⟨761327923182881596675387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4060415590308701848935397 761327923182881596675387)
        ·
          refine ⟨1141991884774322395013081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761327923182881596675387 1141991884774322395013081)
          ·
            refine ⟨856493913580741796259811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141991884774322395013081 856493913580741796259811)
            ·
              refine ⟨1284740870371112694389717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856493913580741796259811 1284740870371112694389717)
              ·
                refine ⟨30111114149322953774759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1284740870371112694389717 30111114149322953774759)
                ·
                  rfl

theorem cell22_791656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_791656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791656 prefixEnd_791656 := by exact prefixLift 791656
  have htrace : WordTrace (prefixWord ++ tailWord_791656) baseStart_791656 baseEnd_791656 := by
    simpa [prefixWord, tailWord_791656, baseEnd_791656] using wordTrace_append hprefix tailTrace_791656
  have hstable : (prefixWord ++ tailWord_791656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791656).length < 2 ^ (prefixWord ++ tailWord_791656).sum := by decide
  have hdescent : baseEnd_791656 < baseStart_791656 := by decide
  rcases family_descends (prefixWord ++ tailWord_791656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791729 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 6]
def baseStart_791729 : Nat := 118140960795 + 791729 * 2 ^ 59
def prefixEnd_791729 : Nat := 4983230072969 + 3 ^ 40 * 791729 * 2
def baseEnd_791729 : Nat := 90341672245252908965869

theorem tailTrace_791729 : CollatzResearch.WordTrace tailWord_791729 prefixEnd_791729 90341672245252908965869 := by
  unfold tailWord_791729
  simp only [CollatzResearch.WordTrace]
  refine ⟨28876728948708524393170241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19251152632472349595446827 28876728948708524393170241)
  ·
    refine ⟨21657546711531393294877681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28876728948708524393170241 21657546711531393294877681)
    ·
      refine ⟨16243160033648544971158261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21657546711531393294877681 16243160033648544971158261)
      ·
        refine ⟨1522796253154551091046087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16243160033648544971158261 1522796253154551091046087)
        ·
          refine ⟨2284194379731826636569131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522796253154551091046087 2284194379731826636569131)
          ·
            refine ⟨3426291569597739954853697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284194379731826636569131 3426291569597739954853697)
            ·
              refine ⟨2569718677198304966140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426291569597739954853697 2569718677198304966140273)
              ·
                refine ⟨1927289007898728724605205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569718677198304966140273 1927289007898728724605205)
                ·
                  refine ⟨90341672245252908965869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1927289007898728724605205 90341672245252908965869)
                  ·
                    rfl

theorem cell22_791729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_791729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791729 prefixEnd_791729 := by exact prefixLift 791729
  have htrace : WordTrace (prefixWord ++ tailWord_791729) baseStart_791729 baseEnd_791729 := by
    simpa [prefixWord, tailWord_791729, baseEnd_791729] using wordTrace_append hprefix tailTrace_791729
  have hstable : (prefixWord ++ tailWord_791729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791729).length < 2 ^ (prefixWord ++ tailWord_791729).sum := by decide
  have hdescent : baseEnd_791729 < baseStart_791729 := by decide
  rcases family_descends (prefixWord ++ tailWord_791729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791819 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 5]
def baseStart_791819 : Nat := 118140960795 + 791819 * 2 ^ 59
def prefixEnd_791819 : Nat := 4983230072969 + 3 ^ 40 * 791819 * 2
def baseEnd_791819 : Nat := 90351941858342830715777

theorem tailTrace_791819 : CollatzResearch.WordTrace tailWord_791819 prefixEnd_791819 90351941858342830715777 := by
  unfold tailWord_791819
  simp only [CollatzResearch.WordTrace]
  refine ⟨28880011518382469763946511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19253341012254979842631007 28880011518382469763946511)
  ·
    refine ⟨43320017277573704645919767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28880011518382469763946511 43320017277573704645919767)
    ·
      refine ⟨64980025916360556968879651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43320017277573704645919767 64980025916360556968879651)
      ·
        refine ⟨97470038874540835453319477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64980025916360556968879651 97470038874540835453319477)
        ·
          refine ⟨9137816144488203323748701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97470038874540835453319477 9137816144488203323748701)
          ·
            refine ⟨3426681054183076246405763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9137816144488203323748701 3426681054183076246405763)
            ·
              refine ⟨5140021581274614369608645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426681054183076246405763 5140021581274614369608645)
              ·
                refine ⟨963754046488990194301621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5140021581274614369608645 963754046488990194301621)
                ·
                  refine ⟨90351941858342830715777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 963754046488990194301621 90351941858342830715777)
                  ·
                    rfl

theorem cell22_791819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 5].length) (baseStart_791819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791819 prefixEnd_791819 := by exact prefixLift 791819
  have htrace : WordTrace (prefixWord ++ tailWord_791819) baseStart_791819 baseEnd_791819 := by
    simpa [prefixWord, tailWord_791819, baseEnd_791819] using wordTrace_append hprefix tailTrace_791819
  have hstable : (prefixWord ++ tailWord_791819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791819).length < 2 ^ (prefixWord ++ tailWord_791819).sum := by decide
  have hdescent : baseEnd_791819 < baseStart_791819 := by decide
  rcases family_descends (prefixWord ++ tailWord_791819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791834 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_791834 : Nat := 118140960795 + 791834 * 2 ^ 59
def prefixEnd_791834 : Nat := 4983230072969 + 3 ^ 40 * 791834 * 2
def baseEnd_791834 : Nat := 271060960381573453022285

theorem tailTrace_791834 : CollatzResearch.WordTrace tailWord_791834 prefixEnd_791834 271060960381573453022285 := by
  unfold tailWord_791834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220139653332031831435639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19253705742218751550495037 7220139653332031831435639)
  ·
    refine ⟨10830209479998047747153459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7220139653332031831435639 10830209479998047747153459)
    ·
      refine ⟨16245314219997071620730189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10830209479998047747153459 16245314219997071620730189)
      ·
        refine ⟨6091992832498901857773821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16245314219997071620730189 6091992832498901857773821)
        ·
          refine ⟨2284497312187088196665183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6091992832498901857773821 2284497312187088196665183)
          ·
            refine ⟨3426745968280632294997775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284497312187088196665183 3426745968280632294997775)
            ·
              refine ⟨5140118952420948442496663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426745968280632294997775 5140118952420948442496663)
              ·
                refine ⟨7710178428631422663744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140118952420948442496663 7710178428631422663744995)
                ·
                  refine ⟨11565267642947133995617493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7710178428631422663744995 11565267642947133995617493)
                  ·
                    refine ⟨271060960381573453022285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11565267642947133995617493 271060960381573453022285)
                    ·
                      rfl

theorem cell22_791834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_791834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791834 prefixEnd_791834 := by exact prefixLift 791834
  have htrace : WordTrace (prefixWord ++ tailWord_791834) baseStart_791834 baseEnd_791834 := by
    simpa [prefixWord, tailWord_791834, baseEnd_791834] using wordTrace_append hprefix tailTrace_791834
  have hstable : (prefixWord ++ tailWord_791834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791834).length < 2 ^ (prefixWord ++ tailWord_791834).sum := by decide
  have hdescent : baseEnd_791834 < baseStart_791834 := by decide
  rcases family_descends (prefixWord ++ tailWord_791834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791866 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_791866 : Nat := 118140960795 + 791866 * 2 ^ 59
def prefixEnd_791866 : Nat := 4983230072969 + 3 ^ 40 * 791866 * 2
def baseEnd_791866 : Nat := 271071914635536036222187

theorem tailTrace_791866 : CollatzResearch.WordTrace tailWord_791866 prefixEnd_791866 271071914635536036222187 := by
  unfold tailWord_791866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220431437303049197726863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19254483832808131193938301 7220431437303049197726863)
  ·
    refine ⟨10830647155954573796590295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7220431437303049197726863 10830647155954573796590295)
    ·
      refine ⟨16245970733931860694885443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10830647155954573796590295 16245970733931860694885443)
      ·
        refine ⟨24368956100897791042328165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16245970733931860694885443 24368956100897791042328165)
        ·
          refine ⟨4569179268918335820436531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24368956100897791042328165 4569179268918335820436531)
          ·
            refine ⟨6853768903377503730654797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569179268918335820436531 6853768903377503730654797)
            ·
              refine ⟨2570163338766563898995549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6853768903377503730654797 2570163338766563898995549)
              ·
                refine ⟨963811252037461462123331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2570163338766563898995549 963811252037461462123331)
                ·
                  refine ⟨1445716878056192193184997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963811252037461462123331 1445716878056192193184997)
                  ·
                    refine ⟨271071914635536036222187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1445716878056192193184997 271071914635536036222187)
                    ·
                      rfl

theorem cell22_791866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_791866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791866 prefixEnd_791866 := by exact prefixLift 791866
  have htrace : WordTrace (prefixWord ++ tailWord_791866) baseStart_791866 baseEnd_791866 := by
    simpa [prefixWord, tailWord_791866, baseEnd_791866] using wordTrace_append hprefix tailTrace_791866
  have hstable : (prefixWord ++ tailWord_791866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791866).length < 2 ^ (prefixWord ++ tailWord_791866).sum := by decide
  have hdescent : baseEnd_791866 < baseStart_791866 := by decide
  rcases family_descends (prefixWord ++ tailWord_791866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791881 : List Nat := [1, 2, 1, 1, 2, 3, 4, 4, 4]
def baseStart_791881 : Nat := 118140960795 + 791881 * 2 ^ 59
def prefixEnd_791881 : Nat := 4983230072969 + 3 ^ 40 * 791881 * 2
def baseEnd_791881 : Nat := 90359016480693665699047

theorem tailTrace_791881 : CollatzResearch.WordTrace tailWord_791881 prefixEnd_791881 90359016480693665699047 := by
  unfold tailWord_791881
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882272844157854352703497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19254848562771902901802331 28882272844157854352703497)
  ·
    refine ⟨21661704633118390764527623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28882272844157854352703497 21661704633118390764527623)
    ·
      refine ⟨32492556949677586146791435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21661704633118390764527623 32492556949677586146791435)
      ·
        refine ⟨48738835424516379220187153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32492556949677586146791435 48738835424516379220187153)
        ·
          refine ⟨36554126568387284415140365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48738835424516379220187153 36554126568387284415140365)
          ·
            refine ⟨13707797463145231655677637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36554126568387284415140365 13707797463145231655677637)
            ·
              refine ⟨2570212024339730935439557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13707797463145231655677637 2570212024339730935439557)
              ·
                refine ⟨481914754563699550394917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2570212024339730935439557 481914754563699550394917)
                ·
                  refine ⟨90359016480693665699047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481914754563699550394917 90359016480693665699047)
                  ·
                    rfl

theorem cell22_791881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_791881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791881 prefixEnd_791881 := by exact prefixLift 791881
  have htrace : WordTrace (prefixWord ++ tailWord_791881) baseStart_791881 baseEnd_791881 := by
    simpa [prefixWord, tailWord_791881, baseEnd_791881] using wordTrace_append hprefix tailTrace_791881
  have hstable : (prefixWord ++ tailWord_791881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791881).length < 2 ^ (prefixWord ++ tailWord_791881).sum := by decide
  have hdescent : baseEnd_791881 < baseStart_791881 := by decide
  rcases family_descends (prefixWord ++ tailWord_791881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791909 : List Nat := [1, 3, 1, 3, 1, 2, 3, 8]
def baseStart_791909 : Nat := 118140960795 + 791909 * 2 ^ 59
def prefixEnd_791909 : Nat := 4983230072969 + 3 ^ 40 * 791909 * 2
def baseEnd_791909 : Nat := 30120737157144250821895

theorem tailTrace_791909 : CollatzResearch.WordTrace tailWord_791909 prefixEnd_791909 30120737157144250821895 := by
  unfold tailWord_791909
  simp only [CollatzResearch.WordTrace]
  refine ⟨28883294088056415134722781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19255529392037610089815187 28883294088056415134722781)
  ·
    refine ⟨10831235283021155675521043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28883294088056415134722781 10831235283021155675521043)
    ·
      refine ⟨16246852924531733513281565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10831235283021155675521043 16246852924531733513281565)
      ·
        refine ⟨6092569846699400067480587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16246852924531733513281565 6092569846699400067480587)
        ·
          refine ⟨9138854770049100101220881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092569846699400067480587 9138854770049100101220881)
          ·
            refine ⟨6854141077536825075915661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9138854770049100101220881 6854141077536825075915661)
            ·
              refine ⟨2570302904076309403468373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6854141077536825075915661 2570302904076309403468373)
              ·
                refine ⟨30120737157144250821895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2570302904076309403468373 30120737157144250821895)
                ·
                  rfl

theorem cell22_791909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 8].length) (baseStart_791909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791909 prefixEnd_791909 := by exact prefixLift 791909
  have htrace : WordTrace (prefixWord ++ tailWord_791909) baseStart_791909 baseEnd_791909 := by
    simpa [prefixWord, tailWord_791909, baseEnd_791909] using wordTrace_append hprefix tailTrace_791909
  have hstable : (prefixWord ++ tailWord_791909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791909).length < 2 ^ (prefixWord ++ tailWord_791909).sum := by decide
  have hdescent : baseEnd_791909 < baseStart_791909 := by decide
  rcases family_descends (prefixWord ++ tailWord_791909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791975 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 1, 3]
def baseStart_791975 : Nat := 118140960795 + 791975 * 2 ^ 59
def prefixEnd_791975 : Nat := 4983230072969 + 3 ^ 40 * 791975 * 2
def baseEnd_791975 : Nat := 271109227563096085246853

theorem tailTrace_791975 : CollatzResearch.WordTrace tailWord_791975 prefixEnd_791975 271109227563096085246853 := by
  unfold tailWord_791975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28885701305817308406625379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19257134203878205604416919 28885701305817308406625379)
  ·
    refine ⟨43328551958725962609938069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28885701305817308406625379 43328551958725962609938069)
    ·
      refine ⟨2031025873065279497340847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43328551958725962609938069 2031025873065279497340847)
      ·
        refine ⟨3046538809597919246011271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031025873065279497340847 3046538809597919246011271)
        ·
          refine ⟨4569808214396878869016907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046538809597919246011271 4569808214396878869016907)
          ·
            refine ⟨6854712321595318303525361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569808214396878869016907 6854712321595318303525361)
            ·
              refine ⟨5141034241196488727644021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6854712321595318303525361 5141034241196488727644021)
              ·
                refine ⟨481971960112170818216627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5141034241196488727644021 481971960112170818216627)
                ·
                  refine ⟨722957940168256227324941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481971960112170818216627 722957940168256227324941)
                  ·
                    refine ⟨271109227563096085246853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 722957940168256227324941 271109227563096085246853)
                    ·
                      rfl

theorem cell22_791975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_791975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791975 prefixEnd_791975 := by exact prefixLift 791975
  have htrace : WordTrace (prefixWord ++ tailWord_791975) baseStart_791975 baseEnd_791975 := by
    simpa [prefixWord, tailWord_791975, baseEnd_791975] using wordTrace_append hprefix tailTrace_791975
  have hstable : (prefixWord ++ tailWord_791975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791975).length < 2 ^ (prefixWord ++ tailWord_791975).sum := by decide
  have hdescent : baseEnd_791975 < baseStart_791975 := by decide
  rcases family_descends (prefixWord ++ tailWord_791975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791999 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 10]
def baseStart_791999 : Nat := 118140960795 + 791999 * 2 ^ 59
def prefixEnd_791999 : Nat := 4983230072969 + 3 ^ 40 * 791999 * 2
def baseEnd_791999 : Nat := 90372481084522674215593

theorem tailTrace_791999 : CollatzResearch.WordTrace tailWord_791999 prefixEnd_791999 90372481084522674215593 := by
  unfold tailWord_791999
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886576657730360505499051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19257717771820240336999367 28886576657730360505499051)
  ·
    refine ⟨43329864986595540758248577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28886576657730360505499051 43329864986595540758248577)
    ·
      refine ⟨32497398739946655568686433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43329864986595540758248577 32497398739946655568686433)
      ·
        refine ⟨24373049054959991676514825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32497398739946655568686433 24373049054959991676514825)
        ·
          refine ⟨18279786791219993757386119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24373049054959991676514825 18279786791219993757386119)
          ·
            refine ⟨27419680186829990636079179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279786791219993757386119 27419680186829990636079179)
            ·
              refine ⟨41129520280244985954118769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27419680186829990636079179 41129520280244985954118769)
              ·
                refine ⟨30847140210183739465589077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41129520280244985954118769 30847140210183739465589077)
                ·
                  refine ⟨90372481084522674215593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 30847140210183739465589077 90372481084522674215593)
                  ·
                    rfl

theorem cell22_791999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_791999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_791999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_791999 prefixEnd_791999 := by exact prefixLift 791999
  have htrace : WordTrace (prefixWord ++ tailWord_791999) baseStart_791999 baseEnd_791999 := by
    simpa [prefixWord, tailWord_791999, baseEnd_791999] using wordTrace_append hprefix tailTrace_791999
  have hstable : (prefixWord ++ tailWord_791999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791999).length < 2 ^ (prefixWord ++ tailWord_791999).sum := by decide
  have hdescent : baseEnd_791999 < baseStart_791999 := by decide
  rcases family_descends (prefixWord ++ tailWord_791999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792031 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 1, 5]
def baseStart_792031 : Nat := 118140960795 + 792031 * 2 ^ 59
def prefixEnd_792031 : Nat := 4983230072969 + 3 ^ 40 * 792031 * 2
def baseEnd_792031 : Nat := 271128397507530605846681

theorem tailTrace_792031 : CollatzResearch.WordTrace tailWord_792031 prefixEnd_792031 271128397507530605846681 := by
  unfold tailWord_792031
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887743793614429970663947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19258495862409619980442631 28887743793614429970663947)
  ·
    refine ⟨43331615690421644955995921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28887743793614429970663947 43331615690421644955995921)
    ·
      refine ⟨32498711767816233716996941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43331615690421644955995921 32498711767816233716996941)
      ·
        refine ⟨12187016912931087643873853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32498711767816233716996941 12187016912931087643873853)
        ·
          refine ⟨4570131342349157866452695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12187016912931087643873853 4570131342349157866452695)
          ·
            refine ⟨6855197013523736799679043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570131342349157866452695 6855197013523736799679043)
            ·
              refine ⟨10282795520285605199518565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6855197013523736799679043 10282795520285605199518565)
              ·
                refine ⟨1928024160053550974909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10282795520285605199518565 1928024160053550974909731)
                ·
                  refine ⟨2892036240080326462364597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928024160053550974909731 2892036240080326462364597)
                  ·
                    refine ⟨271128397507530605846681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2892036240080326462364597 271128397507530605846681)
                    ·
                      rfl

theorem cell22_792031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_792031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792031 prefixEnd_792031 := by exact prefixLift 792031
  have htrace : WordTrace (prefixWord ++ tailWord_792031) baseStart_792031 baseEnd_792031 := by
    simpa [prefixWord, tailWord_792031, baseEnd_792031] using wordTrace_append hprefix tailTrace_792031
  have hstable : (prefixWord ++ tailWord_792031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792031).length < 2 ^ (prefixWord ++ tailWord_792031).sum := by decide
  have hdescent : baseEnd_792031 < baseStart_792031 := by decide
  rcases family_descends (prefixWord ++ tailWord_792031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792033 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 4]
def baseStart_792033 : Nat := 118140960795 + 792033 * 2 ^ 59
def prefixEnd_792033 : Nat := 4983230072969 + 3 ^ 40 * 792033 * 2
def baseEnd_792033 : Nat := 90376360716134422432225

theorem tailTrace_792033 : CollatzResearch.WordTrace tailWord_792033 prefixEnd_792033 90376360716134422432225 := by
  unfold tailWord_792033
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887816739607184312236753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19258544493071456208157835 28887816739607184312236753)
  ·
    refine ⟨21665862554705388234177565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28887816739607184312236753 21665862554705388234177565)
    ·
      refine ⟨8124698458014520587816587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21665862554705388234177565 8124698458014520587816587)
      ·
        refine ⟨12187047687021780881724881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8124698458014520587816587 12187047687021780881724881)
        ·
          refine ⟨9140285765266335661293661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12187047687021780881724881 9140285765266335661293661)
          ·
            refine ⟨3427607161974875872985123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9140285765266335661293661 3427607161974875872985123)
            ·
              refine ⟨5141410742962313809477685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427607161974875872985123 5141410742962313809477685)
              ·
                refine ⟨482007257152716919638533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5141410742962313809477685 482007257152716919638533)
                ·
                  refine ⟨90376360716134422432225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482007257152716919638533 90376360716134422432225)
                  ·
                    rfl

theorem cell22_792033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 4].length) (baseStart_792033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792033 prefixEnd_792033 := by exact prefixLift 792033
  have htrace : WordTrace (prefixWord ++ tailWord_792033) baseStart_792033 baseEnd_792033 := by
    simpa [prefixWord, tailWord_792033, baseEnd_792033] using wordTrace_append hprefix tailTrace_792033
  have hstable : (prefixWord ++ tailWord_792033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792033).length < 2 ^ (prefixWord ++ tailWord_792033).sum := by decide
  have hdescent : baseEnd_792033 < baseStart_792033 := by decide
  rcases family_descends (prefixWord ++ tailWord_792033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792035 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 1, 4]
def baseStart_792035 : Nat := 118140960795 + 792035 * 2 ^ 59
def prefixEnd_792035 : Nat := 4983230072969 + 3 ^ 40 * 792035 * 2
def baseEnd_792035 : Nat := 271129766789275928746669

theorem tailTrace_792035 : CollatzResearch.WordTrace tailWord_792035 prefixEnd_792035 271129766789275928746669 := by
  unfold tailWord_792035
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887889685599938653809559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19258593123733292435873039 28887889685599938653809559)
  ·
    refine ⟨43331834528399907980714339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28887889685599938653809559 43331834528399907980714339)
    ·
      refine ⟨64997751792599861971071509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43331834528399907980714339 64997751792599861971071509)
      ·
        refine ⟨3046769615278118529893977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64997751792599861971071509 3046769615278118529893977)
        ·
          refine ⟨2285077211458588897420483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046769615278118529893977 2285077211458588897420483)
          ·
            refine ⟨3427615817187883346130725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285077211458588897420483 3427615817187883346130725)
            ·
              refine ⟨642677965722728127399511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3427615817187883346130725 642677965722728127399511)
              ·
                refine ⟨964016948584092191099267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642677965722728127399511 964016948584092191099267)
                ·
                  refine ⟨1446025422876138286648901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964016948584092191099267 1446025422876138286648901)
                  ·
                    refine ⟨271129766789275928746669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1446025422876138286648901 271129766789275928746669)
                    ·
                      rfl

theorem cell22_792035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 4].length) (baseStart_792035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792035 prefixEnd_792035 := by exact prefixLift 792035
  have htrace : WordTrace (prefixWord ++ tailWord_792035) baseStart_792035 baseEnd_792035 := by
    simpa [prefixWord, tailWord_792035, baseEnd_792035] using wordTrace_append hprefix tailTrace_792035
  have hstable : (prefixWord ++ tailWord_792035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792035).length < 2 ^ (prefixWord ++ tailWord_792035).sum := by decide
  have hdescent : baseEnd_792035 < baseStart_792035 := by decide
  rcases family_descends (prefixWord ++ tailWord_792035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792048 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_792048 : Nat := 118140960795 + 792048 * 2 ^ 59
def prefixEnd_792048 : Nat := 4983230072969 + 3 ^ 40 * 792048 * 2
def baseEnd_792048 : Nat := 271134216954948228171629

theorem tailTrace_792048 : CollatzResearch.WordTrace tailWord_792048 prefixEnd_792048 271134216954948228171629 := by
  unfold tailWord_792048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14444181917276420937016399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19258909223035227916021865 14444181917276420937016399)
  ·
    refine ⟨21666272875914631405524599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14444181917276420937016399 21666272875914631405524599)
    ·
      refine ⟨32499409313871947108286899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21666272875914631405524599 32499409313871947108286899)
      ·
        refine ⟨48749113970807920662430349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32499409313871947108286899 48749113970807920662430349)
        ·
          refine ⟨18280917739052970248411381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48749113970807920662430349 18280917739052970248411381)
          ·
            refine ⟨1713836038036215960788567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18280917739052970248411381 1713836038036215960788567)
            ·
              refine ⟨2570754057054323941182851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713836038036215960788567 2570754057054323941182851)
              ·
                refine ⟨3856131085581485911774277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570754057054323941182851 3856131085581485911774277)
                ·
                  refine ⟨723024578546528608457677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3856131085581485911774277 723024578546528608457677)
                  ·
                    refine ⟨271134216954948228171629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723024578546528608457677 271134216954948228171629)
                    ·
                      rfl

theorem cell22_792048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_792048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792048 prefixEnd_792048 := by exact prefixLift 792048
  have htrace : WordTrace (prefixWord ++ tailWord_792048) baseStart_792048 baseEnd_792048 := by
    simpa [prefixWord, tailWord_792048, baseEnd_792048] using wordTrace_append hprefix tailTrace_792048
  have hstable : (prefixWord ++ tailWord_792048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792048).length < 2 ^ (prefixWord ++ tailWord_792048).sum := by decide
  have hdescent : baseEnd_792048 < baseStart_792048 := by decide
  rcases family_descends (prefixWord ++ tailWord_792048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792050 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 4]
def baseStart_792050 : Nat := 118140960795 + 792050 * 2 ^ 59
def prefixEnd_792050 : Nat := 4983230072969 + 3 ^ 40 * 792050 * 2
def baseEnd_792050 : Nat := 90378300531940296540541

theorem tailTrace_792050 : CollatzResearch.WordTrace tailWord_792050 prefixEnd_792050 90378300531940296540541 := by
  unfold tailWord_792050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222109195136399053901401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19258957853697064143737069 7222109195136399053901401)
  ·
    refine ⟨5416581896352299290426051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7222109195136399053901401 5416581896352299290426051)
    ·
      refine ⟨8124872844528448935639077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5416581896352299290426051 8124872844528448935639077)
      ·
        refine ⟨1523413658349084175432327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8124872844528448935639077 1523413658349084175432327)
        ·
          refine ⟨2285120487523626263148491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523413658349084175432327 2285120487523626263148491)
          ·
            refine ⟨3427680731285439394722737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285120487523626263148491 3427680731285439394722737)
            ·
              refine ⟨2570760548464079546042053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427680731285439394722737 2570760548464079546042053)
              ·
                refine ⟨482017602837014914882885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2570760548464079546042053 482017602837014914882885)
                ·
                  refine ⟨90378300531940296540541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482017602837014914882885 90378300531940296540541)
                  ·
                    rfl

theorem cell22_792050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_792050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792050 prefixEnd_792050 := by exact prefixLift 792050
  have htrace : WordTrace (prefixWord ++ tailWord_792050) baseStart_792050 baseEnd_792050 := by
    simpa [prefixWord, tailWord_792050, baseEnd_792050] using wordTrace_append hprefix tailTrace_792050
  have hstable : (prefixWord ++ tailWord_792050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792050).length < 2 ^ (prefixWord ++ tailWord_792050).sum := by decide
  have hdescent : baseEnd_792050 < baseStart_792050 := by decide
  rcases family_descends (prefixWord ++ tailWord_792050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792065 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 1, 5]
def baseStart_792065 : Nat := 118140960795 + 792065 * 2 ^ 59
def prefixEnd_792065 : Nat := 4983230072969 + 3 ^ 40 * 792065 * 2
def baseEnd_792065 : Nat := 271140036402365850496577

theorem tailTrace_792065 : CollatzResearch.WordTrace tailWord_792065 prefixEnd_792065 271140036402365850496577 := by
  unfold tailWord_792065
  simp only [CollatzResearch.WordTrace]
  refine ⟨28888983875491253777401649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19259322583660835851601099 28888983875491253777401649)
  ·
    refine ⟨21666737906618440333051237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28888983875491253777401649 21666737906618440333051237)
    ·
      refine ⟨4062513357490957562447107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21666737906618440333051237 4062513357490957562447107)
      ·
        refine ⟨6093770036236436343670661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4062513357490957562447107 6093770036236436343670661)
        ·
          refine ⟨1142581881794331814438249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6093770036236436343670661 1142581881794331814438249)
          ·
            refine ⟨856936411345748860828687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142581881794331814438249 856936411345748860828687)
            ·
              refine ⟨1285404617018623291243031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856936411345748860828687 1285404617018623291243031)
              ·
                refine ⟨1928106925527934936864547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285404617018623291243031 1928106925527934936864547)
                ·
                  refine ⟨2892160388291902405296821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928106925527934936864547 2892160388291902405296821)
                  ·
                    refine ⟨271140036402365850496577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2892160388291902405296821 271140036402365850496577)
                    ·
                      rfl

theorem cell22_792065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_792065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792065 prefixEnd_792065 := by exact prefixLift 792065
  have htrace : WordTrace (prefixWord ++ tailWord_792065) baseStart_792065 baseEnd_792065 := by
    simpa [prefixWord, tailWord_792065, baseEnd_792065] using wordTrace_append hprefix tailTrace_792065
  have hstable : (prefixWord ++ tailWord_792065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792065).length < 2 ^ (prefixWord ++ tailWord_792065).sum := by decide
  have hdescent : baseEnd_792065 < baseStart_792065 := by decide
  rcases family_descends (prefixWord ++ tailWord_792065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792078 : List Nat := [4, 1, 1, 2, 4, 1, 1, 8]
def baseStart_792078 : Nat := 118140960795 + 792078 * 2 ^ 59
def prefixEnd_792078 : Nat := 4983230072969 + 3 ^ 40 * 792078 * 2
def baseEnd_792078 : Nat := 30127165174226461102393

theorem tailTrace_792078 : CollatzResearch.WordTrace tailWord_792078 prefixEnd_792078 30127165174226461102393 := by
  unfold tailWord_792078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3611182253055519624703111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19259638682962771331749925 3611182253055519624703111)
  ·
    refine ⟨5416773379583279437054667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3611182253055519624703111 5416773379583279437054667)
    ·
      refine ⟨8125160069374919155582001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5416773379583279437054667 8125160069374919155582001)
      ·
        refine ⟨6093870052031189366686501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8125160069374919155582001 6093870052031189366686501)
        ·
          refine ⟨1142600634755848006253719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6093870052031189366686501 1142600634755848006253719)
          ·
            refine ⟨1713900952133772009380579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142600634755848006253719 1713900952133772009380579)
            ·
              refine ⟨2570851428200658014070869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713900952133772009380579 2570851428200658014070869)
              ·
                refine ⟨30127165174226461102393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2570851428200658014070869 30127165174226461102393)
                ·
                  rfl

theorem cell22_792078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_792078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792078 prefixEnd_792078 := by exact prefixLift 792078
  have htrace : WordTrace (prefixWord ++ tailWord_792078) baseStart_792078 baseEnd_792078 := by
    simpa [prefixWord, tailWord_792078, baseEnd_792078] using wordTrace_append hprefix tailTrace_792078
  have hstable : (prefixWord ++ tailWord_792078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792078).length < 2 ^ (prefixWord ++ tailWord_792078).sum := by decide
  have hdescent : baseEnd_792078 < baseStart_792078 := by decide
  rcases family_descends (prefixWord ++ tailWord_792078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792084 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 4]
def baseStart_792084 : Nat := 118140960795 + 792084 * 2 ^ 59
def prefixEnd_792084 : Nat := 4983230072969 + 3 ^ 40 * 792084 * 2
def baseEnd_792084 : Nat := 90382180163552044757173

theorem tailTrace_792084 : CollatzResearch.WordTrace tailWord_792084 prefixEnd_792084 90382180163552044757173 := by
  unfold tailWord_792084
  simp only [CollatzResearch.WordTrace]
  refine ⟨14444838431211210011171653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19259784574948280014895537 14444838431211210011171653)
  ·
    refine ⟨2708407205852101877094685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14444838431211210011171653 2708407205852101877094685)
    ·
      refine ⟨1015652702194538203910507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2708407205852101877094685 1015652702194538203910507)
      ·
        refine ⟨1523479053291807305865761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015652702194538203910507 1523479053291807305865761)
        ·
          refine ⟨1142609289968855479399321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523479053291807305865761 1142609289968855479399321)
          ·
            refine ⟨856956967476641609549491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142609289968855479399321 856956967476641609549491)
            ·
              refine ⟨1285435451214962414324237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856956967476641609549491 1285435451214962414324237)
              ·
                refine ⟨482038294205610905371589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285435451214962414324237 482038294205610905371589)
                ·
                  refine ⟨90382180163552044757173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482038294205610905371589 90382180163552044757173)
                  ·
                    rfl

theorem cell22_792084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_792084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792084 prefixEnd_792084 := by exact prefixLift 792084
  have htrace : WordTrace (prefixWord ++ tailWord_792084) baseStart_792084 baseEnd_792084 := by
    simpa [prefixWord, tailWord_792084, baseEnd_792084] using wordTrace_append hprefix tailTrace_792084
  have hstable : (prefixWord ++ tailWord_792084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792084).length < 2 ^ (prefixWord ++ tailWord_792084).sum := by decide
  have hdescent : baseEnd_792084 < baseStart_792084 := by decide
  rcases family_descends (prefixWord ++ tailWord_792084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792153 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_792153 : Nat := 118140960795 + 792153 * 2 ^ 59
def prefixEnd_792153 : Nat := 4983230072969 + 3 ^ 40 * 792153 * 2
def baseEnd_792153 : Nat := 271170160600762954296307

theorem tailTrace_792153 : CollatzResearch.WordTrace tailWord_792153 prefixEnd_792153 271170160600762954296307 := by
  unfold tailWord_792153
  simp only [CollatzResearch.WordTrace]
  refine ⟨28892193499172444806605113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19261462332781629871070075 28892193499172444806605113)
  ·
    refine ⟨21669145124379333604953835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28892193499172444806605113 21669145124379333604953835)
    ·
      refine ⟨32503717686569000407430753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21669145124379333604953835 32503717686569000407430753)
      ·
        refine ⟨24377788264926750305573065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32503717686569000407430753 24377788264926750305573065)
        ·
          refine ⟨18283341198695062729179799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24377788264926750305573065 18283341198695062729179799)
          ·
            refine ⟨27425011798042594093769699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18283341198695062729179799 27425011798042594093769699)
            ·
              refine ⟨41137517697063891140654549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27425011798042594093769699 41137517697063891140654549)
              ·
                refine ⟨964160571024934948609091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41137517697063891140654549 964160571024934948609091)
                ·
                  refine ⟨1446240856537402422913637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964160571024934948609091 1446240856537402422913637)
                  ·
                    refine ⟨271170160600762954296307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1446240856537402422913637 271170160600762954296307)
                    ·
                      rfl

theorem cell22_792153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_792153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792153 prefixEnd_792153 := by exact prefixLift 792153
  have htrace : WordTrace (prefixWord ++ tailWord_792153) baseStart_792153 baseEnd_792153 := by
    simpa [prefixWord, tailWord_792153, baseEnd_792153] using wordTrace_append hprefix tailTrace_792153
  have hstable : (prefixWord ++ tailWord_792153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792153).length < 2 ^ (prefixWord ++ tailWord_792153).sum := by decide
  have hdescent : baseEnd_792153 < baseStart_792153 := by decide
  rcases family_descends (prefixWord ++ tailWord_792153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792183 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 6, 3]
def baseStart_792183 : Nat := 118140960795 + 792183 * 2 ^ 59
def prefixEnd_792183 : Nat := 4983230072969 + 3 ^ 40 * 792183 * 2
def baseEnd_792183 : Nat := 271180430213852876046215

theorem tailTrace_792183 : CollatzResearch.WordTrace tailWord_792183 prefixEnd_792183 271180430213852876046215 := by
  unfold tailWord_792183
  simp only [CollatzResearch.WordTrace]
  refine ⟨28893287689063759930197203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19262191792709173286798135 28893287689063759930197203)
  ·
    refine ⟨43339931533595639895295805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28893287689063759930197203 43339931533595639895295805)
    ·
      refine ⟨16252474325098364960735927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43339931533595639895295805 16252474325098364960735927)
      ·
        refine ⟨24378711487647547441103891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16252474325098364960735927 24378711487647547441103891)
        ·
          refine ⟨36568067231471321161655837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24378711487647547441103891 36568067231471321161655837)
          ·
            refine ⟨13713025211801745435620939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36568067231471321161655837 13713025211801745435620939)
            ·
              refine ⟨20569537817702618153431409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13713025211801745435620939 20569537817702618153431409)
              ·
                refine ⟨15427153363276963615073557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20569537817702618153431409 15427153363276963615073557)
                ·
                  refine ⟨723147813903607669456573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15427153363276963615073557 723147813903607669456573)
                  ·
                    refine ⟨271180430213852876046215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723147813903607669456573 271180430213852876046215)
                    ·
                      rfl

theorem cell22_792183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_792183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792183 prefixEnd_792183 := by exact prefixLift 792183
  have htrace : WordTrace (prefixWord ++ tailWord_792183) baseStart_792183 baseEnd_792183 := by
    simpa [prefixWord, tailWord_792183, baseEnd_792183] using wordTrace_append hprefix tailTrace_792183
  have hstable : (prefixWord ++ tailWord_792183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792183).length < 2 ^ (prefixWord ++ tailWord_792183).sum := by decide
  have hdescent : baseEnd_792183 < baseStart_792183 := by decide
  rcases family_descends (prefixWord ++ tailWord_792183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792202 : List Nat := [3, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_792202 : Nat := 118140960795 + 792202 * 2 ^ 59
def prefixEnd_792202 : Nat := 4983230072969 + 3 ^ 40 * 792202 * 2
def baseEnd_792202 : Nat := 90395644767381053273719

theorem tailTrace_792202 : CollatzResearch.WordTrace tailWord_792202 prefixEnd_792202 90395644767381053273719 := by
  unfold tailWord_792202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7223495168998731543784715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19262653783996617450092573 7223495168998731543784715)
  ·
    refine ⟨10835242753498097315677073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7223495168998731543784715 10835242753498097315677073)
    ·
      refine ⟨8126432065123572986757805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10835242753498097315677073 8126432065123572986757805)
      ·
        refine ⟨3047412024421339870034177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8126432065123572986757805 3047412024421339870034177)
        ·
          refine ⟨2285559018316004902525633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3047412024421339870034177 2285559018316004902525633)
          ·
            refine ⟨1714169263737003676894225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2285559018316004902525633 1714169263737003676894225)
            ·
              refine ⟨1285626947802752757670669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714169263737003676894225 1285626947802752757670669)
              ·
                refine ⟨482110105426032284126501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285626947802752757670669 482110105426032284126501)
                ·
                  refine ⟨90395644767381053273719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482110105426032284126501 90395644767381053273719)
                  ·
                    rfl

theorem cell22_792202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_792202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792202 prefixEnd_792202 := by exact prefixLift 792202
  have htrace : WordTrace (prefixWord ++ tailWord_792202) baseStart_792202 baseEnd_792202 := by
    simpa [prefixWord, tailWord_792202, baseEnd_792202] using wordTrace_append hprefix tailTrace_792202
  have hstable : (prefixWord ++ tailWord_792202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792202).length < 2 ^ (prefixWord ++ tailWord_792202).sum := by decide
  have hdescent : baseEnd_792202 < baseStart_792202 := by decide
  rcases family_descends (prefixWord ++ tailWord_792202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792279 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 1, 3]
def baseStart_792279 : Nat := 118140960795 + 792279 * 2 ^ 59
def prefixEnd_792279 : Nat := 4983230072969 + 3 ^ 40 * 792279 * 2
def baseEnd_792279 : Nat := 271213292975740625645921

theorem tailTrace_792279 : CollatzResearch.WordTrace tailWord_792279 prefixEnd_792279 271213292975740625645921 := by
  unfold tailWord_792279
  simp only [CollatzResearch.WordTrace]
  refine ⟨28896789096715968325691891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19264526064477312217127927 28896789096715968325691891)
  ·
    refine ⟨43345183645073952488537837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28896789096715968325691891 43345183645073952488537837)
    ·
      refine ⟨16254443866902732183201689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43345183645073952488537837 16254443866902732183201689)
      ·
        refine ⟨12190832900177049137401267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16254443866902732183201689 12190832900177049137401267)
        ·
          refine ⟨18286249350265573706101901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12190832900177049137401267 18286249350265573706101901)
          ·
            refine ⟨6857343506349590139788213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18286249350265573706101901 6857343506349590139788213)
            ·
              refine ⟨642875953720274075605145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6857343506349590139788213 642875953720274075605145)
              ·
                refine ⟨482156965290205556703859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642875953720274075605145 482156965290205556703859)
                ·
                  refine ⟨723235447935308335055789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482156965290205556703859 723235447935308335055789)
                  ·
                    refine ⟨271213292975740625645921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723235447935308335055789 271213292975740625645921)
                    ·
                      rfl

theorem cell22_792279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_792279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792279 prefixEnd_792279 := by exact prefixLift 792279
  have htrace : WordTrace (prefixWord ++ tailWord_792279) baseStart_792279 baseEnd_792279 := by
    simpa [prefixWord, tailWord_792279, baseEnd_792279] using wordTrace_append hprefix tailTrace_792279
  have hstable : (prefixWord ++ tailWord_792279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792279).length < 2 ^ (prefixWord ++ tailWord_792279).sum := by decide
  have hdescent : baseEnd_792279 < baseStart_792279 := by decide
  rcases family_descends (prefixWord ++ tailWord_792279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792303 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 8]
def baseStart_792303 : Nat := 118140960795 + 792303 * 2 ^ 59
def prefixEnd_792303 : Nat := 4983230072969 + 3 ^ 40 * 792303 * 2
def baseEnd_792303 : Nat := 90407169555404187681949

theorem tailTrace_792303 : CollatzResearch.WordTrace tailWord_792303 prefixEnd_792303 90407169555404187681949 := by
  unfold tailWord_792303
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897664448629020424565563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19265109632419346949710375 28897664448629020424565563)
  ·
    refine ⟨43346496672943530636848345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28897664448629020424565563 43346496672943530636848345)
    ·
      refine ⟨32509872504707647977636259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43346496672943530636848345 32509872504707647977636259)
      ·
        refine ⟨48764808757061471966454389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32509872504707647977636259 48764808757061471966454389)
        ·
          refine ⟨4571700820974512996855099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48764808757061471966454389 4571700820974512996855099)
          ·
            refine ⟨6857551231461769495282649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571700820974512996855099 6857551231461769495282649)
            ·
              refine ⟨5143163423596327121461987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6857551231461769495282649 5143163423596327121461987)
              ·
                refine ⟨7714745135394490682192981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5143163423596327121461987 7714745135394490682192981)
                ·
                  refine ⟨90407169555404187681949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7714745135394490682192981 90407169555404187681949)
                  ·
                    rfl

theorem cell22_792303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_792303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792303 prefixEnd_792303 := by exact prefixLift 792303
  have htrace : WordTrace (prefixWord ++ tailWord_792303) baseStart_792303 baseEnd_792303 := by
    simpa [prefixWord, tailWord_792303, baseEnd_792303] using wordTrace_append hprefix tailTrace_792303
  have hstable : (prefixWord ++ tailWord_792303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792303).length < 2 ^ (prefixWord ++ tailWord_792303).sum := by decide
  have hdescent : baseEnd_792303 < baseStart_792303 := by decide
  rcases family_descends (prefixWord ++ tailWord_792303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792305 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_792305 : Nat := 118140960795 + 792305 * 2 ^ 59
def prefixEnd_792305 : Nat := 4983230072969 + 3 ^ 40 * 792305 * 2
def baseEnd_792305 : Nat := 271222193307085224495841

theorem tailTrace_792305 : CollatzResearch.WordTrace tailWord_792305 prefixEnd_792305 271222193307085224495841 := by
  unfold tailWord_792305
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897737394621774766138369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19265158263081183177425579 28897737394621774766138369)
  ·
    refine ⟨21673303045966331074603777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28897737394621774766138369 21673303045966331074603777)
    ·
      refine ⟨16254977284474748305952833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21673303045966331074603777 16254977284474748305952833)
      ·
        refine ⟨12191232963356061229464625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16254977284474748305952833 12191232963356061229464625)
        ·
          refine ⟨9143424722517045922098469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12191232963356061229464625 9143424722517045922098469)
          ·
            refine ⟨1714392135471946110393463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9143424722517045922098469 1714392135471946110393463)
            ·
              refine ⟨2571588203207919165590195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714392135471946110393463 2571588203207919165590195)
              ·
                refine ⟨3857382304811878748385293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571588203207919165590195 3857382304811878748385293)
                ·
                  refine ⟨1446518364304454530644485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3857382304811878748385293 1446518364304454530644485)
                  ·
                    refine ⟨271222193307085224495841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1446518364304454530644485 271222193307085224495841)
                    ·
                      rfl

theorem cell22_792305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_792305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792305 prefixEnd_792305 := by exact prefixLift 792305
  have htrace : WordTrace (prefixWord ++ tailWord_792305) baseStart_792305 baseEnd_792305 := by
    simpa [prefixWord, tailWord_792305, baseEnd_792305] using wordTrace_append hprefix tailTrace_792305
  have hstable : (prefixWord ++ tailWord_792305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792305).length < 2 ^ (prefixWord ++ tailWord_792305).sum := by decide
  have hdescent : baseEnd_792305 < baseStart_792305 := by decide
  rcases family_descends (prefixWord ++ tailWord_792305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792352 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_792352 : Nat := 118140960795 + 792352 * 2 ^ 59
def prefixEnd_792352 : Nat := 4983230072969 + 3 ^ 40 * 792352 * 2
def baseEnd_792352 : Nat := 271238282367592768570697

theorem tailTrace_792352 : CollatzResearch.WordTrace tailWord_792352 prefixEnd_792352 271238282367592768570697 := by
  unfold tailWord_792352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449725812725750896549655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19266301083634334528732873 14449725812725750896549655)
  ·
    refine ⟨21674588719088626344824483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14449725812725750896549655 21674588719088626344824483)
    ·
      refine ⟨32511883078632939517236725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21674588719088626344824483 32511883078632939517236725)
      ·
        refine ⟨3047989038621838079740943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32511883078632939517236725 3047989038621838079740943)
        ·
          refine ⟨4571983557932757119611415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047989038621838079740943 4571983557932757119611415)
          ·
            refine ⟨6857975336899135679417123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571983557932757119611415 6857975336899135679417123)
            ·
              refine ⟨10286963005348703519125685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6857975336899135679417123 10286963005348703519125685)
              ·
                refine ⟨964402781751440954918033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10286963005348703519125685 964402781751440954918033)
                ·
                  refine ⟨723302086313580716188525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964402781751440954918033 723302086313580716188525)
                  ·
                    refine ⟨271238282367592768570697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723302086313580716188525 271238282367592768570697)
                    ·
                      rfl

theorem cell22_792352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_792352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792352 prefixEnd_792352 := by exact prefixLift 792352
  have htrace : WordTrace (prefixWord ++ tailWord_792352) baseStart_792352 baseEnd_792352 := by
    simpa [prefixWord, tailWord_792352, baseEnd_792352] using wordTrace_append hprefix tailTrace_792352
  have hstable : (prefixWord ++ tailWord_792352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792352).length < 2 ^ (prefixWord ++ tailWord_792352).sum := by decide
  have hdescent : baseEnd_792352 < baseStart_792352 := by decide
  rcases family_descends (prefixWord ++ tailWord_792352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792474 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 1, 4]
def baseStart_792474 : Nat := 118140960795 + 792474 * 2 ^ 59
def prefixEnd_792474 : Nat := 4983230072969 + 3 ^ 40 * 792474 * 2
def baseEnd_792474 : Nat := 271280045460825117020323

theorem tailTrace_792474 : CollatzResearch.WordTrace tailWord_792474 prefixEnd_792474 271280045460825117020323 := by
  unfold tailWord_792474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225975332752379157260119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19269267554006344419360317 7225975332752379157260119)
  ·
    refine ⟨10838962999128568735890179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7225975332752379157260119 10838962999128568735890179)
    ·
      refine ⟨16258444498692853103835269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10838962999128568735890179 16258444498692853103835269)
      ·
        refine ⟨3048458343504909956969113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16258444498692853103835269 3048458343504909956969113)
        ·
          refine ⟨2286343757628682467726835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048458343504909956969113 2286343757628682467726835)
          ·
            refine ⟨3429515636443023701590253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286343757628682467726835 3429515636443023701590253)
            ·
              refine ⟨1286068363666133888096345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3429515636443023701590253 1286068363666133888096345)
              ·
                refine ⟨964551272749600416072259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286068363666133888096345 964551272749600416072259)
                ·
                  refine ⟨1446826909124400624108389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964551272749600416072259 1446826909124400624108389)
                  ·
                    refine ⟨271280045460825117020323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1446826909124400624108389 271280045460825117020323)
                    ·
                      rfl

theorem cell22_792474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_792474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792474 prefixEnd_792474 := by exact prefixLift 792474
  have htrace : WordTrace (prefixWord ++ tailWord_792474) baseStart_792474 baseEnd_792474 := by
    simpa [prefixWord, tailWord_792474, baseEnd_792474] using wordTrace_append hprefix tailTrace_792474
  have hstable : (prefixWord ++ tailWord_792474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792474).length < 2 ^ (prefixWord ++ tailWord_792474).sum := by decide
  have hdescent : baseEnd_792474 < baseStart_792474 := by decide
  rcases family_descends (prefixWord ++ tailWord_792474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792485 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_792485 : Nat := 118140960795 + 792485 * 2 ^ 59
def prefixEnd_792485 : Nat := 4983230072969 + 3 ^ 40 * 792485 * 2
def baseEnd_792485 : Nat := 271283810985624754995289

theorem tailTrace_792485 : CollatzResearch.WordTrace tailWord_792485 prefixEnd_792485 271283810985624754995289 := by
  unfold tailWord_792485
  simp only [CollatzResearch.WordTrace]
  refine ⟨28904302533969665507690909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19269535022646443671793939 28904302533969665507690909)
  ·
    refine ⟨10839113450238624565384091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28904302533969665507690909 10839113450238624565384091)
    ·
      refine ⟨16258670175357936848076137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10839113450238624565384091 16258670175357936848076137)
      ·
        refine ⟨12194002631518452636057103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16258670175357936848076137 12194002631518452636057103)
        ·
          refine ⟨18291003947277678954085655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12194002631518452636057103 18291003947277678954085655)
          ·
            refine ⟨27436505920916518431128483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18291003947277678954085655 27436505920916518431128483)
            ·
              refine ⟨41154758881374777646692725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27436505920916518431128483 41154758881374777646692725)
              ·
                refine ⟨3858258645128885404377443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41154758881374777646692725 3858258645128885404377443)
                ·
                  refine ⟨5787387967693328106566165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858258645128885404377443 5787387967693328106566165)
                  ·
                    refine ⟨271283810985624754995289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5787387967693328106566165 271283810985624754995289)
                    ·
                      rfl

theorem cell22_792485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_792485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792485 prefixEnd_792485 := by exact prefixLift 792485
  have htrace : WordTrace (prefixWord ++ tailWord_792485) baseStart_792485 baseEnd_792485 := by
    simpa [prefixWord, tailWord_792485, baseEnd_792485] using wordTrace_append hprefix tailTrace_792485
  have hstable : (prefixWord ++ tailWord_792485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792485).length < 2 ^ (prefixWord ++ tailWord_792485).sum := by decide
  have hdescent : baseEnd_792485 < baseStart_792485 := by decide
  rcases family_descends (prefixWord ++ tailWord_792485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792487 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 3, 5]
def baseStart_792487 : Nat := 118140960795 + 792487 * 2 ^ 59
def prefixEnd_792487 : Nat := 4983230072969 + 3 ^ 40 * 792487 * 2
def baseEnd_792487 : Nat := 271284495626497416445283

theorem tailTrace_792487 : CollatzResearch.WordTrace tailWord_792487 prefixEnd_792487 271284495626497416445283 := by
  unfold tailWord_792487
  simp only [CollatzResearch.WordTrace]
  refine ⟨28904375479962419849263715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19269583653308279899509143 28904375479962419849263715)
  ·
    refine ⟨43356563219943629773895573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28904375479962419849263715 43356563219943629773895573)
    ·
      refine ⟨2032338900934857645651355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43356563219943629773895573 2032338900934857645651355)
      ·
        refine ⟨3048508351402286468477033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032338900934857645651355 3048508351402286468477033)
        ·
          refine ⟨2286381263551714851357775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048508351402286468477033 2286381263551714851357775)
          ·
            refine ⟨3429571895327572277036663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286381263551714851357775 3429571895327572277036663)
            ·
              refine ⟨5144357842991358415554995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429571895327572277036663 5144357842991358415554995)
              ·
                refine ⟨7716536764487037623332493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5144357842991358415554995 7716536764487037623332493)
                ·
                  refine ⟨2893701286682639108749685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7716536764487037623332493 2893701286682639108749685)
                  ·
                    refine ⟨271284495626497416445283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2893701286682639108749685 271284495626497416445283)
                    ·
                      rfl

theorem cell22_792487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_792487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792487 prefixEnd_792487 := by exact prefixLift 792487
  have htrace : WordTrace (prefixWord ++ tailWord_792487) baseStart_792487 baseEnd_792487 := by
    simpa [prefixWord, tailWord_792487, baseEnd_792487] using wordTrace_append hprefix tailTrace_792487
  have hstable : (prefixWord ++ tailWord_792487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792487).length < 2 ^ (prefixWord ++ tailWord_792487).sum := by decide
  have hdescent : baseEnd_792487 < baseStart_792487 := by decide
  rcases family_descends (prefixWord ++ tailWord_792487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792504 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_792504 : Nat := 118140960795 + 792504 * 2 ^ 59
def prefixEnd_792504 : Nat := 4983230072969 + 3 ^ 40 * 792504 * 2
def baseEnd_792504 : Nat := 271290315073915038770231

theorem tailTrace_792504 : CollatzResearch.WordTrace tailWord_792504 prefixEnd_792504 271290315073915038770231 := by
  unfold tailWord_792504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14452497760450415876316283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19269997013933887835088377 14452497760450415876316283)
  ·
    refine ⟨21678746640675623814474425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14452497760450415876316283 21678746640675623814474425)
    ·
      refine ⟨16259059980506717860855819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21678746640675623814474425 16259059980506717860855819)
      ·
        refine ⟨24388589970760076791283729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16259059980506717860855819 24388589970760076791283729)
        ·
          refine ⟨18291442478070057593462797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24388589970760076791283729 18291442478070057593462797)
          ·
            refine ⟨6859290929276271597548549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18291442478070057593462797 6859290929276271597548549)
            ·
              refine ⟨1286117049239300924540353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6859290929276271597548549 1286117049239300924540353)
              ·
                refine ⟨964587786929475693405265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286117049239300924540353 964587786929475693405265)
                ·
                  refine ⟨723440840197106770053949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964587786929475693405265 723440840197106770053949)
                  ·
                    refine ⟨271290315073915038770231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723440840197106770053949 271290315073915038770231)
                    ·
                      rfl

theorem cell22_792504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_792504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792504 prefixEnd_792504 := by exact prefixLift 792504
  have htrace : WordTrace (prefixWord ++ tailWord_792504) baseStart_792504 baseEnd_792504 := by
    simpa [prefixWord, tailWord_792504, baseEnd_792504] using wordTrace_append hprefix tailTrace_792504
  have hstable : (prefixWord ++ tailWord_792504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792504).length < 2 ^ (prefixWord ++ tailWord_792504).sum := by decide
  have hdescent : baseEnd_792504 < baseStart_792504 := by decide
  rcases family_descends (prefixWord ++ tailWord_792504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792540 : List Nat := [2, 2, 6, 1, 1, 1, 2, 3, 4]
def baseStart_792540 : Nat := 118140960795 + 792540 * 2 ^ 59
def prefixEnd_792540 : Nat := 4983230072969 + 3 ^ 40 * 792540 * 2
def baseEnd_792540 : Nat := 90434212869874314956707

theorem tailTrace_792540 : CollatzResearch.WordTrace tailWord_792540 prefixEnd_792540 90434212869874314956707 := by
  unfold tailWord_792540
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453154274385204950471537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19270872365846939933962049 14453154274385204950471537)
  ·
    refine ⟨10839865705788903712853653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14453154274385204950471537 10839865705788903712853653)
    ·
      refine ⟨508118704958854861540015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10839865705788903712853653 508118704958854861540015)
      ·
        refine ⟨762178057438282292310023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508118704958854861540015 762178057438282292310023)
        ·
          refine ⟨1143267086157423438465035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762178057438282292310023 1143267086157423438465035)
          ·
            refine ⟨1714900629236135157697553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143267086157423438465035 1714900629236135157697553)
            ·
              refine ⟨1286175471927101368273165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714900629236135157697553 1286175471927101368273165)
              ·
                refine ⟨482315801972663013102437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1286175471927101368273165 482315801972663013102437)
                ·
                  refine ⟨90434212869874314956707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482315801972663013102437 90434212869874314956707)
                  ·
                    rfl

theorem cell22_792540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_792540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792540 prefixEnd_792540 := by exact prefixLift 792540
  have htrace : WordTrace (prefixWord ++ tailWord_792540) baseStart_792540 baseEnd_792540 := by
    simpa [prefixWord, tailWord_792540, baseEnd_792540] using wordTrace_append hprefix tailTrace_792540
  have hstable : (prefixWord ++ tailWord_792540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792540).length < 2 ^ (prefixWord ++ tailWord_792540).sum := by decide
  have hdescent : baseEnd_792540 < baseStart_792540 := by decide
  rcases family_descends (prefixWord ++ tailWord_792540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792577 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_792577 : Nat := 118140960795 + 792577 * 2 ^ 59
def prefixEnd_792577 : Nat := 4983230072969 + 3 ^ 40 * 792577 * 2
def baseEnd_792577 : Nat := 271315304465767181695007

theorem tailTrace_792577 : CollatzResearch.WordTrace tailWord_792577 prefixEnd_792577 271315304465767181695007 := by
  unfold tailWord_792577
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907658049636365220039985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19271772033090910146693323 28907658049636365220039985)
  ·
    refine ⟨21680743537227273915029989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28907658049636365220039985 21680743537227273915029989)
    ·
      refine ⟨4065139413230113859068123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21680743537227273915029989 4065139413230113859068123)
      ·
        refine ⟨6097709119845170788602185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065139413230113859068123 6097709119845170788602185)
        ·
          refine ⟨4573281839883878091451639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097709119845170788602185 4573281839883878091451639)
          ·
            refine ⟨6859922759825817137177459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573281839883878091451639 6859922759825817137177459)
            ·
              refine ⟨10289884139738725705766189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859922759825817137177459 10289884139738725705766189)
              ·
                refine ⟨3858706552402022139662321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10289884139738725705766189 3858706552402022139662321)
                ·
                  refine ⟨2894029914301516604746741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3858706552402022139662321 2894029914301516604746741)
                  ·
                    refine ⟨271315304465767181695007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2894029914301516604746741 271315304465767181695007)
                    ·
                      rfl

theorem cell22_792577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_792577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792577 prefixEnd_792577 := by exact prefixLift 792577
  have htrace : WordTrace (prefixWord ++ tailWord_792577) baseStart_792577 baseEnd_792577 := by
    simpa [prefixWord, tailWord_792577, baseEnd_792577] using wordTrace_append hprefix tailTrace_792577
  have hstable : (prefixWord ++ tailWord_792577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792577).length < 2 ^ (prefixWord ++ tailWord_792577).sum := by decide
  have hdescent : baseEnd_792577 < baseStart_792577 := by decide
  rcases family_descends (prefixWord ++ tailWord_792577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792624 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 6]
def baseStart_792624 : Nat := 118140960795 + 792624 * 2 ^ 59
def prefixEnd_792624 : Nat := 4983230072969 + 3 ^ 40 * 792624 * 2
def baseEnd_792624 : Nat := 90443797842091575256621

theorem tailTrace_792624 : CollatzResearch.WordTrace tailWord_792624 prefixEnd_792624 90443797842091575256621 := by
  unfold tailWord_792624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454686140233046123500463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19272914853644061498000617 14454686140233046123500463)
  ·
    refine ⟨21682029210349569185250695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14454686140233046123500463 21682029210349569185250695)
    ·
      refine ⟨32523043815524353777876043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21682029210349569185250695 32523043815524353777876043)
      ·
        refine ⟨48784565723286530666814065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32523043815524353777876043 48784565723286530666814065)
        ·
          refine ⟨36588424292464898000110549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48784565723286530666814065 36588424292464898000110549)
          ·
            refine ⟨857541194354646046877591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36588424292464898000110549 857541194354646046877591)
            ·
              refine ⟨1286311791531969070316387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857541194354646046877591 1286311791531969070316387)
              ·
                refine ⟨1929467687297953605474581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286311791531969070316387 1929467687297953605474581)
                ·
                  refine ⟨90443797842091575256621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1929467687297953605474581 90443797842091575256621)
                  ·
                    rfl

theorem cell22_792624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_792624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792624 prefixEnd_792624 := by exact prefixLift 792624
  have htrace : WordTrace (prefixWord ++ tailWord_792624) baseStart_792624 baseEnd_792624 := by
    simpa [prefixWord, tailWord_792624, baseEnd_792624] using wordTrace_append hprefix tailTrace_792624
  have hstable : (prefixWord ++ tailWord_792624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792624).length < 2 ^ (prefixWord ++ tailWord_792624).sum := by decide
  have hdescent : baseEnd_792624 < baseStart_792624 := by decide
  rcases family_descends (prefixWord ++ tailWord_792624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792652 : List Nat := [2, 2, 1, 3, 1, 1, 4, 8]
def baseStart_792652 : Nat := 118140960795 + 792652 * 2 ^ 59
def prefixEnd_792652 : Nat := 4983230072969 + 3 ^ 40 * 792652 * 2
def baseEnd_792652 : Nat := 30148997610943554007753

theorem tailTrace_792652 : CollatzResearch.WordTrace tailWord_792652 prefixEnd_792652 30148997610943554007753 := by
  unfold tailWord_792652
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455196762182326514510105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19273595682909768686013473 14455196762182326514510105)
  ·
    refine ⟨10841397571636744885882579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14455196762182326514510105 10841397571636744885882579)
    ·
      refine ⟨16262096357455117328823869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10841397571636744885882579 16262096357455117328823869)
      ·
        refine ⟨6098286134045668998308951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16262096357455117328823869 6098286134045668998308951)
        ·
          refine ⟨9147429201068503497463427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098286134045668998308951 9147429201068503497463427)
          ·
            refine ⟨13721143801602755246195141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9147429201068503497463427 13721143801602755246195141)
            ·
              refine ⟨2572714462800516608661589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13721143801602755246195141 2572714462800516608661589)
              ·
                refine ⟨30148997610943554007753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2572714462800516608661589 30148997610943554007753)
                ·
                  rfl

theorem cell22_792652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_792652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792652 prefixEnd_792652 := by exact prefixLift 792652
  have htrace : WordTrace (prefixWord ++ tailWord_792652) baseStart_792652 baseEnd_792652 := by
    simpa [prefixWord, tailWord_792652, baseEnd_792652] using wordTrace_append hprefix tailTrace_792652
  have hstable : (prefixWord ++ tailWord_792652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792652).length < 2 ^ (prefixWord ++ tailWord_792652).sum := by decide
  have hdescent : baseEnd_792652 < baseStart_792652 := by decide
  rcases family_descends (prefixWord ++ tailWord_792652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792654 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_792654 : Nat := 118140960795 + 792654 * 2 ^ 59
def prefixEnd_792654 : Nat := 4983230072969 + 3 ^ 40 * 792654 * 2
def baseEnd_792654 : Nat := 271341663139364647519771

theorem tailTrace_792654 : CollatzResearch.WordTrace tailWord_792654 prefixEnd_792654 271341663139364647519771 := by
  unfold tailWord_792654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613808308794675921324127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19273644313571604913728677 3613808308794675921324127)
  ·
    refine ⟨5420712463192013881986191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613808308794675921324127 5420712463192013881986191)
    ·
      refine ⟨8131068694788020822979287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420712463192013881986191 8131068694788020822979287)
      ·
        refine ⟨12196603042182031234468931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8131068694788020822979287 12196603042182031234468931)
        ·
          refine ⟨18294904563273046851703397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196603042182031234468931 18294904563273046851703397)
          ·
            refine ⟨3430294605613696284694387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18294904563273046851703397 3430294605613696284694387)
            ·
              refine ⟨5145441908420544427041581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430294605613696284694387 5145441908420544427041581)
              ·
                refine ⟨1929540715657704160140593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5145441908420544427041581 1929540715657704160140593)
                ·
                  refine ⟨1447155536743278120105445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1929540715657704160140593 1447155536743278120105445)
                  ·
                    refine ⟨271341663139364647519771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1447155536743278120105445 271341663139364647519771)
                    ·
                      rfl

theorem cell22_792654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_792654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792654 prefixEnd_792654 := by exact prefixLift 792654
  have htrace : WordTrace (prefixWord ++ tailWord_792654) baseStart_792654 baseEnd_792654 := by
    simpa [prefixWord, tailWord_792654, baseEnd_792654] using wordTrace_append hprefix tailTrace_792654
  have hstable : (prefixWord ++ tailWord_792654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792654).length < 2 ^ (prefixWord ++ tailWord_792654).sum := by decide
  have hdescent : baseEnd_792654 < baseStart_792654 := by decide
  rcases family_descends (prefixWord ++ tailWord_792654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792669 : List Nat := [1, 4, 4, 1, 1, 11]
def baseStart_792669 : Nat := 118140960795 + 792669 * 2 ^ 59
def prefixEnd_792669 : Nat := 4983230072969 + 3 ^ 40 * 792669 * 2
def baseEnd_792669 : Nat := 3349960468468019856725

theorem tailTrace_792669 : CollatzResearch.WordTrace tailWord_792669 prefixEnd_792669 3349960468468019856725 := by
  unfold tailWord_792669
  simp only [CollatzResearch.WordTrace]
  refine ⟨28911013565303064932389061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274009043535376621592707 28911013565303064932389061)
  ·
    refine ⟨5420815043494324674822949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28911013565303064932389061 5420815043494324674822949)
    ·
      refine ⟨1016402820655185876529303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5420815043494324674822949 1016402820655185876529303)
      ·
        refine ⟨1524604230982778814793955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016402820655185876529303 1524604230982778814793955)
        ·
          refine ⟨2286906346474168222190933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524604230982778814793955 2286906346474168222190933)
          ·
            refine ⟨3349960468468019856725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2286906346474168222190933 3349960468468019856725)
            ·
              rfl

theorem cell22_792669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 11].length) (baseStart_792669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792669 prefixEnd_792669 := by exact prefixLift 792669
  have htrace : WordTrace (prefixWord ++ tailWord_792669) baseStart_792669 baseEnd_792669 := by
    simpa [prefixWord, tailWord_792669, baseEnd_792669] using wordTrace_append hprefix tailTrace_792669
  have hstable : (prefixWord ++ tailWord_792669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792669).length < 2 ^ (prefixWord ++ tailWord_792669).sum := by decide
  have hdescent : baseEnd_792669 < baseStart_792669 := by decide
  rcases family_descends (prefixWord ++ tailWord_792669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792701 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_792701 : Nat := 118140960795 + 792701 * 2 ^ 59
def prefixEnd_792701 : Nat := 4983230072969 + 3 ^ 40 * 792701 * 2
def baseEnd_792701 : Nat := 271357752199872191594627

theorem tailTrace_792701 : CollatzResearch.WordTrace tailWord_792701 prefixEnd_792701 271357752199872191594627 := by
  unfold tailWord_792701
  simp only [CollatzResearch.WordTrace]
  refine ⟨28912180701187134397553957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274787134124756265035971 28912180701187134397553957)
  ·
    refine ⟨5421033881472587699541367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28912180701187134397553957 5421033881472587699541367)
    ·
      refine ⟨8131550822208881549312051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5421033881472587699541367 8131550822208881549312051)
      ·
        refine ⟨12197326233313322323968077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8131550822208881549312051 12197326233313322323968077)
        ·
          refine ⟨4573997337492495871488029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12197326233313322323968077 4573997337492495871488029)
          ·
            refine ⟨1715249001559685951808011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4573997337492495871488029 1715249001559685951808011)
            ·
              refine ⟨2572873502339528927712017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715249001559685951808011 2572873502339528927712017)
              ·
                refine ⟨1929655126754646695784013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2572873502339528927712017 1929655126754646695784013)
                ·
                  refine ⟨723620672532992510919005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1929655126754646695784013 723620672532992510919005)
                  ·
                    refine ⟨271357752199872191594627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723620672532992510919005 271357752199872191594627)
                    ·
                      rfl

theorem cell22_792701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_792701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792701 prefixEnd_792701 := by exact prefixLift 792701
  have htrace : WordTrace (prefixWord ++ tailWord_792701) baseStart_792701 baseEnd_792701 := by
    simpa [prefixWord, tailWord_792701, baseEnd_792701] using wordTrace_append hprefix tailTrace_792701
  have hstable : (prefixWord ++ tailWord_792701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792701).length < 2 ^ (prefixWord ++ tailWord_792701).sum := by decide
  have hdescent : baseEnd_792701 < baseStart_792701 := by decide
  rcases family_descends (prefixWord ++ tailWord_792701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792759 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 6]
def baseStart_792759 : Nat := 118140960795 + 792759 * 2 ^ 59
def prefixEnd_792759 : Nat := 4983230072969 + 3 ^ 40 * 792759 * 2
def baseEnd_792759 : Nat := 90459202261726457881483

theorem tailTrace_792759 : CollatzResearch.WordTrace tailWord_792759 prefixEnd_792759 90459202261726457881483 := by
  unfold tailWord_792759
  simp only [CollatzResearch.WordTrace]
  refine ⟨28914296134977010303165331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19276197423318006868776887 28914296134977010303165331)
  ·
    refine ⟨43371444202465515454747997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28914296134977010303165331 43371444202465515454747997)
    ·
      refine ⟨16264291575924568295530499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43371444202465515454747997 16264291575924568295530499)
      ·
        refine ⟨24396437363886852443295749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16264291575924568295530499 24396437363886852443295749)
        ·
          refine ⟨4574332005728784833117953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24396437363886852443295749 4574332005728784833117953)
          ·
            refine ⟨3430749004296588624838465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4574332005728784833117953 3430749004296588624838465)
            ·
              refine ⟨2573061753222441468628849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430749004296588624838465 2573061753222441468628849)
              ·
                refine ⟨1929796314916831101471637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573061753222441468628849 1929796314916831101471637)
                ·
                  refine ⟨90459202261726457881483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1929796314916831101471637 90459202261726457881483)
                  ·
                    rfl

theorem cell22_792759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 6].length) (baseStart_792759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792759 prefixEnd_792759 := by exact prefixLift 792759
  have htrace : WordTrace (prefixWord ++ tailWord_792759) baseStart_792759 baseEnd_792759 := by
    simpa [prefixWord, tailWord_792759, baseEnd_792759] using wordTrace_append hprefix tailTrace_792759
  have hstable : (prefixWord ++ tailWord_792759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792759).length < 2 ^ (prefixWord ++ tailWord_792759).sum := by decide
  have hdescent : baseEnd_792759 < baseStart_792759 := by decide
  rcases family_descends (prefixWord ++ tailWord_792759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792761 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_792761 : Nat := 118140960795 + 792761 * 2 ^ 59
def prefixEnd_792761 : Nat := 4983230072969 + 3 ^ 40 * 792761 * 2
def baseEnd_792761 : Nat := 271378291426052035094443

theorem tailTrace_792761 : CollatzResearch.WordTrace tailWord_792761 prefixEnd_792761 271378291426052035094443 := by
  unfold tailWord_792761
  simp only [CollatzResearch.WordTrace]
  refine ⟨28914369080969764644738137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19276246053979843096492091 28914369080969764644738137)
  ·
    refine ⟨21685776810727323483553603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28914369080969764644738137 21685776810727323483553603)
    ·
      refine ⟨32528665216090985225330405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21685776810727323483553603 32528665216090985225330405)
      ·
        refine ⟨6099124728017059729749451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32528665216090985225330405 6099124728017059729749451)
        ·
          refine ⟨9148687092025589594624177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099124728017059729749451 9148687092025589594624177)
          ·
            refine ⟨6861515319019192195968133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9148687092025589594624177 6861515319019192195968133)
            ·
              refine ⟨1286534122316098536744025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6861515319019192195968133 1286534122316098536744025)
              ·
                refine ⟨964900591737073902558019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286534122316098536744025 964900591737073902558019)
                ·
                  refine ⟨1447350887605610853837029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964900591737073902558019 1447350887605610853837029)
                  ·
                    refine ⟨271378291426052035094443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1447350887605610853837029 271378291426052035094443)
                    ·
                      rfl

theorem cell22_792761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_792761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792761 prefixEnd_792761 := by exact prefixLift 792761
  have htrace : WordTrace (prefixWord ++ tailWord_792761) baseStart_792761 baseEnd_792761 := by
    simpa [prefixWord, tailWord_792761, baseEnd_792761] using wordTrace_append hprefix tailTrace_792761
  have hstable : (prefixWord ++ tailWord_792761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792761).length < 2 ^ (prefixWord ++ tailWord_792761).sum := by decide
  have hdescent : baseEnd_792761 < baseStart_792761 := by decide
  rcases family_descends (prefixWord ++ tailWord_792761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792769 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 1, 3]
def baseStart_792769 : Nat := 118140960795 + 792769 * 2 ^ 59
def prefixEnd_792769 : Nat := 4983230072969 + 3 ^ 40 * 792769 * 2
def baseEnd_792769 : Nat := 271381029989542680894419

theorem tailTrace_792769 : CollatzResearch.WordTrace tailWord_792769 prefixEnd_792769 271381029989542680894419 := by
  unfold tailWord_792769
  simp only [CollatzResearch.WordTrace]
  refine ⟨28914660864940782011029361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19276440576627188007352907 28914660864940782011029361)
  ·
    refine ⟨21685995648705586508272021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28914660864940782011029361 21685995648705586508272021)
    ·
      refine ⟨1016531046033074367575251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21685995648705586508272021 1016531046033074367575251)
      ·
        refine ⟨1524796569049611551362877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016531046033074367575251 1524796569049611551362877)
        ·
          refine ⟨571798713393604331761079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1524796569049611551362877 571798713393604331761079)
          ·
            refine ⟨857698070090406497641619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571798713393604331761079 857698070090406497641619)
            ·
              refine ⟨1286547105135609746462429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857698070090406497641619 1286547105135609746462429)
              ·
                refine ⟨482455164425853654923411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1286547105135609746462429 482455164425853654923411)
                ·
                  refine ⟨723682746638780482385117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482455164425853654923411 723682746638780482385117)
                  ·
                    refine ⟨271381029989542680894419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723682746638780482385117 271381029989542680894419)
                    ·
                      rfl

theorem cell22_792769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_792769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792769 prefixEnd_792769 := by exact prefixLift 792769
  have htrace : WordTrace (prefixWord ++ tailWord_792769) baseStart_792769 baseEnd_792769 := by
    simpa [prefixWord, tailWord_792769, baseEnd_792769] using wordTrace_append hprefix tailTrace_792769
  have hstable : (prefixWord ++ tailWord_792769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792769).length < 2 ^ (prefixWord ++ tailWord_792769).sum := by decide
  have hdescent : baseEnd_792769 < baseStart_792769 := by decide
  rcases family_descends (prefixWord ++ tailWord_792769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792791 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 2, 3]
def baseStart_792791 : Nat := 118140960795 + 792791 * 2 ^ 59
def prefixEnd_792791 : Nat := 4983230072969 + 3 ^ 40 * 792791 * 2
def baseEnd_792791 : Nat := 271388561039141956844351

theorem tailTrace_792791 : CollatzResearch.WordTrace tailWord_792791 prefixEnd_792791 271388561039141956844351 := by
  unfold tailWord_792791
  simp only [CollatzResearch.WordTrace]
  refine ⟨28915463270861079768330227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19276975513907386512220151 28915463270861079768330227)
  ·
    refine ⟨43373194906291619652495341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28915463270861079768330227 43373194906291619652495341)
    ·
      refine ⟨16264948089859357369685753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43373194906291619652495341 16264948089859357369685753)
      ·
        refine ⟨12198711067394518027264315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16264948089859357369685753 12198711067394518027264315)
        ·
          refine ⟨18298066601091777040896473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12198711067394518027264315 18298066601091777040896473)
          ·
            refine ⟨13723549950818832780672355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18298066601091777040896473 13723549950818832780672355)
            ·
              refine ⟨20585324926228249171008533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13723549950818832780672355 20585324926228249171008533)
              ·
                refine ⟨964937105916949179891025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20585324926228249171008533 964937105916949179891025)
                ·
                  refine ⟨723702829437711884918269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964937105916949179891025 723702829437711884918269)
                  ·
                    refine ⟨271388561039141956844351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723702829437711884918269 271388561039141956844351)
                    ·
                      rfl

theorem cell22_792791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_792791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792791 prefixEnd_792791 := by exact prefixLift 792791
  have htrace : WordTrace (prefixWord ++ tailWord_792791) baseStart_792791 baseEnd_792791 := by
    simpa [prefixWord, tailWord_792791, baseEnd_792791] using wordTrace_append hprefix tailTrace_792791
  have hstable : (prefixWord ++ tailWord_792791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792791).length < 2 ^ (prefixWord ++ tailWord_792791).sum := by decide
  have hdescent : baseEnd_792791 < baseStart_792791 := by decide
  rcases family_descends (prefixWord ++ tailWord_792791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792808 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_792808 : Nat := 118140960795 + 792808 * 2 ^ 59
def prefixEnd_792808 : Nat := 4983230072969 + 3 ^ 40 * 792808 * 2
def baseEnd_792808 : Nat := 271394380486559579169299

theorem tailTrace_792808 : CollatzResearch.WordTrace tailWord_792808 prefixEnd_792808 271394380486559579169299 := by
  unfold tailWord_792808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14458041655899745835849539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19277388874532994447799385 14458041655899745835849539)
  ·
    refine ⟨21687062483849618753774309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14458041655899745835849539 21687062483849618753774309)
    ·
      refine ⟨4066324215721803516332683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21687062483849618753774309 4066324215721803516332683)
      ·
        refine ⟨6099486323582705274499025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066324215721803516332683 6099486323582705274499025)
        ·
          refine ⟨4574614742687028955874269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6099486323582705274499025 4574614742687028955874269)
          ·
            refine ⟨1715480528507635858452851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4574614742687028955874269 1715480528507635858452851)
            ·
              refine ⟨2573220792761453787679277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715480528507635858452851 2573220792761453787679277)
              ·
                refine ⟨964957797285545170379729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573220792761453787679277 964957797285545170379729)
                ·
                  refine ⟨723718347964158877784797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964957797285545170379729 723718347964158877784797)
                  ·
                    refine ⟨271394380486559579169299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 723718347964158877784797 271394380486559579169299)
                    ·
                      rfl

theorem cell22_792808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_792808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792808 prefixEnd_792808 := by exact prefixLift 792808
  have htrace : WordTrace (prefixWord ++ tailWord_792808) baseStart_792808 baseEnd_792808 := by
    simpa [prefixWord, tailWord_792808, baseEnd_792808] using wordTrace_append hprefix tailTrace_792808
  have hstable : (prefixWord ++ tailWord_792808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792808).length < 2 ^ (prefixWord ++ tailWord_792808).sum := by decide
  have hdescent : baseEnd_792808 < baseStart_792808 := by decide
  rcases family_descends (prefixWord ++ tailWord_792808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792930 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_792930 : Nat := 118140960795 + 792930 * 2 ^ 59
def prefixEnd_792930 : Nat := 4983230072969 + 3 ^ 40 * 792930 * 2
def baseEnd_792930 : Nat := 271436143579791927618925

theorem tailTrace_792930 : CollatzResearch.WordTrace tailWord_792930 prefixEnd_792930 271436143579791927618925 := by
  unfold tailWord_792930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7230133254339376626910061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19280355344905004338426829 7230133254339376626910061)
  ·
    refine ⟨2711299970377266235091273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7230133254339376626910061 2711299970377266235091273)
    ·
      refine ⟨2033474977782949676318455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2711299970377266235091273 2033474977782949676318455)
      ·
        refine ⟨3050212466674424514477683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033474977782949676318455 3050212466674424514477683)
        ·
          refine ⟨4575318700011636771716525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050212466674424514477683 4575318700011636771716525)
          ·
            refine ⟨1715744512504363789393697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4575318700011636771716525 1715744512504363789393697)
            ·
              refine ⟨1286808384378272842045273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715744512504363789393697 1286808384378272842045273)
              ·
                refine ⟨965106288283704631533955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286808384378272842045273 965106288283704631533955)
                ·
                  refine ⟨1447659432425556947300933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965106288283704631533955 1447659432425556947300933)
                  ·
                    refine ⟨271436143579791927618925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1447659432425556947300933 271436143579791927618925)
                    ·
                      rfl

theorem cell22_792930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_792930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792930 prefixEnd_792930 := by exact prefixLift 792930
  have htrace : WordTrace (prefixWord ++ tailWord_792930) baseStart_792930 baseEnd_792930 := by
    simpa [prefixWord, tailWord_792930, baseEnd_792930] using wordTrace_append hprefix tailTrace_792930
  have hstable : (prefixWord ++ tailWord_792930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792930).length < 2 ^ (prefixWord ++ tailWord_792930).sum := by decide
  have hdescent : baseEnd_792930 < baseStart_792930 := by decide
  rcases family_descends (prefixWord ++ tailWord_792930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792939 : List Nat := [1, 1, 1, 1, 2, 2, 2, 12]
def baseStart_792939 : Nat := 118140960795 + 792939 * 2 ^ 59
def prefixEnd_792939 : Nat := 4983230072969 + 3 ^ 40 * 792939 * 2
def baseEnd_792939 : Nat := 30159913829302100460433

theorem tailTrace_792939 : CollatzResearch.WordTrace tailWord_792939 prefixEnd_792939 30159913829302100460433 := by
  unfold tailWord_792939
  simp only [CollatzResearch.WordTrace]
  refine ⟨28920861274324901044717871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19280574182883267363145247 28920861274324901044717871)
  ·
    refine ⟨43381291911487351567076807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28920861274324901044717871 43381291911487351567076807)
    ·
      refine ⟨65071937867231027350615211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43381291911487351567076807 65071937867231027350615211)
      ·
        refine ⟨97607906800846541025922817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65071937867231027350615211 97607906800846541025922817)
        ·
          refine ⟨73205930100634905769442113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97607906800846541025922817 73205930100634905769442113)
          ·
            refine ⟨54904447575476179327081585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73205930100634905769442113 54904447575476179327081585)
            ·
              refine ⟨41178335681607134495311189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54904447575476179327081585 41178335681607134495311189)
              ·
                refine ⟨30159913829302100460433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 41178335681607134495311189 30159913829302100460433)
                ·
                  rfl

theorem cell22_792939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 12].length) (baseStart_792939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792939 prefixEnd_792939 := by exact prefixLift 792939
  have htrace : WordTrace (prefixWord ++ tailWord_792939) baseStart_792939 baseEnd_792939 := by
    simpa [prefixWord, tailWord_792939, baseEnd_792939] using wordTrace_append hprefix tailTrace_792939
  have hstable : (prefixWord ++ tailWord_792939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792939).length < 2 ^ (prefixWord ++ tailWord_792939).sum := by decide
  have hdescent : baseEnd_792939 < baseStart_792939 := by decide
  rcases family_descends (prefixWord ++ tailWord_792939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792941 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_792941 : Nat := 118140960795 + 792941 * 2 ^ 59
def prefixEnd_792941 : Nat := 4983230072969 + 3 ^ 40 * 792941 * 2
def baseEnd_792941 : Nat := 271439909104591565593891

theorem tailTrace_792941 : CollatzResearch.WordTrace tailWord_792941 prefixEnd_792941 271439909104591565593891 := by
  unfold tailWord_792941
  simp only [CollatzResearch.WordTrace]
  refine ⟨28920934220317655386290677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19280622813545103590860451 28920934220317655386290677)
  ·
    refine ⟨2711337583154780192464751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28920934220317655386290677 2711337583154780192464751)
    ·
      refine ⟨4067006374732170288697127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2711337583154780192464751 4067006374732170288697127)
      ·
        refine ⟨6100509562098255433045691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067006374732170288697127 6100509562098255433045691)
        ·
          refine ⟨9150764343147383149568537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100509562098255433045691 9150764343147383149568537)
          ·
            refine ⟨6863073257360537362176403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9150764343147383149568537 6863073257360537362176403)
            ·
              refine ⟨10294609886040806043264605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863073257360537362176403 10294609886040806043264605)
              ·
                refine ⟨3860478707265302266224227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10294609886040806043264605 3860478707265302266224227)
                ·
                  refine ⟨5790718060897953399336341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3860478707265302266224227 5790718060897953399336341)
                  ·
                    refine ⟨271439909104591565593891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5790718060897953399336341 271439909104591565593891)
                    ·
                      rfl

theorem cell22_792941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_792941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792941 prefixEnd_792941 := by exact prefixLift 792941
  have htrace : WordTrace (prefixWord ++ tailWord_792941) baseStart_792941 baseEnd_792941 := by
    simpa [prefixWord, tailWord_792941, baseEnd_792941] using wordTrace_append hprefix tailTrace_792941
  have hstable : (prefixWord ++ tailWord_792941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792941).length < 2 ^ (prefixWord ++ tailWord_792941).sum := by decide
  have hdescent : baseEnd_792941 < baseStart_792941 := by decide
  rcases family_descends (prefixWord ++ tailWord_792941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792962 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 6]
def baseStart_792962 : Nat := 118140960795 + 792962 * 2 ^ 59
def prefixEnd_792962 : Nat := 4983230072969 + 3 ^ 40 * 792962 * 2
def baseEnd_792962 : Nat := 90482365944584836939609

theorem tailTrace_792962 : CollatzResearch.WordTrace tailWord_792962 prefixEnd_792962 90482365944584836939609 := by
  unfold tailWord_792962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7230425038310393993201285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19281133435494383981870093 7230425038310393993201285)
  ·
    refine ⟨1355704694683198873725241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7230425038310393993201285 1355704694683198873725241)
    ·
      refine ⟨1016778521012399155293931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1355704694683198873725241 1016778521012399155293931)
      ·
        refine ⟨1525167781518598732940897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016778521012399155293931 1525167781518598732940897)
        ·
          refine ⟨1143875836138949049705673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525167781518598732940897 1143875836138949049705673)
          ·
            refine ⟨857906877104211787279255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143875836138949049705673 857906877104211787279255)
            ·
              refine ⟨1286860315656317680918883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857906877104211787279255 1286860315656317680918883)
              ·
                refine ⟨1930290473484476521378325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286860315656317680918883 1930290473484476521378325)
                ·
                  refine ⟨90482365944584836939609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1930290473484476521378325 90482365944584836939609)
                  ·
                    rfl

theorem cell22_792962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_792962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_792962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_792962 prefixEnd_792962 := by exact prefixLift 792962
  have htrace : WordTrace (prefixWord ++ tailWord_792962) baseStart_792962 baseEnd_792962 := by
    simpa [prefixWord, tailWord_792962, baseEnd_792962] using wordTrace_append hprefix tailTrace_792962
  have hstable : (prefixWord ++ tailWord_792962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792962).length < 2 ^ (prefixWord ++ tailWord_792962).sum := by decide
  have hdescent : baseEnd_792962 < baseStart_792962 := by decide
  rcases family_descends (prefixWord ++ tailWord_792962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793016 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_793016 : Nat := 118140960795 + 793016 * 2 ^ 59
def prefixEnd_793016 : Nat := 4983230072969 + 3 ^ 40 * 793016 * 2
def baseEnd_793016 : Nat := 271465583137316369968661

theorem tailTrace_793016 : CollatzResearch.WordTrace tailWord_793016 prefixEnd_793016 271465583137316369968661 := by
  unfold tailWord_793016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461834847522971597635451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19282446463363962130180601 14461834847522971597635451)
  ·
    refine ⟨21692752271284457396453177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14461834847522971597635451 21692752271284457396453177)
    ·
      refine ⟨16269564203463343047339883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21692752271284457396453177 16269564203463343047339883)
      ·
        refine ⟨24404346305195014571009825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16269564203463343047339883 24404346305195014571009825)
        ·
          refine ⟨18303259728896260928257369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24404346305195014571009825 18303259728896260928257369)
          ·
            refine ⟨13727444796672195696193027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18303259728896260928257369 13727444796672195696193027)
            ·
              refine ⟨20591167195008293544289541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13727444796672195696193027 20591167195008293544289541)
              ·
                refine ⟨3860843849064055039554289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20591167195008293544289541 3860843849064055039554289)
                ·
                  refine ⟨2895632886798041279665717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3860843849064055039554289 2895632886798041279665717)
                  ·
                    refine ⟨271465583137316369968661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2895632886798041279665717 271465583137316369968661)
                    ·
                      rfl

theorem cell22_793016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_793016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793016 prefixEnd_793016 := by exact prefixLift 793016
  have htrace : WordTrace (prefixWord ++ tailWord_793016) baseStart_793016 baseEnd_793016 := by
    simpa [prefixWord, tailWord_793016, baseEnd_793016] using wordTrace_append hprefix tailTrace_793016
  have hstable : (prefixWord ++ tailWord_793016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793016).length < 2 ^ (prefixWord ++ tailWord_793016).sum := by decide
  have hdescent : baseEnd_793016 < baseStart_793016 := by decide
  rcases family_descends (prefixWord ++ tailWord_793016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793048 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_793048 : Nat := 118140960795 + 793048 * 2 ^ 59
def prefixEnd_793048 : Nat := 4983230072969 + 3 ^ 40 * 793048 * 2
def baseEnd_793048 : Nat := 271476537391278953168563

theorem tailTrace_793048 : CollatzResearch.WordTrace tailWord_793048 prefixEnd_793048 271476537391278953168563 := by
  unfold tailWord_793048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14462418415465006330217899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19283224553953341773623865 14462418415465006330217899)
  ·
    refine ⟨21693627623197509495326849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14462418415465006330217899 21693627623197509495326849)
    ·
      refine ⟨16270220717398132121495137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21693627623197509495326849 16270220717398132121495137)
      ·
        refine ⟨12202665538048599091121353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16270220717398132121495137 12202665538048599091121353)
        ·
          refine ⟨9151999153536449318341015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12202665538048599091121353 9151999153536449318341015)
          ·
            refine ⟨13727998730304673977511523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9151999153536449318341015 13727998730304673977511523)
            ·
              refine ⟨20591998095457010966267285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13727998730304673977511523 20591998095457010966267285)
              ·
                refine ⟨965249910724547389043779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20591998095457010966267285 965249910724547389043779)
                ·
                  refine ⟨1447874866086821083565669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965249910724547389043779 1447874866086821083565669)
                  ·
                    refine ⟨271476537391278953168563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1447874866086821083565669 271476537391278953168563)
                    ·
                      rfl

theorem cell22_793048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_793048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793048 prefixEnd_793048 := by exact prefixLift 793048
  have htrace : WordTrace (prefixWord ++ tailWord_793048) baseStart_793048 baseEnd_793048 := by
    simpa [prefixWord, tailWord_793048, baseEnd_793048] using wordTrace_append hprefix tailTrace_793048
  have hstable : (prefixWord ++ tailWord_793048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793048).length < 2 ^ (prefixWord ++ tailWord_793048).sum := by decide
  have hdescent : baseEnd_793048 < baseStart_793048 := by decide
  rcases family_descends (prefixWord ++ tailWord_793048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793091 : List Nat := [1, 1, 1, 3, 2, 1, 4, 9]
def baseStart_793091 : Nat := 118140960795 + 793091 * 2 ^ 59
def prefixEnd_793091 : Nat := 4983230072969 + 3 ^ 40 * 793091 * 2
def baseEnd_793091 : Nat := 30165695241115686038159

theorem tailTrace_793091 : CollatzResearch.WordTrace tailWord_793091 prefixEnd_793091 30165695241115686038159 := by
  unfold tailWord_793091
  simp only [CollatzResearch.WordTrace]
  refine ⟨28926405169774231004251127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19284270113182820669500751 28926405169774231004251127)
  ·
    refine ⟨43389607754661346506376691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28926405169774231004251127 43389607754661346506376691)
    ·
      refine ⟨65084411631992019759565037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43389607754661346506376691 65084411631992019759565037)
      ·
        refine ⟨24406654361997007409836889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65084411631992019759565037 24406654361997007409836889)
        ·
          refine ⟨18304990771497755557377667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24406654361997007409836889 18304990771497755557377667)
          ·
            refine ⟨27457486157246633336066501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18304990771497755557377667 27457486157246633336066501)
            ·
              refine ⟨5148278654483743750512469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27457486157246633336066501 5148278654483743750512469)
              ·
                refine ⟨30165695241115686038159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5148278654483743750512469 30165695241115686038159)
                ·
                  rfl

theorem cell22_793091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 9].length) (baseStart_793091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793091 prefixEnd_793091 := by exact prefixLift 793091
  have htrace : WordTrace (prefixWord ++ tailWord_793091) baseStart_793091 baseEnd_793091 := by
    simpa [prefixWord, tailWord_793091, baseEnd_793091] using wordTrace_append hprefix tailTrace_793091
  have hstable : (prefixWord ++ tailWord_793091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793091).length < 2 ^ (prefixWord ++ tailWord_793091).sum := by decide
  have hdescent : baseEnd_793091 < baseStart_793091 := by decide
  rcases family_descends (prefixWord ++ tailWord_793091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793230 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 1, 5]
def baseStart_793230 : Nat := 118140960795 + 793230 * 2 ^ 59
def prefixEnd_793230 : Nat := 4983230072969 + 3 ^ 40 * 793230 * 2
def baseEnd_793230 : Nat := 271538839710691145118005

theorem tailTrace_793230 : CollatzResearch.WordTrace tailWord_793230 prefixEnd_793230 271538839710691145118005 := by
  unfold tailWord_793230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616434364533832217945143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19287649944180438495707429 3616434364533832217945143)
  ·
    refine ⟨5424651546800748326917715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3616434364533832217945143 5424651546800748326917715)
    ·
      refine ⟨8136977320201122490376573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424651546800748326917715 8136977320201122490376573)
      ·
        refine ⟨3051366495075420933891215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8136977320201122490376573 3051366495075420933891215)
        ·
          refine ⟨4577049742613131400836823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051366495075420933891215 4577049742613131400836823)
          ·
            refine ⟨6865574613919697101255235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577049742613131400836823 6865574613919697101255235)
            ·
              refine ⟨10298361920879545651882853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865574613919697101255235 10298361920879545651882853)
              ·
                refine ⟨1930942860164914809728035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10298361920879545651882853 1930942860164914809728035)
                ·
                  refine ⟨2896414290247372214592053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1930942860164914809728035 2896414290247372214592053)
                  ·
                    refine ⟨271538839710691145118005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2896414290247372214592053 271538839710691145118005)
                    ·
                      rfl

theorem cell22_793230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_793230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793230 prefixEnd_793230 := by exact prefixLift 793230
  have htrace : WordTrace (prefixWord ++ tailWord_793230) baseStart_793230 baseEnd_793230 := by
    simpa [prefixWord, tailWord_793230, baseEnd_793230] using wordTrace_append hprefix tailTrace_793230
  have hstable : (prefixWord ++ tailWord_793230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793230).length < 2 ^ (prefixWord ++ tailWord_793230).sum := by decide
  have hdescent : baseEnd_793230 < baseStart_793230 := by decide
  rcases family_descends (prefixWord ++ tailWord_793230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793234 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_793234 : Nat := 118140960795 + 793234 * 2 ^ 59
def prefixEnd_793234 : Nat := 4983230072969 + 3 ^ 40 * 793234 * 2
def baseEnd_793234 : Nat := 271540208992436468017993

theorem tailTrace_793234 : CollatzResearch.WordTrace tailWord_793234 prefixEnd_793234 271540208992436468017993 := by
  unfold tailWord_793234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232905202064041606676689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19287747205504110951137837 7232905202064041606676689)
  ·
    refine ⟨5424678901548031205007517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7232905202064041606676689 5424678901548031205007517)
    ·
      refine ⟨2034254588080511701877819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5424678901548031205007517 2034254588080511701877819)
      ·
        refine ⟨3051381882120767552816729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034254588080511701877819 3051381882120767552816729)
        ·
          refine ⟨2288536411590575664612547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051381882120767552816729 2288536411590575664612547)
          ·
            refine ⟨3432804617385863496918821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288536411590575664612547 3432804617385863496918821)
            ·
              refine ⟨643650865759849405672279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3432804617385863496918821 643650865759849405672279)
              ·
                refine ⟨965476298639774108508419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643650865759849405672279 965476298639774108508419)
                ·
                  refine ⟨1448214447959661162762629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965476298639774108508419 1448214447959661162762629)
                  ·
                    refine ⟨271540208992436468017993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448214447959661162762629 271540208992436468017993)
                    ·
                      rfl

theorem cell22_793234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_793234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793234 prefixEnd_793234 := by exact prefixLift 793234
  have htrace : WordTrace (prefixWord ++ tailWord_793234) baseStart_793234 baseEnd_793234 := by
    simpa [prefixWord, tailWord_793234, baseEnd_793234] using wordTrace_append hprefix tailTrace_793234
  have hstable : (prefixWord ++ tailWord_793234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793234).length < 2 ^ (prefixWord ++ tailWord_793234).sum := by decide
  have hdescent : baseEnd_793234 < baseStart_793234 := by decide
  rcases family_descends (prefixWord ++ tailWord_793234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793245 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_793245 : Nat := 118140960795 + 793245 * 2 ^ 59
def prefixEnd_793245 : Nat := 4983230072969 + 3 ^ 40 * 793245 * 2
def baseEnd_793245 : Nat := 271543974517236105992959

theorem tailTrace_793245 : CollatzResearch.WordTrace tailWord_793245 prefixEnd_793245 271543974517236105992959 := by
  unfold tailWord_793245
  simp only [CollatzResearch.WordTrace]
  refine ⟨28932022011216315305357189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19288014674144210203571459 28932022011216315305357189)
  ·
    refine ⟨5424754127103059119754473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28932022011216315305357189 5424754127103059119754473)
    ·
      refine ⟨4068565595327294339815855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5424754127103059119754473 4068565595327294339815855)
      ·
        refine ⟨6102848392990941509723783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068565595327294339815855 6102848392990941509723783)
        ·
          refine ⟨9154272589486412264585675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6102848392990941509723783 9154272589486412264585675)
          ·
            refine ⟨13731408884229618396878513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9154272589486412264585675 13731408884229618396878513)
            ·
              refine ⟨10298556663172213797658885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13731408884229618396878513 10298556663172213797658885)
              ·
                refine ⟨1930979374344790087061041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10298556663172213797658885 1930979374344790087061041)
                ·
                  refine ⟨1448234530758592565295781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1930979374344790087061041 1448234530758592565295781)
                  ·
                    refine ⟨271543974517236105992959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448234530758592565295781 271543974517236105992959)
                    ·
                      rfl

theorem cell22_793245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_793245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793245 prefixEnd_793245 := by exact prefixLift 793245
  have htrace : WordTrace (prefixWord ++ tailWord_793245) baseStart_793245 baseEnd_793245 := by
    simpa [prefixWord, tailWord_793245, baseEnd_793245] using wordTrace_append hprefix tailTrace_793245
  have hstable : (prefixWord ++ tailWord_793245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793245).length < 2 ^ (prefixWord ++ tailWord_793245).sum := by decide
  have hdescent : baseEnd_793245 < baseStart_793245 := by decide
  rcases family_descends (prefixWord ++ tailWord_793245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793262 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_793262 : Nat := 118140960795 + 793262 * 2 ^ 59
def prefixEnd_793262 : Nat := 4983230072969 + 3 ^ 40 * 793262 * 2
def baseEnd_793262 : Nat := 271549793964653728317907

theorem tailTrace_793262 : CollatzResearch.WordTrace tailWord_793262 prefixEnd_793262 271549793964653728317907 := by
  unfold tailWord_793262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3616580256519340901090755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19288428034769818139150693 3616580256519340901090755)
  ·
    refine ⟨5424870384779011351636133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3616580256519340901090755 5424870384779011351636133)
    ·
      refine ⟨1017163197146064628431775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5424870384779011351636133 1017163197146064628431775)
      ·
        refine ⟨1525744795719096942647663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017163197146064628431775 1525744795719096942647663)
        ·
          refine ⟨2288617193578645413971495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525744795719096942647663 2288617193578645413971495)
          ·
            refine ⟨3432925790367968120957243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288617193578645413971495 3432925790367968120957243)
            ·
              refine ⟨5149388685551952181435865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3432925790367968120957243 5149388685551952181435865)
              ·
                refine ⟨3862041514163964136076899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5149388685551952181435865 3862041514163964136076899)
                ·
                  refine ⟨5793062271245946204115349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862041514163964136076899 5793062271245946204115349)
                  ·
                    refine ⟨271549793964653728317907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5793062271245946204115349 271549793964653728317907)
                    ·
                      rfl

theorem cell22_793262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_793262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793262 prefixEnd_793262 := by exact prefixLift 793262
  have htrace : WordTrace (prefixWord ++ tailWord_793262) baseStart_793262 baseEnd_793262 := by
    simpa [prefixWord, tailWord_793262, baseEnd_793262] using wordTrace_append hprefix tailTrace_793262
  have hstable : (prefixWord ++ tailWord_793262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793262).length < 2 ^ (prefixWord ++ tailWord_793262).sum := by decide
  have hdescent : baseEnd_793262 < baseStart_793262 := by decide
  rcases family_descends (prefixWord ++ tailWord_793262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793277 : List Nat := [1, 4, 1, 2, 1, 5, 2, 6]
def baseStart_793277 : Nat := 118140960795 + 793277 * 2 ^ 59
def prefixEnd_793277 : Nat := 4983230072969 + 3 ^ 40 * 793277 * 2
def baseEnd_793277 : Nat := 30172769863466521021429

theorem tailTrace_793277 : CollatzResearch.WordTrace tailWord_793277 prefixEnd_793277 30172769863466521021429 := by
  unfold tailWord_793277
  simp only [CollatzResearch.WordTrace]
  refine ⟨28933189147100384770522085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19288792764733589847014723 28933189147100384770522085)
  ·
    refine ⟨5424972965081322144472891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28933189147100384770522085 5424972965081322144472891)
    ·
      refine ⟨8137459447621983216709337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424972965081322144472891 8137459447621983216709337)
      ·
        refine ⟨6103094585716487412532003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8137459447621983216709337 6103094585716487412532003)
        ·
          refine ⟨9154641878574731118798005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103094585716487412532003 9154641878574731118798005)
          ·
            refine ⟨858247676116381042387313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9154641878574731118798005 858247676116381042387313)
            ·
              refine ⟨643685757087285781790485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858247676116381042387313 643685757087285781790485)
              ·
                refine ⟨30172769863466521021429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 643685757087285781790485 30172769863466521021429)
                ·
                  rfl

theorem cell22_793277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 6].length) (baseStart_793277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793277 prefixEnd_793277 := by exact prefixLift 793277
  have htrace : WordTrace (prefixWord ++ tailWord_793277) baseStart_793277 baseEnd_793277 := by
    simpa [prefixWord, tailWord_793277, baseEnd_793277] using wordTrace_append hprefix tailTrace_793277
  have hstable : (prefixWord ++ tailWord_793277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793277).length < 2 ^ (prefixWord ++ tailWord_793277).sum := by decide
  have hdescent : baseEnd_793277 < baseStart_793277 := by decide
  rcases family_descends (prefixWord ++ tailWord_793277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793305 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 5]
def baseStart_793305 : Nat := 118140960795 + 793305 * 2 ^ 59
def prefixEnd_793305 : Nat := 4983230072969 + 3 ^ 40 * 793305 * 2
def baseEnd_793305 : Nat := 90521504581138649830925

theorem tailTrace_793305 : CollatzResearch.WordTrace tailWord_793305 prefixEnd_793305 90521504581138649830925 := by
  unfold tailWord_793305
  simp only [CollatzResearch.WordTrace]
  refine ⟨28934210390998945552541369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19289473593999297035027579 28934210390998945552541369)
  ·
    refine ⟨21700657793249209164406027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28934210390998945552541369 21700657793249209164406027)
    ·
      refine ⟨32550986689873813746609041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21700657793249209164406027 32550986689873813746609041)
      ·
        refine ⟨24413240017405360309956781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32550986689873813746609041 24413240017405360309956781)
        ·
          refine ⟨9154965006527010116233793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24413240017405360309956781 9154965006527010116233793)
          ·
            refine ⟨6866223754895257587175345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9154965006527010116233793 6866223754895257587175345)
            ·
              refine ⟨5149667816171443190381509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6866223754895257587175345 5149667816171443190381509)
              ·
                refine ⟨965562715532145598196533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5149667816171443190381509 965562715532145598196533)
                ·
                  refine ⟨90521504581138649830925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 965562715532145598196533 90521504581138649830925)
                  ·
                    rfl

theorem cell22_793305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_793305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793305 prefixEnd_793305 := by exact prefixLift 793305
  have htrace : WordTrace (prefixWord ++ tailWord_793305) baseStart_793305 baseEnd_793305 := by
    simpa [prefixWord, tailWord_793305, baseEnd_793305] using wordTrace_append hprefix tailTrace_793305
  have hstable : (prefixWord ++ tailWord_793305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793305).length < 2 ^ (prefixWord ++ tailWord_793305).sum := by decide
  have hdescent : baseEnd_793305 < baseStart_793305 := by decide
  rcases family_descends (prefixWord ++ tailWord_793305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793365 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_793365 : Nat := 118140960795 + 793365 * 2 ^ 59
def prefixEnd_793365 : Nat := 4983230072969 + 3 ^ 40 * 793365 * 2
def baseEnd_793365 : Nat := 271585052969595792992591

theorem tailTrace_793365 : CollatzResearch.WordTrace tailWord_793365 prefixEnd_793365 271585052969595792992591 := by
  unfold tailWord_793365
  simp only [CollatzResearch.WordTrace]
  refine ⟨28936398770781575799725549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19290932513854383866483699 28936398770781575799725549)
  ·
    refine ⟨10851149539043090924897081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28936398770781575799725549 10851149539043090924897081)
    ·
      refine ⟨8138362154282318193672811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10851149539043090924897081 8138362154282318193672811)
      ·
        refine ⟨12207543231423477290509217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8138362154282318193672811 12207543231423477290509217)
        ·
          refine ⟨9155657423567607967881913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12207543231423477290509217 9155657423567607967881913)
          ·
            refine ⟨6866743067675705975911435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9155657423567607967881913 6866743067675705975911435)
            ·
              refine ⟨10300114601513558963867153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866743067675705975911435 10300114601513558963867153)
              ·
                refine ⟨7725085951135169222900365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10300114601513558963867153 7725085951135169222900365)
                ·
                  refine ⟨2896907231675688458587637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7725085951135169222900365 2896907231675688458587637)
                  ·
                    refine ⟨271585052969595792992591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2896907231675688458587637 271585052969595792992591)
                    ·
                      rfl

theorem cell22_793365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_793365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793365 prefixEnd_793365 := by exact prefixLift 793365
  have htrace : WordTrace (prefixWord ++ tailWord_793365) baseStart_793365 baseEnd_793365 := by
    simpa [prefixWord, tailWord_793365, baseEnd_793365] using wordTrace_append hprefix tailTrace_793365
  have hstable : (prefixWord ++ tailWord_793365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793365).length < 2 ^ (prefixWord ++ tailWord_793365).sum := by decide
  have hdescent : baseEnd_793365 < baseStart_793365 := by decide
  rcases family_descends (prefixWord ++ tailWord_793365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793397 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_793397 : Nat := 118140960795 + 793397 * 2 ^ 59
def prefixEnd_793397 : Nat := 4983230072969 + 3 ^ 40 * 793397 * 2
def baseEnd_793397 : Nat := 271596007223558376192493

theorem tailTrace_793397 : CollatzResearch.WordTrace tailWord_793397 prefixEnd_793397 271596007223558376192493 := by
  unfold tailWord_793397
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937565906665645264890445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19291710604443763509926963 28937565906665645264890445)
  ·
    refine ⟨10851587214999616974333917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28937565906665645264890445 10851587214999616974333917)
    ·
      refine ⟨4069345205624856365375219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10851587214999616974333917 4069345205624856365375219)
      ·
        refine ⟨6104017808437284548062829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069345205624856365375219 6104017808437284548062829)
        ·
          refine ⟨2289006678163981705523561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6104017808437284548062829 2289006678163981705523561)
          ·
            refine ⟨1716755008622986279142671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289006678163981705523561 1716755008622986279142671)
            ·
              refine ⟨2575132512934479418714007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716755008622986279142671 2575132512934479418714007)
              ·
                refine ⟨3862698769401719128071011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575132512934479418714007 3862698769401719128071011)
                ·
                  refine ⟨5794048154102578692106517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3862698769401719128071011 5794048154102578692106517)
                  ·
                    refine ⟨271596007223558376192493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5794048154102578692106517 271596007223558376192493)
                    ·
                      rfl

theorem cell22_793397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_793397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793397 prefixEnd_793397 := by exact prefixLift 793397
  have htrace : WordTrace (prefixWord ++ tailWord_793397) baseStart_793397 baseEnd_793397 := by
    simpa [prefixWord, tailWord_793397, baseEnd_793397] using wordTrace_append hprefix tailTrace_793397
  have hstable : (prefixWord ++ tailWord_793397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793397).length < 2 ^ (prefixWord ++ tailWord_793397).sum := by decide
  have hdescent : baseEnd_793397 < baseStart_793397 := by decide
  rcases family_descends (prefixWord ++ tailWord_793397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793444 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_793444 : Nat := 118140960795 + 793444 * 2 ^ 59
def prefixEnd_793444 : Nat := 4983230072969 + 3 ^ 40 * 793444 * 2
def baseEnd_793444 : Nat := 271612096284065920267349

theorem tailTrace_793444 : CollatzResearch.WordTrace tailWord_793444 prefixEnd_793444 271612096284065920267349 := by
  unfold tailWord_793444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14469640068747686145925693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19292853424996914861234257 14469640068747686145925693)
  ·
    refine ⟨5426115025780382304722135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14469640068747686145925693 5426115025780382304722135)
    ·
      refine ⟨8139172538670573457083203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5426115025780382304722135 8139172538670573457083203)
      ·
        refine ⟨12208758808005860185624805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8139172538670573457083203 12208758808005860185624805)
        ·
          refine ⟨2289142276501098784804651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12208758808005860185624805 2289142276501098784804651)
          ·
            refine ⟨3433713414751648177206977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289142276501098784804651 3433713414751648177206977)
            ·
              refine ⟨2575285061063736132905233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3433713414751648177206977 2575285061063736132905233)
              ·
                refine ⟨1931463795797802099678925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575285061063736132905233 1931463795797802099678925)
                ·
                  refine ⟨724298923424175787379597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1931463795797802099678925 724298923424175787379597)
                  ·
                    refine ⟨271612096284065920267349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724298923424175787379597 271612096284065920267349)
                    ·
                      rfl

theorem cell22_793444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_793444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793444 prefixEnd_793444 := by exact prefixLift 793444
  have htrace : WordTrace (prefixWord ++ tailWord_793444) baseStart_793444 baseEnd_793444 := by
    simpa [prefixWord, tailWord_793444, baseEnd_793444] using wordTrace_append hprefix tailTrace_793444
  have hstable : (prefixWord ++ tailWord_793444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793444).length < 2 ^ (prefixWord ++ tailWord_793444).sum := by decide
  have hdescent : baseEnd_793444 < baseStart_793444 := by decide
  rcases family_descends (prefixWord ++ tailWord_793444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793455 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_793455 : Nat := 118140960795 + 793455 * 2 ^ 59
def prefixEnd_793455 : Nat := 4983230072969 + 3 ^ 40 * 793455 * 2
def baseEnd_793455 : Nat := 271615861808865558242315

theorem tailTrace_793455 : CollatzResearch.WordTrace tailWord_793455 prefixEnd_793455 271615861808865558242315 := by
  unfold tailWord_793455
  simp only [CollatzResearch.WordTrace]
  refine ⟨28939681340455521170501819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19293120893637014113667879 28939681340455521170501819)
  ·
    refine ⟨43409522010683281755752729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28939681340455521170501819 43409522010683281755752729)
    ·
      refine ⟨32557141508012461316814547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43409522010683281755752729 32557141508012461316814547)
      ·
        refine ⟨48835712262018691975221821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32557141508012461316814547 48835712262018691975221821)
        ·
          refine ⟨18313392098257009490708183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48835712262018691975221821 18313392098257009490708183)
          ·
            refine ⟨27470088147385514236062275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18313392098257009490708183 27470088147385514236062275)
            ·
              refine ⟨41205132221078271354093413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27470088147385514236062275 41205132221078271354093413)
              ·
                refine ⟨7725962291452175878892515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41205132221078271354093413 7725962291452175878892515)
                ·
                  refine ⟨11588943437178263818338773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7725962291452175878892515 11588943437178263818338773)
                  ·
                    refine ⟨271615861808865558242315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11588943437178263818338773 271615861808865558242315)
                    ·
                      rfl

theorem cell22_793455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_793455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793455 prefixEnd_793455 := by exact prefixLift 793455
  have htrace : WordTrace (prefixWord ++ tailWord_793455) baseStart_793455 baseEnd_793455 := by
    simpa [prefixWord, tailWord_793455, baseEnd_793455] using wordTrace_append hprefix tailTrace_793455
  have hstable : (prefixWord ++ tailWord_793455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793455).length < 2 ^ (prefixWord ++ tailWord_793455).sum := by decide
  have hdescent : baseEnd_793455 < baseStart_793455 := by decide
  rcases family_descends (prefixWord ++ tailWord_793455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793504 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_793504 : Nat := 118140960795 + 793504 * 2 ^ 59
def prefixEnd_793504 : Nat := 4983230072969 + 3 ^ 40 * 793504 * 2
def baseEnd_793504 : Nat := 271632635510245763767165

theorem tailTrace_793504 : CollatzResearch.WordTrace tailWord_793504 prefixEnd_793504 271632635510245763767165 := by
  unfold tailWord_793504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470734258639001269517783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19294312344852001692690377 14470734258639001269517783)
  ·
    refine ⟨21706101387958501904276675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14470734258639001269517783 21706101387958501904276675)
    ·
      refine ⟨32559152081937752856415013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21706101387958501904276675 32559152081937752856415013)
      ·
        refine ⟨6104841015363328660577815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32559152081937752856415013 6104841015363328660577815)
        ·
          refine ⟨9157261523044992990866723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104841015363328660577815 9157261523044992990866723)
          ·
            refine ⟨13735892284567489486300085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9157261523044992990866723 13735892284567489486300085)
            ·
              refine ⟨1287739901678202139340633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13735892284567489486300085 1287739901678202139340633)
              ·
                refine ⟨965804926258651604505475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287739901678202139340633 965804926258651604505475)
                ·
                  refine ⟨1448707389387977406758213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 965804926258651604505475 1448707389387977406758213)
                  ·
                    refine ⟨271632635510245763767165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1448707389387977406758213 271632635510245763767165)
                    ·
                      rfl

theorem cell22_793504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_793504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793504 prefixEnd_793504 := by exact prefixLift 793504
  have htrace : WordTrace (prefixWord ++ tailWord_793504) baseStart_793504 baseEnd_793504 := by
    simpa [prefixWord, tailWord_793504, baseEnd_793504] using wordTrace_append hprefix tailTrace_793504
  have hstable : (prefixWord ++ tailWord_793504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793504).length < 2 ^ (prefixWord ++ tailWord_793504).sum := by decide
  have hdescent : baseEnd_793504 < baseStart_793504 := by decide
  rcases family_descends (prefixWord ++ tailWord_793504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793536 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 4]
def baseStart_793536 : Nat := 118140960795 + 793536 * 2 ^ 59
def prefixEnd_793536 : Nat := 4983230072969 + 3 ^ 40 * 793536 * 2
def baseEnd_793536 : Nat := 90547863254736115655689

theorem tailTrace_793536 : CollatzResearch.WordTrace tailWord_793536 prefixEnd_793536 90547863254736115655689 := by
  unfold tailWord_793536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14471317826581036002100231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19295090435441381336133641 14471317826581036002100231)
  ·
    refine ⟨21706976739871554003150347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14471317826581036002100231 21706976739871554003150347)
    ·
      refine ⟨32560465109807331004725521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21706976739871554003150347 32560465109807331004725521)
      ·
        refine ⟨24420348832355498253544141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32560465109807331004725521 24420348832355498253544141)
        ·
          refine ⟨9157630812133311845079053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24420348832355498253544141 9157630812133311845079053)
          ·
            refine ⟨3434111554549991941904645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9157630812133311845079053 3434111554549991941904645)
            ·
              refine ⟨643895916478123489107121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3434111554549991941904645 643895916478123489107121)
              ·
                refine ⟨482921937358592616830341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643895916478123489107121 482921937358592616830341)
                ·
                  refine ⟨90547863254736115655689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482921937358592616830341 90547863254736115655689)
                  ·
                    rfl

theorem cell22_793536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_793536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793536 prefixEnd_793536 := by exact prefixLift 793536
  have htrace : WordTrace (prefixWord ++ tailWord_793536) baseStart_793536 baseEnd_793536 := by
    simpa [prefixWord, tailWord_793536, baseEnd_793536] using wordTrace_append hprefix tailTrace_793536
  have hstable : (prefixWord ++ tailWord_793536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793536).length < 2 ^ (prefixWord ++ tailWord_793536).sum := by decide
  have hdescent : baseEnd_793536 < baseStart_793536 := by decide
  rcases family_descends (prefixWord ++ tailWord_793536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793547 : List Nat := [1, 1, 1, 1, 3, 5, 3, 7]
def baseStart_793547 : Nat := 118140960795 + 793547 * 2 ^ 59
def prefixEnd_793547 : Nat := 4983230072969 + 3 ^ 40 * 793547 * 2
def baseEnd_793547 : Nat := 30183039476556442771337

theorem tailTrace_793547 : CollatzResearch.WordTrace tailWord_793547 prefixEnd_793547 30183039476556442771337 := by
  unfold tailWord_793547
  simp only [CollatzResearch.WordTrace]
  refine ⟨28943036856122220882850895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19295357904081480588567263 28943036856122220882850895)
  ·
    refine ⟨43414555284183331324276343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28943036856122220882850895 43414555284183331324276343)
    ·
      refine ⟨65121832926274996986414515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43414555284183331324276343 65121832926274996986414515)
      ·
        refine ⟨97682749389412495479621773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65121832926274996986414515 97682749389412495479621773)
        ·
          refine ⟨36631031021029685804858165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97682749389412495479621773 36631031021029685804858165)
          ·
            refine ⟨3434159158221533044205453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36631031021029685804858165 3434159158221533044205453)
            ·
              refine ⟨1287809684333074891577045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3434159158221533044205453 1287809684333074891577045)
              ·
                refine ⟨30183039476556442771337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1287809684333074891577045 30183039476556442771337)
                ·
                  rfl

theorem cell22_793547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 7].length) (baseStart_793547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793547 prefixEnd_793547 := by exact prefixLift 793547
  have htrace : WordTrace (prefixWord ++ tailWord_793547) baseStart_793547 baseEnd_793547 := by
    simpa [prefixWord, tailWord_793547, baseEnd_793547] using wordTrace_append hprefix tailTrace_793547
  have hstable : (prefixWord ++ tailWord_793547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793547).length < 2 ^ (prefixWord ++ tailWord_793547).sum := by decide
  have hdescent : baseEnd_793547 < baseStart_793547 := by decide
  rcases family_descends (prefixWord ++ tailWord_793547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793596 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_793596 : Nat := 118140960795 + 793596 * 2 ^ 59
def prefixEnd_793596 : Nat := 4983230072969 + 3 ^ 40 * 793596 * 2
def baseEnd_793596 : Nat := 271664128990388190466883

theorem tailTrace_793596 : CollatzResearch.WordTrace tailWord_793596 prefixEnd_793596 271664128990388190466883 := by
  unfold tailWord_793596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14472412016472351125692321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19296549355296468167589761 14472412016472351125692321)
  ·
    refine ⟨10854309012354263344269241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14472412016472351125692321 10854309012354263344269241)
    ·
      refine ⟨8140731759265697508201931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10854309012354263344269241 8140731759265697508201931)
      ·
        refine ⟨12211097638898546262302897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140731759265697508201931 12211097638898546262302897)
        ·
          refine ⟨9158323229173909696727173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12211097638898546262302897 9158323229173909696727173)
          ·
            refine ⟨1717185605470108068136345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9158323229173909696727173 1717185605470108068136345)
            ·
              refine ⟨1287889204102581051102259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717185605470108068136345 1287889204102581051102259)
              ·
                refine ⟨1931833806153871576653389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287889204102581051102259 1931833806153871576653389)
                ·
                  refine ⟨724437677307701841245021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1931833806153871576653389 724437677307701841245021)
                  ·
                    refine ⟨271664128990388190466883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724437677307701841245021 271664128990388190466883)
                    ·
                      rfl

theorem cell22_793596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_793596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793596 prefixEnd_793596 := by exact prefixLift 793596
  have htrace : WordTrace (prefixWord ++ tailWord_793596) baseStart_793596 baseEnd_793596 := by
    simpa [prefixWord, tailWord_793596, baseEnd_793596] using wordTrace_append hprefix tailTrace_793596
  have hstable : (prefixWord ++ tailWord_793596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793596).length < 2 ^ (prefixWord ++ tailWord_793596).sum := by decide
  have hdescent : baseEnd_793596 < baseStart_793596 := by decide
  rcases family_descends (prefixWord ++ tailWord_793596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793602 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_793602 : Nat := 118140960795 + 793602 * 2 ^ 59
def prefixEnd_793602 : Nat := 4983230072969 + 3 ^ 40 * 793602 * 2
def baseEnd_793602 : Nat := 271666182913006174816865

theorem tailTrace_793602 : CollatzResearch.WordTrace tailWord_793602 prefixEnd_793602 271666182913006174816865 := by
  unfold tailWord_793602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236260717730741319025765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19296695247281976850735373 7236260717730741319025765)
  ·
    refine ⟨1356798884574513997317331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7236260717730741319025765 1356798884574513997317331)
    ·
      refine ⟨2035198326861770995975997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356798884574513997317331 2035198326861770995975997)
      ·
        refine ⟨763199372573164123490999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2035198326861770995975997 763199372573164123490999)
        ·
          refine ⟨1144799058859746185236499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763199372573164123490999 1144799058859746185236499)
          ·
            refine ⟨1717198588289619277854749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144799058859746185236499 1717198588289619277854749)
            ·
              refine ⟨643949470608607229195531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1717198588289619277854749 643949470608607229195531)
              ·
                refine ⟨965924205912910843793297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643949470608607229195531 965924205912910843793297)
                ·
                  refine ⟨724443154434683132844973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 965924205912910843793297 724443154434683132844973)
                  ·
                    refine ⟨271666182913006174816865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724443154434683132844973 271666182913006174816865)
                    ·
                      rfl

theorem cell22_793602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_793602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793602 prefixEnd_793602 := by exact prefixLift 793602
  have htrace : WordTrace (prefixWord ++ tailWord_793602) baseStart_793602 baseEnd_793602 := by
    simpa [prefixWord, tailWord_793602, baseEnd_793602] using wordTrace_append hprefix tailTrace_793602
  have hstable : (prefixWord ++ tailWord_793602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793602).length < 2 ^ (prefixWord ++ tailWord_793602).sum := by decide
  have hdescent : baseEnd_793602 < baseStart_793602 := by decide
  rcases family_descends (prefixWord ++ tailWord_793602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793684 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_793684 : Nat := 118140960795 + 793684 * 2 ^ 59
def prefixEnd_793684 : Nat := 4983230072969 + 3 ^ 40 * 793684 * 2
def baseEnd_793684 : Nat := 271694253188785294266613

theorem tailTrace_793684 : CollatzResearch.WordTrace tailWord_793684 prefixEnd_793684 271694253188785294266613 := by
  unfold tailWord_793684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14474016828312946640294053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19298689104417262187058737 14474016828312946640294053)
  ·
    refine ⟨2713878155308677495055135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14474016828312946640294053 2713878155308677495055135)
    ·
      refine ⟨4070817232963016242582703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2713878155308677495055135 4070817232963016242582703)
      ·
        refine ⟨6106225849444524363874055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070817232963016242582703 6106225849444524363874055)
        ·
          refine ⟨9159338774166786545811083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106225849444524363874055 9159338774166786545811083)
          ·
            refine ⟨13739008161250179818716625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159338774166786545811083 13739008161250179818716625)
            ·
              refine ⟨10304256120937634864037469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13739008161250179818716625 10304256120937634864037469)
              ·
                refine ⟨3864096045351613074014051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10304256120937634864037469 3864096045351613074014051)
                ·
                  refine ⟨5796144068027419611021077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3864096045351613074014051 5796144068027419611021077)
                  ·
                    refine ⟨271694253188785294266613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5796144068027419611021077 271694253188785294266613)
                    ·
                      rfl

theorem cell22_793684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_793684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793684 prefixEnd_793684 := by exact prefixLift 793684
  have htrace : WordTrace (prefixWord ++ tailWord_793684) baseStart_793684 baseEnd_793684 := by
    simpa [prefixWord, tailWord_793684, baseEnd_793684] using wordTrace_append hprefix tailTrace_793684
  have hstable : (prefixWord ++ tailWord_793684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793684).length < 2 ^ (prefixWord ++ tailWord_793684).sum := by decide
  have hdescent : baseEnd_793684 < baseStart_793684 := by decide
  rcases family_descends (prefixWord ++ tailWord_793684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793703 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 2, 3]
def baseStart_793703 : Nat := 118140960795 + 793703 * 2 ^ 59
def prefixEnd_793703 : Nat := 4983230072969 + 3 ^ 40 * 793703 * 2
def baseEnd_793703 : Nat := 271700757277075578041555

theorem tailTrace_793703 : CollatzResearch.WordTrace tailWord_793703 prefixEnd_793703 271700757277075578041555 := by
  unfold tailWord_793703
  simp only [CollatzResearch.WordTrace]
  refine ⟨28948726643557059525529763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19299151095704706350353175 28948726643557059525529763)
  ·
    refine ⟨43423089965335589288294645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28948726643557059525529763 43423089965335589288294645)
    ·
      refine ⟨4070914684250211495777623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43423089965335589288294645 4070914684250211495777623)
      ·
        refine ⟨6106372026375317243666435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070914684250211495777623 6106372026375317243666435)
        ·
          refine ⟨9159558039562975865499653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106372026375317243666435 9159558039562975865499653)
          ·
            refine ⟨1717417132418057974781185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9159558039562975865499653 1717417132418057974781185)
            ·
              refine ⟨1288062849313543481085889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1717417132418057974781185 1288062849313543481085889)
              ·
                refine ⟨966047136985157610814417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288062849313543481085889 966047136985157610814417)
                ·
                  refine ⟨724535352738868208110813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 966047136985157610814417 724535352738868208110813)
                  ·
                    refine ⟨271700757277075578041555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724535352738868208110813 271700757277075578041555)
                    ·
                      rfl

theorem cell22_793703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_793703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793703 prefixEnd_793703 := by exact prefixLift 793703
  have htrace : WordTrace (prefixWord ++ tailWord_793703) baseStart_793703 baseEnd_793703 := by
    simpa [prefixWord, tailWord_793703, baseEnd_793703] using wordTrace_append hprefix tailTrace_793703
  have hstable : (prefixWord ++ tailWord_793703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793703).length < 2 ^ (prefixWord ++ tailWord_793703).sum := by decide
  have hdescent : baseEnd_793703 < baseStart_793703 := by decide
  rcases family_descends (prefixWord ++ tailWord_793703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793731 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 3, 3]
def baseStart_793731 : Nat := 118140960795 + 793731 * 2 ^ 59
def prefixEnd_793731 : Nat := 4983230072969 + 3 ^ 40 * 793731 * 2
def baseEnd_793731 : Nat := 271710342249292838341469

theorem tailTrace_793731 : CollatzResearch.WordTrace tailWord_793731 prefixEnd_793731 271710342249292838341469 := by
  unfold tailWord_793731
  simp only [CollatzResearch.WordTrace]
  refine ⟨28949747887455620307549047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19299831924970413538366031 28949747887455620307549047)
  ·
    refine ⟨43424621831183430461323571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28949747887455620307549047 43424621831183430461323571)
    ·
      refine ⟨65136932746775145691985357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43424621831183430461323571 65136932746775145691985357)
      ·
        refine ⟨24426349780040679634494509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65136932746775145691985357 24426349780040679634494509)
        ·
          refine ⟨9159881167515254862935441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24426349780040679634494509 9159881167515254862935441)
          ·
            refine ⟨6869910875636441147201581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9159881167515254862935441 6869910875636441147201581)
            ·
              refine ⟨2576216578363665430200593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6869910875636441147201581 2576216578363665430200593)
              ·
                refine ⟨1932162433772749072650445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2576216578363665430200593 1932162433772749072650445)
                ·
                  refine ⟨724560912664780902243917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1932162433772749072650445 724560912664780902243917)
                  ·
                    refine ⟨271710342249292838341469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 724560912664780902243917 271710342249292838341469)
                    ·
                      rfl

theorem cell22_793731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 3].length) (baseStart_793731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793731 prefixEnd_793731 := by exact prefixLift 793731
  have htrace : WordTrace (prefixWord ++ tailWord_793731) baseStart_793731 baseEnd_793731 := by
    simpa [prefixWord, tailWord_793731, baseEnd_793731] using wordTrace_append hprefix tailTrace_793731
  have hstable : (prefixWord ++ tailWord_793731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793731).length < 2 ^ (prefixWord ++ tailWord_793731).sum := by decide
  have hdescent : baseEnd_793731 < baseStart_793731 := by decide
  rcases family_descends (prefixWord ++ tailWord_793731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793778 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 5]
def baseStart_793778 : Nat := 118140960795 + 793778 * 2 ^ 59
def prefixEnd_793778 : Nat := 4983230072969 + 3 ^ 40 * 793778 * 2
def baseEnd_793778 : Nat := 90575477103266794138775

theorem tailTrace_793778 : CollatzResearch.WordTrace tailWord_793778 prefixEnd_793778 90575477103266794138775 := by
  unfold tailWord_793778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7237865529571336833627497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19300974745523564889673325 7237865529571336833627497)
  ·
    refine ⟨5428399147178502625220623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7237865529571336833627497 5428399147178502625220623)
    ·
      refine ⟨8142598720767753937830935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5428399147178502625220623 8142598720767753937830935)
      ·
        refine ⟨12213898081151630906746403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8142598720767753937830935 12213898081151630906746403)
        ·
          refine ⟨18320847121727446360119605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12213898081151630906746403 18320847121727446360119605)
          ·
            refine ⟨1717579417661948096261213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18320847121727446360119605 1717579417661948096261213)
            ·
              refine ⟨644092281623230536097955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1717579417661948096261213 644092281623230536097955)
              ·
                refine ⟨966138422434845804146933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644092281623230536097955 966138422434845804146933)
                ·
                  refine ⟨90575477103266794138775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 966138422434845804146933 90575477103266794138775)
                  ·
                    rfl

theorem cell22_793778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_793778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793778 prefixEnd_793778 := by exact prefixLift 793778
  have htrace : WordTrace (prefixWord ++ tailWord_793778) baseStart_793778 baseEnd_793778 := by
    simpa [prefixWord, tailWord_793778, baseEnd_793778] using wordTrace_append hprefix tailTrace_793778
  have hstable : (prefixWord ++ tailWord_793778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793778).length < 2 ^ (prefixWord ++ tailWord_793778).sum := by decide
  have hdescent : baseEnd_793778 < baseStart_793778 := by decide
  rcases family_descends (prefixWord ++ tailWord_793778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793791 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 1, 4]
def baseStart_793791 : Nat := 118140960795 + 793791 * 2 ^ 59
def prefixEnd_793791 : Nat := 4983230072969 + 3 ^ 40 * 793791 * 2
def baseEnd_793791 : Nat := 271730881475472681841285

theorem tailTrace_793791 : CollatzResearch.WordTrace tailWord_793791 prefixEnd_793791 271730881475472681841285 := by
  unfold tailWord_793791
  simp only [CollatzResearch.WordTrace]
  refine ⟨28951936267238250554733227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19301290844825500369822151 28951936267238250554733227)
  ·
    refine ⟨43427904400857375832099841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28951936267238250554733227 43427904400857375832099841)
    ·
      refine ⟨32570928300643031874074881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43427904400857375832099841 32570928300643031874074881)
      ·
        refine ⟨24428196225482273905556161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32570928300643031874074881 24428196225482273905556161)
        ·
          refine ⟨18321147169111705429167121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24428196225482273905556161 18321147169111705429167121)
          ·
            refine ⟨13740860376833779071875341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18321147169111705429167121 13740860376833779071875341)
            ·
              refine ⟨5152822641312667151953253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13740860376833779071875341 5152822641312667151953253)
              ·
                refine ⟨966154245246125090991235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5152822641312667151953253 966154245246125090991235)
                ·
                  refine ⟨1449231367869187636486853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966154245246125090991235 1449231367869187636486853)
                  ·
                    refine ⟨271730881475472681841285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449231367869187636486853 271730881475472681841285)
                    ·
                      rfl

theorem cell22_793791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_793791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793791 prefixEnd_793791 := by exact prefixLift 793791
  have htrace : WordTrace (prefixWord ++ tailWord_793791) baseStart_793791 baseEnd_793791 := by
    simpa [prefixWord, tailWord_793791, baseEnd_793791] using wordTrace_append hprefix tailTrace_793791
  have hstable : (prefixWord ++ tailWord_793791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793791).length < 2 ^ (prefixWord ++ tailWord_793791).sum := by decide
  have hdescent : baseEnd_793791 < baseStart_793791 := by decide
  rcases family_descends (prefixWord ++ tailWord_793791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793842 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_793842 : Nat := 118140960795 + 793842 * 2 ^ 59
def prefixEnd_793842 : Nat := 4983230072969 + 3 ^ 40 * 793842 * 2
def baseEnd_793842 : Nat := 271748339817725548816129

theorem tailTrace_793842 : CollatzResearch.WordTrace tailWord_793842 prefixEnd_793842 271748339817725548816129 := by
  unfold tailWord_793842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238449097513371566209945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19302530926702324176559853 7238449097513371566209945)
  ·
    refine ⟨5428836823135028674657459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7238449097513371566209945 5428836823135028674657459)
    ·
      refine ⟨8143255234702543011986189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5428836823135028674657459 8143255234702543011986189)
      ·
        refine ⟨3053720713013453629494821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8143255234702543011986189 3053720713013453629494821)
        ·
          refine ⟨572572633690022555530279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3053720713013453629494821 572572633690022555530279)
          ·
            refine ⟨858858950535033833295419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572572633690022555530279 858858950535033833295419)
            ·
              refine ⟨1288288425802550749943129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858858950535033833295419 1288288425802550749943129)
              ·
                refine ⟨966216319351913062457347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288288425802550749943129 966216319351913062457347)
                ·
                  refine ⟨1449324479027869593686021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966216319351913062457347 1449324479027869593686021)
                  ·
                    refine ⟨271748339817725548816129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449324479027869593686021 271748339817725548816129)
                    ·
                      rfl

theorem cell22_793842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_793842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793842 prefixEnd_793842 := by exact prefixLift 793842
  have htrace : WordTrace (prefixWord ++ tailWord_793842) baseStart_793842 baseEnd_793842 := by
    simpa [prefixWord, tailWord_793842, baseEnd_793842] using wordTrace_append hprefix tailTrace_793842
  have hstable : (prefixWord ++ tailWord_793842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793842).length < 2 ^ (prefixWord ++ tailWord_793842).sum := by decide
  have hdescent : baseEnd_793842 < baseStart_793842 := by decide
  rcases family_descends (prefixWord ++ tailWord_793842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793988 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_793988 : Nat := 118140960795 + 793988 * 2 ^ 59
def prefixEnd_793988 : Nat := 4983230072969 + 3 ^ 40 * 793988 * 2
def baseEnd_793988 : Nat := 271798318601429834665681

theorem tailTrace_793988 : CollatzResearch.WordTrace tailWord_793988 prefixEnd_793988 271798318601429834665681 := by
  unfold tailWord_793988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479560723762276599827309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19306080965016368799769745 14479560723762276599827309)
  ·
    refine ⟨5429835271410853724935241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14479560723762276599827309 5429835271410853724935241)
    ·
      refine ⟨4072376453558140293701431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5429835271410853724935241 4072376453558140293701431)
      ·
        refine ⟨6108564680337210440552147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072376453558140293701431 6108564680337210440552147)
        ·
          refine ⟨9162847020505815660828221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108564680337210440552147 9162847020505815660828221)
          ·
            refine ⟨3436067632689680872810583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9162847020505815660828221 3436067632689680872810583)
            ·
              refine ⟨5154101449034521309215875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436067632689680872810583 5154101449034521309215875)
              ·
                refine ⟨7731152173551781963823813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5154101449034521309215875 7731152173551781963823813)
                ·
                  refine ⟨1449591032540959118216965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7731152173551781963823813 1449591032540959118216965)
                  ·
                    refine ⟨271798318601429834665681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449591032540959118216965 271798318601429834665681)
                    ·
                      rfl

theorem cell22_793988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_793988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793988 prefixEnd_793988 := by exact prefixLift 793988
  have htrace : WordTrace (prefixWord ++ tailWord_793988) baseStart_793988 baseEnd_793988 := by
    simpa [prefixWord, tailWord_793988, baseEnd_793988] using wordTrace_append hprefix tailTrace_793988
  have hstable : (prefixWord ++ tailWord_793988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793988).length < 2 ^ (prefixWord ++ tailWord_793988).sum := by decide
  have hdescent : baseEnd_793988 < baseStart_793988 := by decide
  rcases family_descends (prefixWord ++ tailWord_793988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793992 : List Nat := [2, 1, 3, 3, 1, 3, 3, 2, 4]
def baseStart_793992 : Nat := 118140960795 + 793992 * 2 ^ 59
def prefixEnd_793992 : Nat := 4983230072969 + 3 ^ 40 * 793992 * 2
def baseEnd_793992 : Nat := 90599895961058385855223

theorem tailTrace_793992 : CollatzResearch.WordTrace tailWord_793992 prefixEnd_793992 90599895961058385855223 := by
  unfold tailWord_793992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479633669755030941400115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19306178226340041255200153 14479633669755030941400115)
  ·
    refine ⟨21719450504632546412100173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14479633669755030941400115 21719450504632546412100173)
    ·
      refine ⟨8144793939237204904537565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21719450504632546412100173 8144793939237204904537565)
      ·
        refine ⟨3054297727213951839201587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8144793939237204904537565 3054297727213951839201587)
        ·
          refine ⟨4581446590820927758802381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054297727213951839201587 4581446590820927758802381)
          ·
            refine ⟨1718042471557847909550893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4581446590820927758802381 1718042471557847909550893)
            ·
              refine ⟨644265926834192966081585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1718042471557847909550893 644265926834192966081585)
              ·
                refine ⟨483199445125644724561189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644265926834192966081585 483199445125644724561189)
                ·
                  refine ⟨90599895961058385855223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483199445125644724561189 90599895961058385855223)
                  ·
                    rfl

theorem cell22_793992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 2, 4].length) (baseStart_793992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_793992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_793992 prefixEnd_793992 := by exact prefixLift 793992
  have htrace : WordTrace (prefixWord ++ tailWord_793992) baseStart_793992 baseEnd_793992 := by
    simpa [prefixWord, tailWord_793992, baseEnd_793992] using wordTrace_append hprefix tailTrace_793992
  have hstable : (prefixWord ++ tailWord_793992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793992).length < 2 ^ (prefixWord ++ tailWord_793992).sum := by decide
  have hdescent : baseEnd_793992 < baseStart_793992 := by decide
  rcases family_descends (prefixWord ++ tailWord_793992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794031 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 9]
def baseStart_794031 : Nat := 118140960795 + 794031 * 2 ^ 59
def prefixEnd_794031 : Nat := 4983230072969 + 3 ^ 40 * 794031 * 2
def baseEnd_794031 : Nat := 90604346126730685280183

theorem tailTrace_794031 : CollatzResearch.WordTrace tailWord_794031 prefixEnd_794031 90604346126730685280183 := by
  unfold tailWord_794031
  simp only [CollatzResearch.WordTrace]
  refine ⟨28960689786368771543469947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19307126524245847695646631 28960689786368771543469947)
  ·
    refine ⟨43441034679553157315204921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28960689786368771543469947 43441034679553157315204921)
    ·
      refine ⟨32580776009664867986403691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43441034679553157315204921 32580776009664867986403691)
      ·
        refine ⟨48871164014497301979605537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32580776009664867986403691 48871164014497301979605537)
        ·
          refine ⟨36653373010872976484704153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48871164014497301979605537 36653373010872976484704153)
          ·
            refine ⟨27490029758154732363528115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36653373010872976484704153 27490029758154732363528115)
            ·
              refine ⟨41235044637232098545292173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27490029758154732363528115 41235044637232098545292173)
              ·
                refine ⟨15463141738962036954484565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41235044637232098545292173 15463141738962036954484565)
                ·
                  refine ⟨90604346126730685280183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15463141738962036954484565 90604346126730685280183)
                  ·
                    rfl

theorem cell22_794031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_794031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794031 prefixEnd_794031 := by exact prefixLift 794031
  have htrace : WordTrace (prefixWord ++ tailWord_794031) baseStart_794031 baseEnd_794031 := by
    simpa [prefixWord, tailWord_794031, baseEnd_794031] using wordTrace_append hprefix tailTrace_794031
  have hstable : (prefixWord ++ tailWord_794031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794031).length < 2 ^ (prefixWord ++ tailWord_794031).sum := by decide
  have hdescent : baseEnd_794031 < baseStart_794031 := by decide
  rcases family_descends (prefixWord ++ tailWord_794031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794048 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 5]
def baseStart_794048 : Nat := 118140960795 + 794048 * 2 ^ 59
def prefixEnd_794048 : Nat := 4983230072969 + 3 ^ 40 * 794048 * 2
def baseEnd_794048 : Nat := 90606285942536559388499

theorem tailTrace_794048 : CollatzResearch.WordTrace tailWord_794048 prefixEnd_794048 90606285942536559388499 := by
  unfold tailWord_794048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480654913653591723419399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19307539884871455631225865 14480654913653591723419399)
  ·
    refine ⟨21720982370480387585129099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14480654913653591723419399 21720982370480387585129099)
    ·
      refine ⟨32581473555720581377693649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21720982370480387585129099 32581473555720581377693649)
      ·
        refine ⟨24436105166790436033270237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32581473555720581377693649 24436105166790436033270237)
        ·
          refine ⟨9163539437546413512476339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24436105166790436033270237 9163539437546413512476339)
          ·
            refine ⟨13745309156319620268714509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9163539437546413512476339 13745309156319620268714509)
            ·
              refine ⟨5154490933619857600767941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13745309156319620268714509 5154490933619857600767941)
              ·
                refine ⟨966467050053723300143989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5154490933619857600767941 966467050053723300143989)
                ·
                  refine ⟨90606285942536559388499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 966467050053723300143989 90606285942536559388499)
                  ·
                    rfl

theorem cell22_794048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 5].length) (baseStart_794048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794048 prefixEnd_794048 := by exact prefixLift 794048
  have htrace : WordTrace (prefixWord ++ tailWord_794048) baseStart_794048 baseEnd_794048 := by
    simpa [prefixWord, tailWord_794048, baseEnd_794048] using wordTrace_append hprefix tailTrace_794048
  have hstable : (prefixWord ++ tailWord_794048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794048).length < 2 ^ (prefixWord ++ tailWord_794048).sum := by decide
  have hdescent : baseEnd_794048 < baseStart_794048 := by decide
  rcases family_descends (prefixWord ++ tailWord_794048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794108 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_794108 : Nat := 118140960795 + 794108 * 2 ^ 59
def prefixEnd_794108 : Nat := 4983230072969 + 3 ^ 40 * 794108 * 2
def baseEnd_794108 : Nat := 271839397053789521665313

theorem tailTrace_794108 : CollatzResearch.WordTrace tailWord_794108 prefixEnd_794108 271839397053789521665313 := by
  unfold tailWord_794108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14481749103544906847011489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19308998804726542462681985 14481749103544906847011489)
  ·
    refine ⟨10861311827658680135258617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14481749103544906847011489 10861311827658680135258617)
    ·
      refine ⟨8145983870744010101443963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10861311827658680135258617 8145983870744010101443963)
      ·
        refine ⟨12218975806116015152165945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145983870744010101443963 12218975806116015152165945)
        ·
          refine ⟨9164231854587011364124459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12218975806116015152165945 9164231854587011364124459)
          ·
            refine ⟨13746347781880517046186689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164231854587011364124459 13746347781880517046186689)
            ·
              refine ⟨10309760836410387784640017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13746347781880517046186689 10309760836410387784640017)
              ·
                refine ⟨7732320627307790838480013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10309760836410387784640017 7732320627307790838480013)
                ·
                  refine ⟨2899620235240421564430005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7732320627307790838480013 2899620235240421564430005)
                  ·
                    refine ⟨271839397053789521665313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2899620235240421564430005 271839397053789521665313)
                    ·
                      rfl

theorem cell22_794108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_794108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794108 prefixEnd_794108 := by exact prefixLift 794108
  have htrace : WordTrace (prefixWord ++ tailWord_794108) baseStart_794108 baseEnd_794108 := by
    simpa [prefixWord, tailWord_794108, baseEnd_794108] using wordTrace_append hprefix tailTrace_794108
  have hstable : (prefixWord ++ tailWord_794108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794108).length < 2 ^ (prefixWord ++ tailWord_794108).sum := by decide
  have hdescent : baseEnd_794108 < baseStart_794108 := by decide
  rcases family_descends (prefixWord ++ tailWord_794108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794140 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_794140 : Nat := 118140960795 + 794140 * 2 ^ 59
def prefixEnd_794140 : Nat := 4983230072969 + 3 ^ 40 * 794140 * 2
def baseEnd_794140 : Nat := 271850351307752104865215

theorem tailTrace_794140 : CollatzResearch.WordTrace tailWord_794140 prefixEnd_794140 271850351307752104865215 := by
  unfold tailWord_794140
  simp only [CollatzResearch.WordTrace]
  refine ⟨14482332671486941579593937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19309776895315922106125249 14482332671486941579593937)
  ·
    refine ⟨10861749503615206184695453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14482332671486941579593937 10861749503615206184695453)
    ·
      refine ⟨4073156063855702319260795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10861749503615206184695453 4073156063855702319260795)
      ·
        refine ⟨6109734095783553478891193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073156063855702319260795 6109734095783553478891193)
        ·
          refine ⟨4582300571837665109168395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6109734095783553478891193 4582300571837665109168395)
          ·
            refine ⟨6873450857756497663752593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582300571837665109168395 6873450857756497663752593)
            ·
              refine ⟨5155088143317373247814445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6873450857756497663752593 5155088143317373247814445)
              ·
                refine ⟨1933158053744014967930417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5155088143317373247814445 1933158053744014967930417)
                ·
                  refine ⟨1449868540308011225947813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1933158053744014967930417 1449868540308011225947813)
                  ·
                    refine ⟨271850351307752104865215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1449868540308011225947813 271850351307752104865215)
                    ·
                      rfl

theorem cell22_794140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_794140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794140 prefixEnd_794140 := by exact prefixLift 794140
  have htrace : WordTrace (prefixWord ++ tailWord_794140) baseStart_794140 baseEnd_794140 := by
    simpa [prefixWord, tailWord_794140, baseEnd_794140] using wordTrace_append hprefix tailTrace_794140
  have hstable : (prefixWord ++ tailWord_794140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794140).length < 2 ^ (prefixWord ++ tailWord_794140).sum := by decide
  have hdescent : baseEnd_794140 < baseStart_794140 := by decide
  rcases family_descends (prefixWord ++ tailWord_794140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794144 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 4]
def baseStart_794144 : Nat := 118140960795 + 794144 * 2 ^ 59
def prefixEnd_794144 : Nat := 4983230072969 + 3 ^ 40 * 794144 * 2
def baseEnd_794144 : Nat := 90617240196499142588401

theorem tailTrace_794144 : CollatzResearch.WordTrace tailWord_794144 prefixEnd_794144 90617240196499142588401 := by
  unfold tailWord_794144
  simp only [CollatzResearch.WordTrace]
  refine ⟨14482405617479695921166743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19309874156639594561555657 14482405617479695921166743)
  ·
    refine ⟨21723608426219543881750115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14482405617479695921166743 21723608426219543881750115)
    ·
      refine ⟨32585412639329315822625173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21723608426219543881750115 32585412639329315822625173)
      ·
        refine ⟨1527441217468561679185555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32585412639329315822625173 1527441217468561679185555)
        ·
          refine ⟨2291161826202842518778333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527441217468561679185555 2291161826202842518778333)
          ·
            refine ⟨859185684826065944541875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2291161826202842518778333 859185684826065944541875)
            ·
              refine ⟨1288778527239098916812813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859185684826065944541875 1288778527239098916812813)
              ·
                refine ⟨483291947714662093804805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1288778527239098916812813 483291947714662093804805)
                ·
                  refine ⟨90617240196499142588401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483291947714662093804805 90617240196499142588401)
                  ·
                    rfl

theorem cell22_794144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 4].length) (baseStart_794144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794144 prefixEnd_794144 := by exact prefixLift 794144
  have htrace : WordTrace (prefixWord ++ tailWord_794144) baseStart_794144 baseEnd_794144 := by
    simpa [prefixWord, tailWord_794144, baseEnd_794144] using wordTrace_append hprefix tailTrace_794144
  have hstable : (prefixWord ++ tailWord_794144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794144).length < 2 ^ (prefixWord ++ tailWord_794144).sum := by decide
  have hdescent : baseEnd_794144 < baseStart_794144 := by decide
  rcases family_descends (prefixWord ++ tailWord_794144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794221 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_794221 : Nat := 118140960795 + 794221 * 2 ^ 59
def prefixEnd_794221 : Nat := 4983230072969 + 3 ^ 40 * 794221 * 2
def baseEnd_794221 : Nat := 271878079263094893589967

theorem tailTrace_794221 : CollatzResearch.WordTrace tailWord_794221 prefixEnd_794221 271878079263094893589967 := by
  unfold tailWord_794221
  simp only [CollatzResearch.WordTrace]
  refine ⟨28967619655680433992886517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19311746437120289328591011 28967619655680433992886517)
  ·
    refine ⟨2715714342720040686833111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28967619655680433992886517 2715714342720040686833111)
    ·
      refine ⟨4073571514080061030249667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715714342720040686833111 4073571514080061030249667)
      ·
        refine ⟨6110357271120091545374501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073571514080061030249667 6110357271120091545374501)
        ·
          refine ⟨1145691988335017164757719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6110357271120091545374501 1145691988335017164757719)
          ·
            refine ⟨1718537982502525747136579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145691988335017164757719 1718537982502525747136579)
            ·
              refine ⟨2577806973753788620704869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718537982502525747136579 2577806973753788620704869)
              ·
                refine ⟨483338807578835366382163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2577806973753788620704869 483338807578835366382163)
                ·
                  refine ⟨725008211368253049573245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483338807578835366382163 725008211368253049573245)
                  ·
                    refine ⟨271878079263094893589967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725008211368253049573245 271878079263094893589967)
                    ·
                      rfl

theorem cell22_794221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_794221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794221 prefixEnd_794221 := by exact prefixLift 794221
  have htrace : WordTrace (prefixWord ++ tailWord_794221) baseStart_794221 baseEnd_794221 := by
    simpa [prefixWord, tailWord_794221, baseEnd_794221] using wordTrace_append hprefix tailTrace_794221
  have hstable : (prefixWord ++ tailWord_794221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794221).length < 2 ^ (prefixWord ++ tailWord_794221).sum := by decide
  have hdescent : baseEnd_794221 < baseStart_794221 := by decide
  rcases family_descends (prefixWord ++ tailWord_794221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794245 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 6]
def baseStart_794245 : Nat := 118140960795 + 794245 * 2 ^ 59
def prefixEnd_794245 : Nat := 4983230072969 + 3 ^ 40 * 794245 * 2
def baseEnd_794245 : Nat := 90628764984522276996631

theorem tailTrace_794245 : CollatzResearch.WordTrace tailWord_794245 prefixEnd_794245 90628764984522276996631 := by
  unfold tailWord_794245
  simp only [CollatzResearch.WordTrace]
  refine ⟨28968495007593486091760189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19312330005062324061173459 28968495007593486091760189)
  ·
    refine ⟨10863185627847557284410071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28968495007593486091760189 10863185627847557284410071)
    ·
      refine ⟨16294778441771335926615107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10863185627847557284410071 16294778441771335926615107)
      ·
        refine ⟨24442167662657003889922661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16294778441771335926615107 24442167662657003889922661)
        ·
          refine ⟨4582906436748188229360499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24442167662657003889922661 4582906436748188229360499)
          ·
            refine ⟨6874359655122282344040749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582906436748188229360499 6874359655122282344040749)
            ·
              refine ⟨2577884870670855879015281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6874359655122282344040749 2577884870670855879015281)
              ·
                refine ⟨1933413653003141909261461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577884870670855879015281 1933413653003141909261461)
                ·
                  refine ⟨90628764984522276996631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1933413653003141909261461 90628764984522276996631)
                  ·
                    rfl

theorem cell22_794245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_794245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794245 prefixEnd_794245 := by exact prefixLift 794245
  have htrace : WordTrace (prefixWord ++ tailWord_794245) baseStart_794245 baseEnd_794245 := by
    simpa [prefixWord, tailWord_794245, baseEnd_794245] using wordTrace_append hprefix tailTrace_794245
  have hstable : (prefixWord ++ tailWord_794245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794245).length < 2 ^ (prefixWord ++ tailWord_794245).sum := by decide
  have hdescent : baseEnd_794245 < baseStart_794245 := by decide
  rcases family_descends (prefixWord ++ tailWord_794245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794264 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 1, 4]
def baseStart_794264 : Nat := 118140960795 + 794264 * 2 ^ 59
def prefixEnd_794264 : Nat := 4983230072969 + 3 ^ 40 * 794264 * 2
def baseEnd_794264 : Nat := 271892799041857114764835

theorem tailTrace_794264 : CollatzResearch.WordTrace tailWord_794264 prefixEnd_794264 271892799041857114764835 := by
  unfold tailWord_794264
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484593997262326168350923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19312791996349768224467897 14484593997262326168350923)
  ·
    refine ⟨21726890995893489252526385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14484593997262326168350923 21726890995893489252526385)
    ·
      refine ⟨16295168246920116939394789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21726890995893489252526385 16295168246920116939394789)
      ·
        refine ⟨3055344046297521926136523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16295168246920116939394789 3055344046297521926136523)
        ·
          refine ⟨4583016069446282889204785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055344046297521926136523 4583016069446282889204785)
          ·
            refine ⟨3437262052084712166903589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4583016069446282889204785 3437262052084712166903589)
            ·
              refine ⟨644486634765883531294423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3437262052084712166903589 644486634765883531294423)
              ·
                refine ⟨966729952148825296941635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644486634765883531294423 966729952148825296941635)
                ·
                  refine ⟨1450094928223237945412453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 966729952148825296941635 1450094928223237945412453)
                  ·
                    refine ⟨271892799041857114764835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1450094928223237945412453 271892799041857114764835)
                    ·
                      rfl

theorem cell22_794264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_794264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794264 prefixEnd_794264 := by exact prefixLift 794264
  have htrace : WordTrace (prefixWord ++ tailWord_794264) baseStart_794264 baseEnd_794264 := by
    simpa [prefixWord, tailWord_794264, baseEnd_794264] using wordTrace_append hprefix tailTrace_794264
  have hstable : (prefixWord ++ tailWord_794264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794264).length < 2 ^ (prefixWord ++ tailWord_794264).sum := by decide
  have hdescent : baseEnd_794264 < baseStart_794264 := by decide
  rcases family_descends (prefixWord ++ tailWord_794264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794275 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 4, 4]
def baseStart_794275 : Nat := 118140960795 + 794275 * 2 ^ 59
def prefixEnd_794275 : Nat := 4983230072969 + 3 ^ 40 * 794275 * 2
def baseEnd_794275 : Nat := 271896564566656752739801

theorem tailTrace_794275 : CollatzResearch.WordTrace tailWord_794275 prefixEnd_794275 271896564566656752739801 := by
  unfold tailWord_794275
  simp only [CollatzResearch.WordTrace]
  refine ⟨28969589197484801215352279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19313059464989867476901519 28969589197484801215352279)
  ·
    refine ⟨43454383796227201823028419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28969589197484801215352279 43454383796227201823028419)
    ·
      refine ⟨65181575694340802734542629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43454383796227201823028419 65181575694340802734542629)
      ·
        refine ⟨12221545442688900512726743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65181575694340802734542629 12221545442688900512726743)
        ·
          refine ⟨18332318164033350769090115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12221545442688900512726743 18332318164033350769090115)
          ·
            refine ⟨27498477246050026153635173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18332318164033350769090115 27498477246050026153635173)
            ·
              refine ⟨5155964483634379903806595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27498477246050026153635173 5155964483634379903806595)
              ·
                refine ⟨7733946725451569855709893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155964483634379903806595 7733946725451569855709893)
                ·
                  refine ⟨1450115011022169347945605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7733946725451569855709893 1450115011022169347945605)
                  ·
                    refine ⟨271896564566656752739801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1450115011022169347945605 271896564566656752739801)
                    ·
                      rfl

theorem cell22_794275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_794275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794275 prefixEnd_794275 := by exact prefixLift 794275
  have htrace : WordTrace (prefixWord ++ tailWord_794275) baseStart_794275 baseEnd_794275 := by
    simpa [prefixWord, tailWord_794275, baseEnd_794275] using wordTrace_append hprefix tailTrace_794275
  have hstable : (prefixWord ++ tailWord_794275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794275).length < 2 ^ (prefixWord ++ tailWord_794275).sum := by decide
  have hdescent : baseEnd_794275 < baseStart_794275 := by decide
  rcases family_descends (prefixWord ++ tailWord_794275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794335 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 7]
def baseStart_794335 : Nat := 118140960795 + 794335 * 2 ^ 59
def prefixEnd_794335 : Nat := 4983230072969 + 3 ^ 40 * 794335 * 2
def baseEnd_794335 : Nat := 90639034597612198746539

theorem tailTrace_794335 : CollatzResearch.WordTrace tailWord_794335 prefixEnd_794335 90639034597612198746539 := by
  unfold tailWord_794335
  simp only [CollatzResearch.WordTrace]
  refine ⟨28971777577267431462536459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19314518384844954308357639 28971777577267431462536459)
  ·
    refine ⟨43457666365901147193804689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28971777577267431462536459 43457666365901147193804689)
    ·
      refine ⟨32593249774425860395353517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43457666365901147193804689 32593249774425860395353517)
      ·
        refine ⟨12222468665409697648257569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32593249774425860395353517 12222468665409697648257569)
        ·
          refine ⟨9166851499057273236193177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12222468665409697648257569 9166851499057273236193177)
          ·
            refine ⟨6875138624292954927144883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9166851499057273236193177 6875138624292954927144883)
            ·
              refine ⟨10312707936439432390717325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875138624292954927144883 10312707936439432390717325)
              ·
                refine ⟨3867265476164787146518997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10312707936439432390717325 3867265476164787146518997)
                ·
                  refine ⟨90639034597612198746539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3867265476164787146518997 90639034597612198746539)
                  ·
                    rfl

theorem cell22_794335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_794335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794335 prefixEnd_794335 := by exact prefixLift 794335
  have htrace : WordTrace (prefixWord ++ tailWord_794335) baseStart_794335 baseEnd_794335 := by
    simpa [prefixWord, tailWord_794335, baseEnd_794335] using wordTrace_append hprefix tailTrace_794335
  have hstable : (prefixWord ++ tailWord_794335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794335).length < 2 ^ (prefixWord ++ tailWord_794335).sum := by decide
  have hdescent : baseEnd_794335 < baseStart_794335 := by decide
  rcases family_descends (prefixWord ++ tailWord_794335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794386 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_794386 : Nat := 118140960795 + 794386 * 2 ^ 59
def prefixEnd_794386 : Nat := 4983230072969 + 3 ^ 40 * 794386 * 2
def baseEnd_794386 : Nat := 90644854045029821071487

theorem tailTrace_794386 : CollatzResearch.WordTrace tailWord_794386 prefixEnd_794386 90644854045029821071487 := by
  unfold tailWord_794386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7243409425020666793160753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19315758466721778115095341 7243409425020666793160753)
  ·
    refine ⟨5432557068765500094870565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7243409425020666793160753 5432557068765500094870565)
    ·
      refine ⟨1018604450393531267788231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5432557068765500094870565 1018604450393531267788231)
      ·
        refine ⟨1527906675590296901682347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018604450393531267788231 1527906675590296901682347)
        ·
          refine ⟨2291860013385445352523521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527906675590296901682347 2291860013385445352523521)
          ·
            refine ⟨1718895010039084014392641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291860013385445352523521 1718895010039084014392641)
            ·
              refine ⟨1289171257529313010794481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718895010039084014392641 1289171257529313010794481)
              ·
                refine ⟨966878443146984758095861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289171257529313010794481 966878443146984758095861)
                ·
                  refine ⟨90644854045029821071487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 966878443146984758095861 90644854045029821071487)
                  ·
                    rfl

theorem cell22_794386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_794386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794386 prefixEnd_794386 := by exact prefixLift 794386
  have htrace : WordTrace (prefixWord ++ tailWord_794386) baseStart_794386 baseEnd_794386 := by
    simpa [prefixWord, tailWord_794386, baseEnd_794386] using wordTrace_append hprefix tailTrace_794386
  have hstable : (prefixWord ++ tailWord_794386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794386).length < 2 ^ (prefixWord ++ tailWord_794386).sum := by decide
  have hdescent : baseEnd_794386 < baseStart_794386 := by decide
  rcases family_descends (prefixWord ++ tailWord_794386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794412 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_794412 : Nat := 118140960795 + 794412 * 2 ^ 59
def prefixEnd_794412 : Nat := 4983230072969 + 3 ^ 40 * 794412 * 2
def baseEnd_794412 : Nat := 271943462466434062064381

theorem tailTrace_794412 : CollatzResearch.WordTrace tailWord_794412 prefixEnd_794412 271943462466434062064381 := by
  unfold tailWord_794412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487292998994236806544745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19316390665325649075392993 14487292998994236806544745)
  ·
    refine ⟨10865469749245677604908559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14487292998994236806544745 10865469749245677604908559)
    ·
      refine ⟨16298204623868516407362839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865469749245677604908559 16298204623868516407362839)
      ·
        refine ⟨24447306935802774611044259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16298204623868516407362839 24447306935802774611044259)
        ·
          refine ⟨36670960403704161916566389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24447306935802774611044259 36670960403704161916566389)
          ·
            refine ⟨3437902537847265179678099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36670960403704161916566389 3437902537847265179678099)
            ·
              refine ⟨5156853806770897769517149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3437902537847265179678099 5156853806770897769517149)
              ·
                refine ⟨1933820177539086663568931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5156853806770897769517149 1933820177539086663568931)
                ·
                  refine ⟨2900730266308629995353397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933820177539086663568931 2900730266308629995353397)
                  ·
                    refine ⟨271943462466434062064381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2900730266308629995353397 271943462466434062064381)
                    ·
                      rfl

theorem cell22_794412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_794412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794412 prefixEnd_794412 := by exact prefixLift 794412
  have htrace : WordTrace (prefixWord ++ tailWord_794412) baseStart_794412 baseEnd_794412 := by
    simpa [prefixWord, tailWord_794412, baseEnd_794412] using wordTrace_append hprefix tailTrace_794412
  have hstable : (prefixWord ++ tailWord_794412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794412).length < 2 ^ (prefixWord ++ tailWord_794412).sum := by decide
  have hdescent : baseEnd_794412 < baseStart_794412 := by decide
  rcases family_descends (prefixWord ++ tailWord_794412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794429 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_794429 : Nat := 118140960795 + 794429 * 2 ^ 59
def prefixEnd_794429 : Nat := 4983230072969 + 3 ^ 40 * 794429 * 2
def baseEnd_794429 : Nat := 271949281913851684389329

theorem tailTrace_794429 : CollatzResearch.WordTrace tailWord_794429 prefixEnd_794429 271949281913851684389329 := by
  unfold tailWord_794429
  simp only [CollatzResearch.WordTrace]
  refine ⟨28975206038926885516458341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19316804025951257010972227 28975206038926885516458341)
  ·
    refine ⟨5432851132298791034335939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28975206038926885516458341 5432851132298791034335939)
    ·
      refine ⟨8149276698448186551503909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5432851132298791034335939 8149276698448186551503909)
      ·
        refine ⟨1527989380959034978406983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8149276698448186551503909 1527989380959034978406983)
        ·
          refine ⟨2291984071438552467610475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527989380959034978406983 2291984071438552467610475)
          ·
            refine ⟨3437976107157828701415713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291984071438552467610475 3437976107157828701415713)
            ·
              refine ⟨2578482080368371526061785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3437976107157828701415713 2578482080368371526061785)
              ·
                refine ⟨1933861560276278644546339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2578482080368371526061785 1933861560276278644546339)
                ·
                  refine ⟨2900792340414417966819509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1933861560276278644546339 2900792340414417966819509)
                  ·
                    refine ⟨271949281913851684389329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2900792340414417966819509 271949281913851684389329)
                    ·
                      rfl

theorem cell22_794429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_794429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794429 prefixEnd_794429 := by exact prefixLift 794429
  have htrace : WordTrace (prefixWord ++ tailWord_794429) baseStart_794429 baseEnd_794429 := by
    simpa [prefixWord, tailWord_794429, baseEnd_794429] using wordTrace_append hprefix tailTrace_794429
  have hstable : (prefixWord ++ tailWord_794429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794429).length < 2 ^ (prefixWord ++ tailWord_794429).sum := by decide
  have hdescent : baseEnd_794429 < baseStart_794429 := by decide
  rcases family_descends (prefixWord ++ tailWord_794429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794431 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 4]
def baseStart_794431 : Nat := 118140960795 + 794431 * 2 ^ 59
def prefixEnd_794431 : Nat := 4983230072969 + 3 ^ 40 * 794431 * 2
def baseEnd_794431 : Nat := 90649988851574781946441

theorem tailTrace_794431 : CollatzResearch.WordTrace tailWord_794431 prefixEnd_794431 90649988851574781946441 := by
  unfold tailWord_794431
  simp only [CollatzResearch.WordTrace]
  refine ⟨28975278984919639858031147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19316852656613093238687431 28975278984919639858031147)
  ·
    refine ⟨43462918477379459787046721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28975278984919639858031147 43462918477379459787046721)
    ·
      refine ⟨32597188858034594840285041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43462918477379459787046721 32597188858034594840285041)
      ·
        refine ⟨24447891643525946130213781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32597188858034594840285041 24447891643525946130213781)
        ·
          refine ⟨1145994920790278724853771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24447891643525946130213781 1145994920790278724853771)
          ·
            refine ⟨1718992381185418087280657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145994920790278724853771 1718992381185418087280657)
            ·
              refine ⟨1289244285889063565460493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718992381185418087280657 1289244285889063565460493)
              ·
                refine ⟨483466607208398837047685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289244285889063565460493 483466607208398837047685)
                ·
                  refine ⟨90649988851574781946441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483466607208398837047685 90649988851574781946441)
                  ·
                    rfl

theorem cell22_794431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 4].length) (baseStart_794431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794431 prefixEnd_794431 := by exact prefixLift 794431
  have htrace : WordTrace (prefixWord ++ tailWord_794431) baseStart_794431 baseEnd_794431 := by
    simpa [prefixWord, tailWord_794431, baseEnd_794431] using wordTrace_append hprefix tailTrace_794431
  have hstable : (prefixWord ++ tailWord_794431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794431).length < 2 ^ (prefixWord ++ tailWord_794431).sum := by decide
  have hdescent : baseEnd_794431 < baseStart_794431 := by decide
  rcases family_descends (prefixWord ++ tailWord_794431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794577 : List Nat := [1, 2, 2, 1, 2, 1, 2, 11]
def baseStart_794577 : Nat := 118140960795 + 794577 * 2 ^ 59
def prefixEnd_794577 : Nat := 4983230072969 + 3 ^ 40 * 794577 * 2
def baseEnd_794577 : Nat := 30222216148714292409875

theorem tailTrace_794577 : CollatzResearch.WordTrace tailWord_794577 prefixEnd_794577 30222216148714292409875 := by
  unfold tailWord_794577
  simp only [CollatzResearch.WordTrace]
  refine ⟨28980604042390706792845985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19320402694927137861897323 28980604042390706792845985)
  ·
    refine ⟨21735453031793030094634489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28980604042390706792845985 21735453031793030094634489)
    ·
      refine ⟨16301589773844772570975867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21735453031793030094634489 16301589773844772570975867)
      ·
        refine ⟨24452384660767158856463801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16301589773844772570975867 24452384660767158856463801)
        ·
          refine ⟨18339288495575369142347851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24452384660767158856463801 18339288495575369142347851)
          ·
            refine ⟨27508932743363053713521777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18339288495575369142347851 27508932743363053713521777)
            ·
              refine ⟨20631699557522290285141333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27508932743363053713521777 20631699557522290285141333)
              ·
                refine ⟨30222216148714292409875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 20631699557522290285141333 30222216148714292409875)
                ·
                  rfl

theorem cell22_794577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 11].length) (baseStart_794577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794577 prefixEnd_794577 := by exact prefixLift 794577
  have htrace : WordTrace (prefixWord ++ tailWord_794577) baseStart_794577 baseEnd_794577 := by
    simpa [prefixWord, tailWord_794577, baseEnd_794577] using wordTrace_append hprefix tailTrace_794577
  have hstable : (prefixWord ++ tailWord_794577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794577).length < 2 ^ (prefixWord ++ tailWord_794577).sum := by decide
  have hdescent : baseEnd_794577 < baseStart_794577 := by decide
  rcases family_descends (prefixWord ++ tailWord_794577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794581 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_794581 : Nat := 118140960795 + 794581 * 2 ^ 59
def prefixEnd_794581 : Nat := 4983230072969 + 3 ^ 40 * 794581 * 2
def baseEnd_794581 : Nat := 272001314620173954588863

theorem tailTrace_794581 : CollatzResearch.WordTrace tailWord_794581 prefixEnd_794581 272001314620173954588863 := by
  unfold tailWord_794581
  simp only [CollatzResearch.WordTrace]
  refine ⟨28980749934376215475991597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19320499956250810317327731 28980749934376215475991597)
  ·
    refine ⟨10867781225391080803496849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28980749934376215475991597 10867781225391080803496849)
    ·
      refine ⟨8150835919043310602622637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10867781225391080803496849 8150835919043310602622637)
      ·
        refine ⟨3056563469641241475983489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8150835919043310602622637 3056563469641241475983489)
        ·
          refine ⟨2292422602230931106987617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056563469641241475983489 2292422602230931106987617)
          ·
            refine ⟨1719316951673198330240713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292422602230931106987617 1719316951673198330240713)
            ·
              refine ⟨1289487713754898747680535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719316951673198330240713 1289487713754898747680535)
              ·
                refine ⟨1934231570632348121520803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289487713754898747680535 1934231570632348121520803)
                ·
                  refine ⟨2901347355948522182281205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1934231570632348121520803 2901347355948522182281205)
                  ·
                    refine ⟨272001314620173954588863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2901347355948522182281205 272001314620173954588863)
                    ·
                      rfl

theorem cell22_794581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_794581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794581 prefixEnd_794581 := by exact prefixLift 794581
  have htrace : WordTrace (prefixWord ++ tailWord_794581) baseStart_794581 baseEnd_794581 := by
    simpa [prefixWord, tailWord_794581, baseEnd_794581] using wordTrace_append hprefix tailTrace_794581
  have hstable : (prefixWord ++ tailWord_794581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794581).length < 2 ^ (prefixWord ++ tailWord_794581).sum := by decide
  have hdescent : baseEnd_794581 < baseStart_794581 := by decide
  rcases family_descends (prefixWord ++ tailWord_794581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794701 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 8]
def baseStart_794701 : Nat := 118140960795 + 794701 * 2 ^ 59
def prefixEnd_794701 : Nat := 4983230072969 + 3 ^ 40 * 794701 * 2
def baseEnd_794701 : Nat := 90680797690844547196165

theorem tailTrace_794701 : CollatzResearch.WordTrace tailWord_794701 prefixEnd_794701 90680797690844547196165 := by
  unfold tailWord_794701
  simp only [CollatzResearch.WordTrace]
  refine ⟨28985126693941475970359957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19323417795960983980239971 28985126693941475970359957)
  ·
    refine ⟨1358677813778506686110623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28985126693941475970359957 1358677813778506686110623)
    ·
      refine ⟨2038016720667760029165935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358677813778506686110623 2038016720667760029165935)
      ·
        refine ⟨3057025081001640043748903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038016720667760029165935 3057025081001640043748903)
        ·
          refine ⟨4585537621502460065623355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057025081001640043748903 4585537621502460065623355)
          ·
            refine ⟨6878306432253690098435033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585537621502460065623355 6878306432253690098435033)
            ·
              refine ⟨5158729824190267573826275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6878306432253690098435033 5158729824190267573826275)
              ·
                refine ⟨7738094736285401360739413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158729824190267573826275 7738094736285401360739413)
                ·
                  refine ⟨90680797690844547196165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7738094736285401360739413 90680797690844547196165)
                  ·
                    rfl

theorem cell22_794701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_794701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794701 prefixEnd_794701 := by exact prefixLift 794701
  have htrace : WordTrace (prefixWord ++ tailWord_794701) baseStart_794701 baseEnd_794701 := by
    simpa [prefixWord, tailWord_794701, baseEnd_794701] using wordTrace_append hprefix tailTrace_794701
  have hstable : (prefixWord ++ tailWord_794701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794701).length < 2 ^ (prefixWord ++ tailWord_794701).sum := by decide
  have hdescent : baseEnd_794701 < baseStart_794701 := by decide
  rcases family_descends (prefixWord ++ tailWord_794701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794716 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_794716 : Nat := 118140960795 + 794716 * 2 ^ 59
def prefixEnd_794716 : Nat := 4983230072969 + 3 ^ 40 * 794716 * 2
def baseEnd_794716 : Nat := 272047527879078602463449

theorem tailTrace_794716 : CollatzResearch.WordTrace tailWord_794716 prefixEnd_794716 272047527879078602463449 := by
  unfold tailWord_794716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492836894443566766078001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19323782525924755688104001 14492836894443566766078001)
  ·
    refine ⟨10869627670832675074558501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14492836894443566766078001 10869627670832675074558501)
    ·
      refine ⟨2038055188281126576479719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10869627670832675074558501 2038055188281126576479719)
      ·
        refine ⟨3057082782421689864719579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038055188281126576479719 3057082782421689864719579)
        ·
          refine ⟨4585624173632534797079369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057082782421689864719579 4585624173632534797079369)
          ·
            refine ⟨3439218130224401097809527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4585624173632534797079369 3439218130224401097809527)
            ·
              refine ⟨5158827195336601646714291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439218130224401097809527 5158827195336601646714291)
              ·
                refine ⟨7738240793004902470071437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158827195336601646714291 7738240793004902470071437)
                ·
                  refine ⟨2901840297376838426276789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7738240793004902470071437 2901840297376838426276789)
                  ·
                    refine ⟨272047527879078602463449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2901840297376838426276789 272047527879078602463449)
                    ·
                      rfl

theorem cell22_794716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_794716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794716 prefixEnd_794716 := by exact prefixLift 794716
  have htrace : WordTrace (prefixWord ++ tailWord_794716) baseStart_794716 baseEnd_794716 := by
    simpa [prefixWord, tailWord_794716, baseEnd_794716] using wordTrace_append hprefix tailTrace_794716
  have hstable : (prefixWord ++ tailWord_794716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794716).length < 2 ^ (prefixWord ++ tailWord_794716).sum := by decide
  have hdescent : baseEnd_794716 < baseStart_794716 := by decide
  rcases family_descends (prefixWord ++ tailWord_794716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794735 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 4]
def baseStart_794735 : Nat := 118140960795 + 794735 * 2 ^ 59
def prefixEnd_794735 : Nat := 4983230072969 + 3 ^ 40 * 794735 * 2
def baseEnd_794735 : Nat := 90684677322456295412797

theorem tailTrace_794735 : CollatzResearch.WordTrace tailWord_794735 prefixEnd_794735 90684677322456295412797 := by
  unfold tailWord_794735
  simp only [CollatzResearch.WordTrace]
  refine ⟨28986366775818299777097659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19324244517212199851398439 28986366775818299777097659)
  ·
    refine ⟨43479550163727449665646489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28986366775818299777097659 43479550163727449665646489)
    ·
      refine ⟨32609662622795587249234867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43479550163727449665646489 32609662622795587249234867)
      ·
        refine ⟨48914493934193380873852301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32609662622795587249234867 48914493934193380873852301)
        ·
          refine ⟨18342935225322517827694613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48914493934193380873852301 18342935225322517827694613)
          ·
            refine ⟨859825088686993023173185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18342935225322517827694613 859825088686993023173185)
            ·
              refine ⟨644868816515244767379889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859825088686993023173185 644868816515244767379889)
              ·
                refine ⟨483651612386433575534917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644868816515244767379889 483651612386433575534917)
                ·
                  refine ⟨90684677322456295412797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483651612386433575534917 90684677322456295412797)
                  ·
                    rfl

theorem cell22_794735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 4].length) (baseStart_794735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794735 prefixEnd_794735 := by exact prefixLift 794735
  have htrace : WordTrace (prefixWord ++ tailWord_794735) baseStart_794735 baseEnd_794735 := by
    simpa [prefixWord, tailWord_794735, baseEnd_794735] using wordTrace_append hprefix tailTrace_794735
  have hstable : (prefixWord ++ tailWord_794735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794735).length < 2 ^ (prefixWord ++ tailWord_794735).sum := by decide
  have hdescent : baseEnd_794735 < baseStart_794735 := by decide
  rcases family_descends (prefixWord ++ tailWord_794735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794744 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 7]
def baseStart_794744 : Nat := 118140960795 + 794744 * 2 ^ 59
def prefixEnd_794744 : Nat := 4983230072969 + 3 ^ 40 * 794744 * 2
def baseEnd_794744 : Nat := 272057112851295862763363

theorem tailTrace_794744 : CollatzResearch.WordTrace tailWord_794744 prefixEnd_794744 272057112851295862763363 := by
  unfold tailWord_794744
  simp only [CollatzResearch.WordTrace]
  refine ⟨14493347516392847157087643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19324463355190462876116857 14493347516392847157087643)
  ·
    refine ⟨21740021274589270735631465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14493347516392847157087643 21740021274589270735631465)
    ·
      refine ⟨16305015955941953051723599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21740021274589270735631465 16305015955941953051723599)
      ·
        refine ⟨24457523933912929577585399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16305015955941953051723599 24457523933912929577585399)
        ·
          refine ⟨36686285900869394366378099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24457523933912929577585399 36686285900869394366378099)
          ·
            refine ⟨55029428851304091549567149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36686285900869394366378099 55029428851304091549567149)
            ·
              refine ⟨20636035819239034331087681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55029428851304091549567149 20636035819239034331087681)
              ·
                refine ⟨15477026864429275748315761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20636035819239034331087681 15477026864429275748315761)
                ·
                  refine ⟨11607770148321956811236821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15477026864429275748315761 11607770148321956811236821)
                  ·
                    refine ⟨272057112851295862763363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11607770148321956811236821 272057112851295862763363)
                    ·
                      rfl

theorem cell22_794744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_794744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794744 prefixEnd_794744 := by exact prefixLift 794744
  have htrace : WordTrace (prefixWord ++ tailWord_794744) baseStart_794744 baseEnd_794744 := by
    simpa [prefixWord, tailWord_794744, baseEnd_794744] using wordTrace_append hprefix tailTrace_794744
  have hstable : (prefixWord ++ tailWord_794744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794744).length < 2 ^ (prefixWord ++ tailWord_794744).sum := by decide
  have hdescent : baseEnd_794744 < baseStart_794744 := by decide
  rcases family_descends (prefixWord ++ tailWord_794744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794808 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 5]
def baseStart_794808 : Nat := 118140960795 + 794808 * 2 ^ 59
def prefixEnd_794808 : Nat := 4983230072969 + 3 ^ 40 * 794808 * 2
def baseEnd_794808 : Nat := 90693007119740343054389

theorem tailTrace_794808 : CollatzResearch.WordTrace tailWord_794808 prefixEnd_794808 90693007119740343054389 := by
  unfold tailWord_794808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494514652276916622252539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19326019536369222163003385 14494514652276916622252539)
  ·
    refine ⟨21741771978415374933378809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14494514652276916622252539 21741771978415374933378809)
    ·
      refine ⟨16306328983811531200034107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21741771978415374933378809 16306328983811531200034107)
      ·
        refine ⟨24459493475717296800051161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16306328983811531200034107 24459493475717296800051161)
        ·
          refine ⟨18344620106787972600038371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24459493475717296800051161 18344620106787972600038371)
          ·
            refine ⟨27516930160181958900057557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18344620106787972600038371 27516930160181958900057557)
            ·
              refine ⟨644928050629264661720099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27516930160181958900057557 644928050629264661720099)
              ·
                refine ⟨967392075943896992580149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644928050629264661720099 967392075943896992580149)
                ·
                  refine ⟨90693007119740343054389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967392075943896992580149 90693007119740343054389)
                  ·
                    rfl

theorem cell22_794808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 5].length) (baseStart_794808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794808 prefixEnd_794808 := by exact prefixLift 794808
  have htrace : WordTrace (prefixWord ++ tailWord_794808) baseStart_794808 baseEnd_794808 := by
    simpa [prefixWord, tailWord_794808, baseEnd_794808] using wordTrace_append hprefix tailTrace_794808
  have hstable : (prefixWord ++ tailWord_794808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794808).length < 2 ^ (prefixWord ++ tailWord_794808).sum := by decide
  have hdescent : baseEnd_794808 < baseStart_794808 := by decide
  rcases family_descends (prefixWord ++ tailWord_794808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794821 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_794821 : Nat := 118140960795 + 794821 * 2 ^ 59
def prefixEnd_794821 : Nat := 4983230072969 + 3 ^ 40 * 794821 * 2
def baseEnd_794821 : Nat := 272083471524893328588127

theorem tailTrace_794821 : CollatzResearch.WordTrace tailWord_794821 prefixEnd_794821 272083471524893328588127 := by
  unfold tailWord_794821
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989503453506736464728317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19326335635671157643152211 28989503453506736464728317)
  ·
    refine ⟨10871063795065026174273119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28989503453506736464728317 10871063795065026174273119)
    ·
      refine ⟨16306595692597539261409679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10871063795065026174273119 16306595692597539261409679)
      ·
        refine ⟨24459893538896308892114519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16306595692597539261409679 24459893538896308892114519)
        ·
          refine ⟨36689840308344463338171779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24459893538896308892114519 36689840308344463338171779)
          ·
            refine ⟨55034760462516695007257669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36689840308344463338171779 55034760462516695007257669)
            ·
              refine ⟨10319017586721880313860813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55034760462516695007257669 10319017586721880313860813)
              ·
                refine ⟨3869631595020705117697805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10319017586721880313860813 3869631595020705117697805)
                ·
                  refine ⟨1451111848132764419136677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3869631595020705117697805 1451111848132764419136677)
                  ·
                    refine ⟨272083471524893328588127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1451111848132764419136677 272083471524893328588127)
                    ·
                      rfl

theorem cell22_794821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_794821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794821 prefixEnd_794821 := by exact prefixLift 794821
  have htrace : WordTrace (prefixWord ++ tailWord_794821) baseStart_794821 baseEnd_794821 := by
    simpa [prefixWord, tailWord_794821, baseEnd_794821] using wordTrace_append hprefix tailTrace_794821
  have hstable : (prefixWord ++ tailWord_794821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794821).length < 2 ^ (prefixWord ++ tailWord_794821).sum := by decide
  have hdescent : baseEnd_794821 < baseStart_794821 := by decide
  rcases family_descends (prefixWord ++ tailWord_794821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794853 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 6]
def baseStart_794853 : Nat := 118140960795 + 794853 * 2 ^ 59
def prefixEnd_794853 : Nat := 4983230072969 + 3 ^ 40 * 794853 * 2
def baseEnd_794853 : Nat := 90698141926285303929343

theorem tailTrace_794853 : CollatzResearch.WordTrace tailWord_794853 prefixEnd_794853 90698141926285303929343 := by
  unfold tailWord_794853
  simp only [CollatzResearch.WordTrace]
  refine ⟨28990670589390805929893213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327113726260537286595475 28990670589390805929893213)
  ·
    refine ⟨10871501471021552223709955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28990670589390805929893213 10871501471021552223709955)
    ·
      refine ⟨16307252206532328335564933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10871501471021552223709955 16307252206532328335564933)
      ·
        refine ⟨3057609788724811562918425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16307252206532328335564933 3057609788724811562918425)
        ·
          refine ⟨2293207341543608672188819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3057609788724811562918425 2293207341543608672188819)
          ·
            refine ⟨3439811012315413008283229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293207341543608672188819 3439811012315413008283229)
            ·
              refine ⟨1289929129618279878106211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3439811012315413008283229 1289929129618279878106211)
              ·
                refine ⟨1934893694427419817159317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289929129618279878106211 1934893694427419817159317)
                ·
                  refine ⟨90698141926285303929343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1934893694427419817159317 90698141926285303929343)
                  ·
                    rfl

theorem cell22_794853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_794853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794853 prefixEnd_794853 := by exact prefixLift 794853
  have htrace : WordTrace (prefixWord ++ tailWord_794853) baseStart_794853 baseEnd_794853 := by
    simpa [prefixWord, tailWord_794853, baseEnd_794853] using wordTrace_append hprefix tailTrace_794853
  have hstable : (prefixWord ++ tailWord_794853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794853).length < 2 ^ (prefixWord ++ tailWord_794853).sum := by decide
  have hdescent : baseEnd_794853 < baseStart_794853 := by decide
  rcases family_descends (prefixWord ++ tailWord_794853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794881 : List Nat := [1, 2, 4, 1, 1, 2, 1, 10]
def baseStart_794881 : Nat := 118140960795 + 794881 * 2 ^ 59
def prefixEnd_794881 : Nat := 4983230072969 + 3 ^ 40 * 794881 * 2
def baseEnd_794881 : Nat := 30233778972341463565327

theorem tailTrace_794881 : CollatzResearch.WordTrace tailWord_794881 prefixEnd_794881 30233778972341463565327 := by
  unfold tailWord_794881
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991691833289366711912497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327794555526244474608331 28991691833289366711912497)
  ·
    refine ⟨21743768874967025033934373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28991691833289366711912497 21743768874967025033934373)
    ·
      refine ⟨4076956664056317193862695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21743768874967025033934373 4076956664056317193862695)
      ·
        refine ⟨6115434996084475790794043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076956664056317193862695 6115434996084475790794043)
        ·
          refine ⟨9173152494126713686191065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6115434996084475790794043 9173152494126713686191065)
          ·
            refine ⟨6879864370595035264643299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9173152494126713686191065 6879864370595035264643299)
            ·
              refine ⟨10319796555892552896964949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879864370595035264643299 10319796555892552896964949)
              ·
                refine ⟨30233778972341463565327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10319796555892552896964949 30233778972341463565327)
                ·
                  rfl

theorem cell22_794881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 10].length) (baseStart_794881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794881 prefixEnd_794881 := by exact prefixLift 794881
  have htrace : WordTrace (prefixWord ++ tailWord_794881) baseStart_794881 baseEnd_794881 := by
    simpa [prefixWord, tailWord_794881, baseEnd_794881] using wordTrace_append hprefix tailTrace_794881
  have hstable : (prefixWord ++ tailWord_794881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794881).length < 2 ^ (prefixWord ++ tailWord_794881).sum := by decide
  have hdescent : baseEnd_794881 < baseStart_794881 := by decide
  rcases family_descends (prefixWord ++ tailWord_794881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794883 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 2, 4]
def baseStart_794883 : Nat := 118140960795 + 794883 * 2 ^ 59
def prefixEnd_794883 : Nat := 4983230072969 + 3 ^ 40 * 794883 * 2
def baseEnd_794883 : Nat := 272104695391945833537937

theorem tailTrace_794883 : CollatzResearch.WordTrace tailWord_794883 prefixEnd_794883 272104695391945833537937 := by
  unfold tailWord_794883
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991764779282121053485303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327843186188080702323535 28991764779282121053485303)
  ·
    refine ⟨43487647168923181580227955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28991764779282121053485303 43487647168923181580227955)
    ·
      refine ⟨65231470753384772370341933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43487647168923181580227955 65231470753384772370341933)
      ·
        refine ⟨24461801532519289638878225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65231470753384772370341933 24461801532519289638878225)
        ·
          refine ⟨18346351149389467229158669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24461801532519289638878225 18346351149389467229158669)
          ·
            refine ⟨6879881681021050210934501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18346351149389467229158669 6879881681021050210934501)
            ·
              refine ⟨1289977815191446914550219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6879881681021050210934501 1289977815191446914550219)
              ·
                refine ⟨1934966722787170371825329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289977815191446914550219 1934966722787170371825329)
                ·
                  refine ⟨1451225042090377778868997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1934966722787170371825329 1451225042090377778868997)
                  ·
                    refine ⟨272104695391945833537937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1451225042090377778868997 272104695391945833537937)
                    ·
                      rfl

theorem cell22_794883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 4].length) (baseStart_794883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794883 prefixEnd_794883 := by exact prefixLift 794883
  have htrace : WordTrace (prefixWord ++ tailWord_794883) baseStart_794883 baseEnd_794883 := by
    simpa [prefixWord, tailWord_794883, baseEnd_794883] using wordTrace_append hprefix tailTrace_794883
  have hstable : (prefixWord ++ tailWord_794883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794883).length < 2 ^ (prefixWord ++ tailWord_794883).sum := by decide
  have hdescent : baseEnd_794883 < baseStart_794883 := by decide
  rcases family_descends (prefixWord ++ tailWord_794883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794919 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 1, 5]
def baseStart_794919 : Nat := 118140960795 + 794919 * 2 ^ 59
def prefixEnd_794919 : Nat := 4983230072969 + 3 ^ 40 * 794919 * 2
def baseEnd_794919 : Nat := 272117018927653739637827

theorem tailTrace_794919 : CollatzResearch.WordTrace tailWord_794919 prefixEnd_794919 272117018927653739637827 := by
  unfold tailWord_794919
  simp only [CollatzResearch.WordTrace]
  refine ⟨28993077807151699201795811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19328718538101132801197207 28993077807151699201795811)
  ·
    refine ⟨43489616710727548802693717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28993077807151699201795811 43489616710727548802693717)
    ·
      refine ⟨509643945828838462531567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 43489616710727548802693717 509643945828838462531567)
      ·
        refine ⟨764465918743257693797351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509643945828838462531567 764465918743257693797351)
        ·
          refine ⟨1146698878114886540696027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764465918743257693797351 1146698878114886540696027)
          ·
            refine ⟨1720048317172329811044041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146698878114886540696027 1720048317172329811044041)
            ·
              refine ⟨1290036237879247358283031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720048317172329811044041 1290036237879247358283031)
              ·
                refine ⟨1935054356818871037424547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290036237879247358283031 1935054356818871037424547)
                ·
                  refine ⟨2902581535228306556136821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1935054356818871037424547 2902581535228306556136821)
                  ·
                    refine ⟨272117018927653739637827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2902581535228306556136821 272117018927653739637827)
                    ·
                      rfl

theorem cell22_794919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_794919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794919 prefixEnd_794919 := by exact prefixLift 794919
  have htrace : WordTrace (prefixWord ++ tailWord_794919) baseStart_794919 baseEnd_794919 := by
    simpa [prefixWord, tailWord_794919, baseEnd_794919] using wordTrace_append hprefix tailTrace_794919
  have hstable : (prefixWord ++ tailWord_794919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794919).length < 2 ^ (prefixWord ++ tailWord_794919).sum := by decide
  have hdescent : baseEnd_794919 < baseStart_794919 := by decide
  rcases family_descends (prefixWord ++ tailWord_794919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794960 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 5]
def baseStart_794960 : Nat := 118140960795 + 794960 * 2 ^ 59
def prefixEnd_794960 : Nat := 4983230072969 + 3 ^ 40 * 794960 * 2
def baseEnd_794960 : Nat := 90710351355181099787567

theorem tailTrace_794960 : CollatzResearch.WordTrace tailWord_794960 prefixEnd_794960 90710351355181099787567 := by
  unfold tailWord_794960
  simp only [CollatzResearch.WordTrace]
  refine ⟨14497286600001581602019167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19329715466668775469358889 14497286600001581602019167)
  ·
    refine ⟨21745929900002372403028751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14497286600001581602019167 21745929900002372403028751)
    ·
      refine ⟨32618894850003558604543127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21745929900002372403028751 32618894850003558604543127)
      ·
        refine ⟨48928342275005337906814691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32618894850003558604543127 48928342275005337906814691)
        ·
          refine ⟨73392513412508006860222037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48928342275005337906814691 73392513412508006860222037)
          ·
            refine ⟨860068516552828205393227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 73392513412508006860222037 860068516552828205393227)
            ·
              refine ⟨1290102774829242308089841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860068516552828205393227 1290102774829242308089841)
              ·
                refine ⟨967577081121931731067381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290102774829242308089841 967577081121931731067381)
                ·
                  refine ⟨90710351355181099787567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967577081121931731067381 90710351355181099787567)
                  ·
                    rfl

theorem cell22_794960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 5].length) (baseStart_794960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794960 prefixEnd_794960 := by exact prefixLift 794960
  have htrace : WordTrace (prefixWord ++ tailWord_794960) baseStart_794960 baseEnd_794960 := by
    simpa [prefixWord, tailWord_794960, baseEnd_794960] using wordTrace_append hprefix tailTrace_794960
  have hstable : (prefixWord ++ tailWord_794960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794960).length < 2 ^ (prefixWord ++ tailWord_794960).sum := by decide
  have hdescent : baseEnd_794960 < baseStart_794960 := by decide
  rcases family_descends (prefixWord ++ tailWord_794960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794998 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_794998 : Nat := 118140960795 + 794998 * 2 ^ 59
def prefixEnd_794998 : Nat := 4983230072969 + 3 ^ 40 * 794998 * 2
def baseEnd_794998 : Nat := 272144062242123866912585

theorem tailTrace_794998 : CollatzResearch.WordTrace tailWord_794998 prefixEnd_794998 272144062242123866912585 := by
  unfold tailWord_794998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812247448366593480870103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19330639449243663795947765 1812247448366593480870103)
  ·
    refine ⟨2718371172549890221305155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1812247448366593480870103 2718371172549890221305155)
    ·
      refine ⟨4077556758824835331957733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718371172549890221305155 4077556758824835331957733)
      ·
        refine ⟨764541892279656624742075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4077556758824835331957733 764541892279656624742075)
        ·
          refine ⟨1146812838419484937113113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764541892279656624742075 1146812838419484937113113)
          ·
            refine ⟨860109628814613702834835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146812838419484937113113 860109628814613702834835)
            ·
              refine ⟨1290164443221920554252253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860109628814613702834835 1290164443221920554252253)
              ·
                refine ⟨483811666208220207844595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1290164443221920554252253 483811666208220207844595)
                ·
                  refine ⟨725717499312330311766893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483811666208220207844595 725717499312330311766893)
                  ·
                    refine ⟨272144062242123866912585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725717499312330311766893 272144062242123866912585)
                    ·
                      rfl

theorem cell22_794998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_794998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_794998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_794998 prefixEnd_794998 := by exact prefixLift 794998
  have htrace : WordTrace (prefixWord ++ tailWord_794998) baseStart_794998 baseEnd_794998 := by
    simpa [prefixWord, tailWord_794998, baseEnd_794998] using wordTrace_append hprefix tailTrace_794998
  have hstable : (prefixWord ++ tailWord_794998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794998).length < 2 ^ (prefixWord ++ tailWord_794998).sum := by decide
  have hdescent : baseEnd_794998 < baseStart_794998 := by decide
  rcases family_descends (prefixWord ++ tailWord_794998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795020 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_795020 : Nat := 118140960795 + 795020 * 2 ^ 59
def prefixEnd_795020 : Nat := 4983230072969 + 3 ^ 40 * 795020 * 2
def baseEnd_795020 : Nat := 272151593291723142862517

theorem tailTrace_795020 : CollatzResearch.WordTrace tailWord_795020 prefixEnd_795020 272151593291723142862517 := by
  unfold tailWord_795020
  simp only [CollatzResearch.WordTrace]
  refine ⟨14498380789892896725611257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19331174386523862300815009 14498380789892896725611257)
  ·
    refine ⟨10873785592419672544208443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14498380789892896725611257 10873785592419672544208443)
    ·
      refine ⟨16310678388629508816312665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10873785592419672544208443 16310678388629508816312665)
      ·
        refine ⟨12233008791472131612234499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16310678388629508816312665 12233008791472131612234499)
        ·
          refine ⟨18349513187208197418351749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12233008791472131612234499 18349513187208197418351749)
          ·
            refine ⟨3440533722601537015940953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18349513187208197418351749 3440533722601537015940953)
            ·
              refine ⟨2580400291951152761955715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3440533722601537015940953 2580400291951152761955715)
              ·
                refine ⟨3870600437926729142933573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580400291951152761955715 3870600437926729142933573)
                ·
                  refine ⟨725737582111261714300045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3870600437926729142933573 725737582111261714300045)
                  ·
                    refine ⟨272151593291723142862517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725737582111261714300045 272151593291723142862517)
                    ·
                      rfl

theorem cell22_795020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_795020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795020 prefixEnd_795020 := by exact prefixLift 795020
  have htrace : WordTrace (prefixWord ++ tailWord_795020) baseStart_795020 baseEnd_795020 := by
    simpa [prefixWord, tailWord_795020, baseEnd_795020] using wordTrace_append hprefix tailTrace_795020
  have hstable : (prefixWord ++ tailWord_795020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795020).length < 2 ^ (prefixWord ++ tailWord_795020).sum := by decide
  have hdescent : baseEnd_795020 < baseStart_795020 := by decide
  rcases family_descends (prefixWord ++ tailWord_795020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795022 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_795022 : Nat := 118140960795 + 795022 * 2 ^ 59
def prefixEnd_795022 : Nat := 4983230072969 + 3 ^ 40 * 795022 * 2
def baseEnd_795022 : Nat := 90717425977531934770837

theorem tailTrace_795022 : CollatzResearch.WordTrace tailWord_795022 prefixEnd_795022 90717425977531934770837 := by
  unfold tailWord_795022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624604315722318474099415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19331223017185698528530213 3624604315722318474099415)
  ·
    refine ⟨5436906473583477711149123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3624604315722318474099415 5436906473583477711149123)
    ·
      refine ⟨8155359710375216566723685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5436906473583477711149123 8155359710375216566723685)
      ·
        refine ⟨1529129945695353106260691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8155359710375216566723685 1529129945695353106260691)
        ·
          refine ⟨2293694918543029659391037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529129945695353106260691 2293694918543029659391037)
          ·
            refine ⟨860135594453636122271639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2293694918543029659391037 860135594453636122271639)
            ·
              refine ⟨1290203391680454183407459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860135594453636122271639 1290203391680454183407459)
              ·
                refine ⟨1935305087520681275111189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290203391680454183407459 1935305087520681275111189)
                ·
                  refine ⟨90717425977531934770837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1935305087520681275111189 90717425977531934770837)
                  ·
                    rfl

theorem cell22_795022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_795022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795022 prefixEnd_795022 := by exact prefixLift 795022
  have htrace : WordTrace (prefixWord ++ tailWord_795022) baseStart_795022 baseEnd_795022 := by
    simpa [prefixWord, tailWord_795022, baseEnd_795022] using wordTrace_append hprefix tailTrace_795022
  have hstable : (prefixWord ++ tailWord_795022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795022).length < 2 ^ (prefixWord ++ tailWord_795022).sum := by decide
  have hdescent : baseEnd_795022 < baseStart_795022 := by decide
  rcases family_descends (prefixWord ++ tailWord_795022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795033 : List Nat := [1, 2, 1, 2, 1, 4, 4, 7]
def baseStart_795033 : Nat := 118140960795 + 795033 * 2 ^ 59
def prefixEnd_795033 : Nat := 4983230072969 + 3 ^ 40 * 795033 * 2
def baseEnd_795033 : Nat := 30239560384155049143053

theorem tailTrace_795033 : CollatzResearch.WordTrace tailWord_795033 prefixEnd_795033 30239560384155049143053 := by
  unfold tailWord_795033
  simp only [CollatzResearch.WordTrace]
  refine ⟨28997235728738696671445753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19331490485825797780963835 28997235728738696671445753)
  ·
    refine ⟨21747926796554022503584315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28997235728738696671445753 21747926796554022503584315)
    ·
      refine ⟨32621890194831033755376473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21747926796554022503584315 32621890194831033755376473)
      ·
        refine ⟨24466417646123275316532355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32621890194831033755376473 24466417646123275316532355)
        ·
          refine ⟨36699626469184912974798533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24466417646123275316532355 36699626469184912974798533)
          ·
            refine ⟨6881179962972171182774725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36699626469184912974798533 6881179962972171182774725)
            ·
              refine ⟨1290221243057282096770261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6881179962972171182774725 1290221243057282096770261)
              ·
                refine ⟨30239560384155049143053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1290221243057282096770261 30239560384155049143053)
                ·
                  rfl

theorem cell22_795033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 7].length) (baseStart_795033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795033 prefixEnd_795033 := by exact prefixLift 795033
  have htrace : WordTrace (prefixWord ++ tailWord_795033) baseStart_795033 baseEnd_795033 := by
    simpa [prefixWord, tailWord_795033, baseEnd_795033] using wordTrace_append hprefix tailTrace_795033
  have hstable : (prefixWord ++ tailWord_795033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795033).length < 2 ^ (prefixWord ++ tailWord_795033).sum := by decide
  have hdescent : baseEnd_795033 < baseStart_795033 := by decide
  rcases family_descends (prefixWord ++ tailWord_795033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795041 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 1, 4]
def baseStart_795041 : Nat := 118140960795 + 795041 * 2 ^ 59
def prefixEnd_795041 : Nat := 4983230072969 + 3 ^ 40 * 795041 * 2
def baseEnd_795041 : Nat := 272158782020886088087453

theorem tailTrace_795041 : CollatzResearch.WordTrace tailWord_795041 prefixEnd_795041 272158782020886088087453 := by
  unfold tailWord_795041
  simp only [CollatzResearch.WordTrace]
  refine ⟨28997527512709714037736977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19331685008473142691824651 28997527512709714037736977)
  ·
    refine ⟨21748145634532285528302733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28997527512709714037736977 21748145634532285528302733)
    ·
      refine ⟨8155554612949607073113525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21748145634532285528302733 8155554612949607073113525)
      ·
        refine ⟨764583244964025663104393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8155554612949607073113525 764583244964025663104393)
        ·
          refine ⟨573437433723019247328295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764583244964025663104393 573437433723019247328295)
          ·
            refine ⟨860156150584528870992443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573437433723019247328295 860156150584528870992443)
            ·
              refine ⟨1290234225876793306488665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860156150584528870992443 1290234225876793306488665)
              ·
                refine ⟨967675669407594979866499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290234225876793306488665 967675669407594979866499)
                ·
                  refine ⟨1451513504111392469799749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 967675669407594979866499 1451513504111392469799749)
                  ·
                    refine ⟨272158782020886088087453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1451513504111392469799749 272158782020886088087453)
                    ·
                      rfl

theorem cell22_795041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_795041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795041 prefixEnd_795041 := by exact prefixLift 795041
  have htrace : WordTrace (prefixWord ++ tailWord_795041) baseStart_795041 baseEnd_795041 := by
    simpa [prefixWord, tailWord_795041, baseEnd_795041] using wordTrace_append hprefix tailTrace_795041
  have hstable : (prefixWord ++ tailWord_795041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795041).length < 2 ^ (prefixWord ++ tailWord_795041).sum := by decide
  have hdescent : baseEnd_795041 < baseStart_795041 := by decide
  rcases family_descends (prefixWord ++ tailWord_795041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795123 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 8]
def baseStart_795123 : Nat := 118140960795 + 795123 * 2 ^ 59
def prefixEnd_795123 : Nat := 4983230072969 + 3 ^ 40 * 795123 * 2
def baseEnd_795123 : Nat := 90728950765555069179067

theorem tailTrace_795123 : CollatzResearch.WordTrace tailWord_795123 prefixEnd_795123 90728950765555069179067 := by
  unfold tailWord_795123
  simp only [CollatzResearch.WordTrace]
  refine ⟨29000518298412642042222023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19333678865608428028148015 29000518298412642042222023)
  ·
    refine ⟨43500777447618963063333035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29000518298412642042222023 43500777447618963063333035)
    ·
      refine ⟨65251166171428444594999553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43500777447618963063333035 65251166171428444594999553)
      ·
        refine ⟨48938374628571333446249665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65251166171428444594999553 48938374628571333446249665)
        ·
          refine ⟨36703780971428500084687249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48938374628571333446249665 36703780971428500084687249)
          ·
            refine ⟨27527835728571375063515437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36703780971428500084687249 27527835728571375063515437)
            ·
              refine ⟨10322938398214265648818289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27527835728571375063515437 10322938398214265648818289)
              ·
                refine ⟨7742203798660699236613717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10322938398214265648818289 7742203798660699236613717)
                ·
                  refine ⟨90728950765555069179067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7742203798660699236613717 90728950765555069179067)
                  ·
                    rfl

theorem cell22_795123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_795123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795123 prefixEnd_795123 := by exact prefixLift 795123
  have htrace : WordTrace (prefixWord ++ tailWord_795123) baseStart_795123 baseEnd_795123 := by
    simpa [prefixWord, tailWord_795123, baseEnd_795123] using wordTrace_append hprefix tailTrace_795123
  have hstable : (prefixWord ++ tailWord_795123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795123).length < 2 ^ (prefixWord ++ tailWord_795123).sum := by decide
  have hdescent : baseEnd_795123 < baseStart_795123 := by decide
  rcases family_descends (prefixWord ++ tailWord_795123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795305 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_795305 : Nat := 118140960795 + 795305 * 2 ^ 59
def prefixEnd_795305 : Nat := 4983230072969 + 3 ^ 40 * 795305 * 2
def baseEnd_795305 : Nat := 272249154616077399486643

theorem tailTrace_795305 : CollatzResearch.WordTrace tailWord_795305 prefixEnd_795305 272249154616077399486643 := by
  unfold tailWord_795305
  simp only [CollatzResearch.WordTrace]
  refine ⟨29007156383753287125347369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19338104255835524750231579 29007156383753287125347369)
  ·
    refine ⟨21755367287814965344010527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29007156383753287125347369 21755367287814965344010527)
    ·
      refine ⟨32633050931722448016015791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21755367287814965344010527 32633050931722448016015791)
      ·
        refine ⟨48949576397583672024023687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32633050931722448016015791 48949576397583672024023687)
        ·
          refine ⟨73424364596375508036035531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48949576397583672024023687 73424364596375508036035531)
          ·
            refine ⟨110136546894563262054053297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73424364596375508036035531 110136546894563262054053297)
            ·
              refine ⟨82602410170922446540539973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110136546894563262054053297 82602410170922446540539973)
              ·
                refine ⟨15487951907047958726351245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82602410170922446540539973 15487951907047958726351245)
                ·
                  refine ⟨5807981965142984522381717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15487951907047958726351245 5807981965142984522381717)
                  ·
                    refine ⟨272249154616077399486643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5807981965142984522381717 272249154616077399486643)
                    ·
                      rfl

theorem cell22_795305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_795305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795305 prefixEnd_795305 := by exact prefixLift 795305
  have htrace : WordTrace (prefixWord ++ tailWord_795305) baseStart_795305 baseEnd_795305 := by
    simpa [prefixWord, tailWord_795305, baseEnd_795305] using wordTrace_append hprefix tailTrace_795305
  have hstable : (prefixWord ++ tailWord_795305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795305).length < 2 ^ (prefixWord ++ tailWord_795305).sum := by decide
  have hdescent : baseEnd_795305 < baseStart_795305 := by decide
  rcases family_descends (prefixWord ++ tailWord_795305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795309 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 6]
def baseStart_795309 : Nat := 118140960795 + 795309 * 2 ^ 59
def prefixEnd_795309 : Nat := 4983230072969 + 3 ^ 40 * 795309 * 2
def baseEnd_795309 : Nat := 90750174632607574128877

theorem tailTrace_795309 : CollatzResearch.WordTrace tailWord_795309 prefixEnd_795309 90750174632607574128877 := by
  unfold tailWord_795309
  simp only [CollatzResearch.WordTrace]
  refine ⟨29007302275738795808492981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19338201517159197205661987 29007302275738795808492981)
  ·
    refine ⟨2719434588350512107046217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29007302275738795808492981 2719434588350512107046217)
    ·
      refine ⟨2039575941262884080284663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2719434588350512107046217 2039575941262884080284663)
      ·
        refine ⟨3059363911894326120426995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039575941262884080284663 3059363911894326120426995)
        ·
          refine ⟨4589045867841489180640493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059363911894326120426995 4589045867841489180640493)
          ·
            refine ⟨1720892200440558442740185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4589045867841489180640493 1720892200440558442740185)
            ·
              refine ⟨1290669150330418832055139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720892200440558442740185 1290669150330418832055139)
              ·
                refine ⟨1936003725495628248082709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290669150330418832055139 1936003725495628248082709)
                ·
                  refine ⟨90750174632607574128877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1936003725495628248082709 90750174632607574128877)
                  ·
                    rfl

theorem cell22_795309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_795309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795309 prefixEnd_795309 := by exact prefixLift 795309
  have htrace : WordTrace (prefixWord ++ tailWord_795309) baseStart_795309 baseEnd_795309 := by
    simpa [prefixWord, tailWord_795309, baseEnd_795309] using wordTrace_append hprefix tailTrace_795309
  have hstable : (prefixWord ++ tailWord_795309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795309).length < 2 ^ (prefixWord ++ tailWord_795309).sum := by decide
  have hdescent : baseEnd_795309 < baseStart_795309 := by decide
  rcases family_descends (prefixWord ++ tailWord_795309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795356 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_795356 : Nat := 118140960795 + 795356 * 2 ^ 59
def prefixEnd_795356 : Nat := 4983230072969 + 3 ^ 40 * 795356 * 2
def baseEnd_795356 : Nat := 272266612958330266461487

theorem tailTrace_795356 : CollatzResearch.WordTrace tailWord_795356 prefixEnd_795356 272266612958330266461487 := by
  unfold tailWord_795356
  simp only [CollatzResearch.WordTrace]
  refine ⟨14504508253284261417726961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19339344337712348556969281 14504508253284261417726961)
  ·
    refine ⟨10878381189963196063295221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14504508253284261417726961 10878381189963196063295221)
    ·
      refine ⟨1019848236559049630933927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10878381189963196063295221 1019848236559049630933927)
      ·
        refine ⟨1529772354838574446400891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019848236559049630933927 1529772354838574446400891)
        ·
          refine ⟨2294658532257861669601337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529772354838574446400891 2294658532257861669601337)
          ·
            refine ⟨1720993899193396252201003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2294658532257861669601337 1720993899193396252201003)
            ·
              refine ⟨2581490848790094378301505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720993899193396252201003 2581490848790094378301505)
              ·
                refine ⟨1936118136592570783726129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2581490848790094378301505 1936118136592570783726129)
                ·
                  refine ⟨1452088602444428087794597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1936118136592570783726129 1452088602444428087794597)
                  ·
                    refine ⟨272266612958330266461487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452088602444428087794597 272266612958330266461487)
                    ·
                      rfl

theorem cell22_795356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_795356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795356 prefixEnd_795356 := by exact prefixLift 795356
  have htrace : WordTrace (prefixWord ++ tailWord_795356) baseStart_795356 baseEnd_795356 := by
    simpa [prefixWord, tailWord_795356, baseEnd_795356] using wordTrace_append hprefix tailTrace_795356
  have hstable : (prefixWord ++ tailWord_795356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795356).length < 2 ^ (prefixWord ++ tailWord_795356).sum := by decide
  have hdescent : baseEnd_795356 < baseStart_795356 := by decide
  rcases family_descends (prefixWord ++ tailWord_795356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795369 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 3, 3]
def baseStart_795369 : Nat := 118140960795 + 795369 * 2 ^ 59
def prefixEnd_795369 : Nat := 4983230072969 + 3 ^ 40 * 795369 * 2
def baseEnd_795369 : Nat := 272271063124002565886447

theorem tailTrace_795369 : CollatzResearch.WordTrace tailWord_795369 prefixEnd_795369 272271063124002565886447 := by
  unfold tailWord_795369
  simp only [CollatzResearch.WordTrace]
  refine ⟨29009490655521426055677161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19339660437014284037118107 29009490655521426055677161)
  ·
    refine ⟨21757117991641069541757871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29009490655521426055677161 21757117991641069541757871)
    ·
      refine ⟨32635676987461604312636807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21757117991641069541757871 32635676987461604312636807)
      ·
        refine ⟨48953515481192406468955211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32635676987461604312636807 48953515481192406468955211)
        ·
          refine ⟨73430273221788609703432817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48953515481192406468955211 73430273221788609703432817)
          ·
            refine ⟨55072704916341457277574613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73430273221788609703432817 55072704916341457277574613)
            ·
              refine ⟨1290766521476752904943155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55072704916341457277574613 1290766521476752904943155)
              ·
                refine ⟨1936149782215129357414733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290766521476752904943155 1936149782215129357414733)
                ·
                  refine ⟨726056168330673509030525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1936149782215129357414733 726056168330673509030525)
                  ·
                    refine ⟨272271063124002565886447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726056168330673509030525 272271063124002565886447)
                    ·
                      rfl

theorem cell22_795369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 3].length) (baseStart_795369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795369 prefixEnd_795369 := by exact prefixLift 795369
  have htrace : WordTrace (prefixWord ++ tailWord_795369) baseStart_795369 baseEnd_795369 := by
    simpa [prefixWord, tailWord_795369, baseEnd_795369] using wordTrace_append hprefix tailTrace_795369
  have hstable : (prefixWord ++ tailWord_795369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795369).length < 2 ^ (prefixWord ++ tailWord_795369).sum := by decide
  have hdescent : baseEnd_795369 < baseStart_795369 := by decide
  rcases family_descends (prefixWord ++ tailWord_795369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795420 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_795420 : Nat := 118140960795 + 795420 * 2 ^ 59
def prefixEnd_795420 : Nat := 4983230072969 + 3 ^ 40 * 795420 * 2
def baseEnd_795420 : Nat := 272288521466255432861291

theorem tailTrace_795420 : CollatzResearch.WordTrace tailWord_795420 prefixEnd_795420 272288521466255432861291 := by
  unfold tailWord_795420
  simp only [CollatzResearch.WordTrace]
  refine ⟨14505675389168330882891857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19340900518891107843855809 14505675389168330882891857)
  ·
    refine ⟨10879256541876248162168893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14505675389168330882891857 10879256541876248162168893)
    ·
      refine ⟨4079721203203593060813335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10879256541876248162168893 4079721203203593060813335)
      ·
        refine ⟨6119581804805389591220003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079721203203593060813335 6119581804805389591220003)
        ·
          refine ⟨9179372707208084386830005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119581804805389591220003 9179372707208084386830005)
          ·
            refine ⟨860566191300757911265313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9179372707208084386830005 860566191300757911265313)
            ·
              refine ⟨645424643475568433448985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860566191300757911265313 645424643475568433448985)
              ·
                refine ⟨484068482606676325086739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645424643475568433448985 484068482606676325086739)
                ·
                  refine ⟨726102723910014487630109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484068482606676325086739 726102723910014487630109)
                  ·
                    refine ⟨272288521466255432861291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726102723910014487630109 272288521466255432861291)
                    ·
                      rfl

theorem cell22_795420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_795420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795420 prefixEnd_795420 := by exact prefixLift 795420
  have htrace : WordTrace (prefixWord ++ tailWord_795420) baseStart_795420 baseEnd_795420 := by
    simpa [prefixWord, tailWord_795420, baseEnd_795420] using wordTrace_append hprefix tailTrace_795420
  have hstable : (prefixWord ++ tailWord_795420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795420).length < 2 ^ (prefixWord ++ tailWord_795420).sum := by decide
  have hdescent : baseEnd_795420 < baseStart_795420 := by decide
  rcases family_descends (prefixWord ++ tailWord_795420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795427 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 6]
def baseStart_795427 : Nat := 118140960795 + 795427 * 2 ^ 59
def prefixEnd_795427 : Nat := 4983230072969 + 3 ^ 40 * 795427 * 2
def baseEnd_795427 : Nat := 90763639236436582645423

theorem tailTrace_795427 : CollatzResearch.WordTrace tailWord_795427 prefixEnd_795427 90763639236436582645423 := by
  unfold tailWord_795427
  simp only [CollatzResearch.WordTrace]
  refine ⟨29011606089311301961288535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19341070726207534640859023 29011606089311301961288535)
  ·
    refine ⟨43517409133966952941932803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29011606089311301961288535 43517409133966952941932803)
    ·
      refine ⟨65276113700950429412899205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43517409133966952941932803 65276113700950429412899205)
      ·
        refine ⟨12239271318928205514918601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65276113700950429412899205 12239271318928205514918601)
        ·
          refine ⟨9179453489196154136188951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12239271318928205514918601 9179453489196154136188951)
          ·
            refine ⟨13769180233794231204283427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9179453489196154136188951 13769180233794231204283427)
            ·
              refine ⟨20653770350691346806425141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13769180233794231204283427 20653770350691346806425141)
              ·
                refine ⟨1936290970377313763102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20653770350691346806425141 1936290970377313763102357)
                ·
                  refine ⟨90763639236436582645423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1936290970377313763102357 90763639236436582645423)
                  ·
                    rfl

theorem cell22_795427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_795427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795427 prefixEnd_795427 := by exact prefixLift 795427
  have htrace : WordTrace (prefixWord ++ tailWord_795427) baseStart_795427 baseEnd_795427 := by
    simpa [prefixWord, tailWord_795427, baseEnd_795427] using wordTrace_append hprefix tailTrace_795427
  have hstable : (prefixWord ++ tailWord_795427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795427).length < 2 ^ (prefixWord ++ tailWord_795427).sum := by decide
  have hdescent : baseEnd_795427 < baseStart_795427 := by decide
  rcases family_descends (prefixWord ++ tailWord_795427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795459 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 4, 3]
def baseStart_795459 : Nat := 118140960795 + 795459 * 2 ^ 59
def prefixEnd_795459 : Nat := 4983230072969 + 3 ^ 40 * 795459 * 2
def baseEnd_795459 : Nat := 272301871963272331136171

theorem tailTrace_795459 : CollatzResearch.WordTrace tailWord_795459 prefixEnd_795459 272301871963272331136171 := by
  unfold tailWord_795459
  simp only [CollatzResearch.WordTrace]
  refine ⟨29012773225195371426453431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19341848816796914284302287 29012773225195371426453431)
  ·
    refine ⟨43519159837793057139680147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29012773225195371426453431 43519159837793057139680147)
    ·
      refine ⟨65278739756689585709520221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43519159837793057139680147 65278739756689585709520221)
      ·
        refine ⟨24479527408758594641070083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65278739756689585709520221 24479527408758594641070083)
        ·
          refine ⟨36719291113137891961605125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24479527408758594641070083 36719291113137891961605125)
          ·
            refine ⟨6884867083713354742800961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36719291113137891961605125 6884867083713354742800961)
            ·
              refine ⟨5163650312785016057100721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884867083713354742800961 5163650312785016057100721)
              ·
                refine ⟨3872737734588762042825541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5163650312785016057100721 3872737734588762042825541)
                ·
                  refine ⟨726138325235392883029789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3872737734588762042825541 726138325235392883029789)
                  ·
                    refine ⟨272301871963272331136171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726138325235392883029789 272301871963272331136171)
                    ·
                      rfl

theorem cell22_795459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 3].length) (baseStart_795459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795459 prefixEnd_795459 := by exact prefixLift 795459
  have htrace : WordTrace (prefixWord ++ tailWord_795459) baseStart_795459 baseEnd_795459 := by
    simpa [prefixWord, tailWord_795459, baseEnd_795459] using wordTrace_append hprefix tailTrace_795459
  have hstable : (prefixWord ++ tailWord_795459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795459).length < 2 ^ (prefixWord ++ tailWord_795459).sum := by decide
  have hdescent : baseEnd_795459 < baseStart_795459 := by decide
  rcases family_descends (prefixWord ++ tailWord_795459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795474 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_795474 : Nat := 118140960795 + 795474 * 2 ^ 59
def prefixEnd_795474 : Nat := 4983230072969 + 3 ^ 40 * 795474 * 2
def baseEnd_795474 : Nat := 272307006769817292011125

theorem tailTrace_795474 : CollatzResearch.WordTrace tailWord_795474 prefixEnd_795474 272307006769817292011125 := by
  unfold tailWord_795474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253330080035257247062369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19342213546760685992166317 7253330080035257247062369)
  ·
    refine ⟨5439997560026442935296777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7253330080035257247062369 5439997560026442935296777)
    ·
      refine ⟨4079998170019832201472583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5439997560026442935296777 4079998170019832201472583)
      ·
        refine ⟨6119997255029748302208875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4079998170019832201472583 6119997255029748302208875)
        ·
          refine ⟨9179995882544622453313313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6119997255029748302208875 9179995882544622453313313)
          ·
            refine ⟨6884996911908466839984985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9179995882544622453313313 6884996911908466839984985)
            ·
              refine ⟨5163747683931350129988739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6884996911908466839984985 5163747683931350129988739)
              ·
                refine ⟨7745621525897025194983109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163747683931350129988739 7745621525897025194983109)
                ·
                  refine ⟨1452304036105692224059333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7745621525897025194983109 1452304036105692224059333)
                  ·
                    refine ⟨272307006769817292011125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452304036105692224059333 272307006769817292011125)
                    ·
                      rfl

theorem cell22_795474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_795474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795474 prefixEnd_795474 := by exact prefixLift 795474
  have htrace : WordTrace (prefixWord ++ tailWord_795474) baseStart_795474 baseEnd_795474 := by
    simpa [prefixWord, tailWord_795474, baseEnd_795474] using wordTrace_append hprefix tailTrace_795474
  have hstable : (prefixWord ++ tailWord_795474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795474).length < 2 ^ (prefixWord ++ tailWord_795474).sum := by decide
  have hdescent : baseEnd_795474 < baseStart_795474 := by decide
  rcases family_descends (prefixWord ++ tailWord_795474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795549 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_795549 : Nat := 118140960795 + 795549 * 2 ^ 59
def prefixEnd_795549 : Nat := 4983230072969 + 3 ^ 40 * 795549 * 2
def baseEnd_795549 : Nat := 272332680802542096385895

theorem tailTrace_795549 : CollatzResearch.WordTrace tailWord_795549 prefixEnd_795549 272332680802542096385895 := by
  unfold tailWord_795549
  simp only [CollatzResearch.WordTrace]
  refine ⟨29016055794869316797229701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19344037196579544531486467 29016055794869316797229701)
  ·
    refine ⟨5440510461537996899480569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29016055794869316797229701 5440510461537996899480569)
    ·
      refine ⟨4080382846153497674610427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5440510461537996899480569 4080382846153497674610427)
      ·
        refine ⟨6120574269230246511915641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080382846153497674610427 6120574269230246511915641)
        ·
          refine ⟨4590430701922684883936731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6120574269230246511915641 4590430701922684883936731)
          ·
            refine ⟨6885646052884027325905097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590430701922684883936731 6885646052884027325905097)
            ·
              refine ⟨5164234539663020494428823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6885646052884027325905097 5164234539663020494428823)
              ·
                refine ⟨7746351809494530741643235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5164234539663020494428823 7746351809494530741643235)
                ·
                  refine ⟨11619527714241796112464853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7746351809494530741643235 11619527714241796112464853)
                  ·
                    refine ⟨272332680802542096385895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11619527714241796112464853 272332680802542096385895)
                    ·
                      rfl

theorem cell22_795549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_795549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795549 prefixEnd_795549 := by exact prefixLift 795549
  have htrace : WordTrace (prefixWord ++ tailWord_795549) baseStart_795549 baseEnd_795549 := by
    simpa [prefixWord, tailWord_795549, baseEnd_795549] using wordTrace_append hprefix tailTrace_795549
  have hstable : (prefixWord ++ tailWord_795549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795549).length < 2 ^ (prefixWord ++ tailWord_795549).sum := by decide
  have hdescent : baseEnd_795549 < baseStart_795549 := by decide
  rcases family_descends (prefixWord ++ tailWord_795549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795551 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 5]
def baseStart_795551 : Nat := 118140960795 + 795551 * 2 ^ 59
def prefixEnd_795551 : Nat := 4983230072969 + 3 ^ 40 * 795551 * 2
def baseEnd_795551 : Nat := 90777788481138252611963

theorem tailTrace_795551 : CollatzResearch.WordTrace tailWord_795551 prefixEnd_795551 90777788481138252611963 := by
  unfold tailWord_795551
  simp only [CollatzResearch.WordTrace]
  refine ⟨29016128740862071138802507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19344085827241380759201671 29016128740862071138802507)
  ·
    refine ⟨43524193111293106708203761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29016128740862071138802507 43524193111293106708203761)
    ·
      refine ⟨32643144833469830031152821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43524193111293106708203761 32643144833469830031152821)
      ·
        refine ⟨3060294828137796565420577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32643144833469830031152821 3060294828137796565420577)
        ·
          refine ⟨2295221121103347424065433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060294828137796565420577 2295221121103347424065433)
          ·
            refine ⟨1721415840827510568049075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295221121103347424065433 1721415840827510568049075)
            ·
              refine ⟨2582123761241265852073613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721415840827510568049075 2582123761241265852073613)
              ·
                refine ⟨968296410465474694527605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2582123761241265852073613 968296410465474694527605)
                ·
                  refine ⟨90777788481138252611963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 968296410465474694527605 90777788481138252611963)
                  ·
                    rfl

theorem cell22_795551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 5].length) (baseStart_795551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795551 prefixEnd_795551 := by exact prefixLift 795551
  have htrace : WordTrace (prefixWord ++ tailWord_795551) baseStart_795551 baseEnd_795551 := by
    simpa [prefixWord, tailWord_795551, baseEnd_795551] using wordTrace_append hprefix tailTrace_795551
  have hstable : (prefixWord ++ tailWord_795551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795551).length < 2 ^ (prefixWord ++ tailWord_795551).sum := by decide
  have hdescent : baseEnd_795551 < baseStart_795551 := by decide
  rcases family_descends (prefixWord ++ tailWord_795551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795564 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_795564 : Nat := 118140960795 + 795564 * 2 ^ 59
def prefixEnd_795564 : Nat := 4983230072969 + 3 ^ 40 * 795564 * 2
def baseEnd_795564 : Nat := 272337815609087057260849

theorem tailTrace_795564 : CollatzResearch.WordTrace tailWord_795564 prefixEnd_795564 272337815609087057260849 := by
  unfold tailWord_795564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14508301444907487179512873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19344401926543316239350497 14508301444907487179512873)
  ·
    refine ⟨10881226083680615384634655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14508301444907487179512873 10881226083680615384634655)
    ·
      refine ⟨16321839125520923076951983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10881226083680615384634655 16321839125520923076951983)
      ·
        refine ⟨24482758688281384615427975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16321839125520923076951983 24482758688281384615427975)
        ·
          refine ⟨36724138032422076923141963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24482758688281384615427975 36724138032422076923141963)
          ·
            refine ⟨55086207048633115384712945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36724138032422076923141963 55086207048633115384712945)
            ·
              refine ⟨41314655286474836538534709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55086207048633115384712945 41314655286474836538534709)
              ·
                refine ⟨3873248933107015925487629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41314655286474836538534709 3873248933107015925487629)
                ·
                  refine ⟨1452468349915130972057861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3873248933107015925487629 1452468349915130972057861)
                  ·
                    refine ⟨272337815609087057260849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452468349915130972057861 272337815609087057260849)
                    ·
                      rfl

theorem cell22_795564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_795564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795564 prefixEnd_795564 := by exact prefixLift 795564
  have htrace : WordTrace (prefixWord ++ tailWord_795564) baseStart_795564 baseEnd_795564 := by
    simpa [prefixWord, tailWord_795564, baseEnd_795564] using wordTrace_append hprefix tailTrace_795564
  have hstable : (prefixWord ++ tailWord_795564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795564).length < 2 ^ (prefixWord ++ tailWord_795564).sum := by decide
  have hdescent : baseEnd_795564 < baseStart_795564 := by decide
  rcases family_descends (prefixWord ++ tailWord_795564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795594 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_795594 : Nat := 118140960795 + 795594 * 2 ^ 59
def prefixEnd_795594 : Nat := 4983230072969 + 3 ^ 40 * 795594 * 2
def baseEnd_795594 : Nat := 272348085222176979010757

theorem tailTrace_795594 : CollatzResearch.WordTrace tailWord_795594 prefixEnd_795594 272348085222176979010757 := by
  unfold tailWord_795594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254424269926572370654459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19345131386470859655078557 7254424269926572370654459)
  ·
    refine ⟨10881636404889858555981689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254424269926572370654459 10881636404889858555981689)
    ·
      refine ⟨8161227303667393916986267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10881636404889858555981689 8161227303667393916986267)
      ·
        refine ⟨12241840955501090875479401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161227303667393916986267 12241840955501090875479401)
        ·
          refine ⟨9181380716625818156609551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12241840955501090875479401 9181380716625818156609551)
          ·
            refine ⟨13772071074938727234914327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9181380716625818156609551 13772071074938727234914327)
            ·
              refine ⟨20658106612408090852371491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13772071074938727234914327 20658106612408090852371491)
              ·
                refine ⟨30987159918612136278557237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20658106612408090852371491 30987159918612136278557237)
                ·
                  refine ⟨2905046242369887776114741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30987159918612136278557237 2905046242369887776114741)
                  ·
                    refine ⟨272348085222176979010757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2905046242369887776114741 272348085222176979010757)
                    ·
                      rfl

theorem cell22_795594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_795594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795594 prefixEnd_795594 := by exact prefixLift 795594
  have htrace : WordTrace (prefixWord ++ tailWord_795594) baseStart_795594 baseEnd_795594 := by
    simpa [prefixWord, tailWord_795594, baseEnd_795594] using wordTrace_append hprefix tailTrace_795594
  have hstable : (prefixWord ++ tailWord_795594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795594).length < 2 ^ (prefixWord ++ tailWord_795594).sum := by decide
  have hdescent : baseEnd_795594 < baseStart_795594 := by decide
  rcases family_descends (prefixWord ++ tailWord_795594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795624 : List Nat := [2, 1, 4, 1, 1, 1, 2, 10]
def baseStart_795624 : Nat := 118140960795 + 795624 * 2 ^ 59
def prefixEnd_795624 : Nat := 4983230072969 + 3 ^ 40 * 795624 * 2
def baseEnd_795624 : Nat := 30262039426140766751185

theorem tailTrace_795624 : CollatzResearch.WordTrace tailWord_795624 prefixEnd_795624 30262039426140766751185 := by
  unfold tailWord_795624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14509395634798802303104963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19345860846398403070806617 14509395634798802303104963)
  ·
    refine ⟨21764093452198203454657445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14509395634798802303104963 21764093452198203454657445)
    ·
      refine ⟨4080767522287163147748271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21764093452198203454657445 4080767522287163147748271)
      ·
        refine ⟨6121151283430744721622407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080767522287163147748271 6121151283430744721622407)
        ·
          refine ⟨9181726925146117082433611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121151283430744721622407 9181726925146117082433611)
          ·
            refine ⟨13772590387719175623650417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9181726925146117082433611 13772590387719175623650417)
            ·
              refine ⟨10329442790789381717737813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13772590387719175623650417 10329442790789381717737813)
              ·
                refine ⟨30262039426140766751185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10329442790789381717737813 30262039426140766751185)
                ·
                  rfl

theorem cell22_795624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_795624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795624 prefixEnd_795624 := by exact prefixLift 795624
  have htrace : WordTrace (prefixWord ++ tailWord_795624) baseStart_795624 baseEnd_795624 := by
    simpa [prefixWord, tailWord_795624, baseEnd_795624] using wordTrace_append hprefix tailTrace_795624
  have hstable : (prefixWord ++ tailWord_795624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795624).length < 2 ^ (prefixWord ++ tailWord_795624).sum := by decide
  have hdescent : baseEnd_795624 < baseStart_795624 := by decide
  rcases family_descends (prefixWord ++ tailWord_795624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795626 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_795626 : Nat := 118140960795 + 795626 * 2 ^ 59
def prefixEnd_795626 : Nat := 4983230072969 + 3 ^ 40 * 795626 * 2
def baseEnd_795626 : Nat := 272359039476139562210659

theorem tailTrace_795626 : CollatzResearch.WordTrace tailWord_795626 prefixEnd_795626 272359039476139562210659 := by
  unfold tailWord_795626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254716053897589736945683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19345909477060239298521821 7254716053897589736945683)
  ·
    refine ⟨10882074080846384605418525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7254716053897589736945683 10882074080846384605418525)
    ·
      refine ⟨4080777780317394227031947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10882074080846384605418525 4080777780317394227031947)
      ·
        refine ⟨6121166670476091340547921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080777780317394227031947 6121166670476091340547921)
        ·
          refine ⟨4590875002857068505410941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6121166670476091340547921 4590875002857068505410941)
          ·
            refine ⟨1721578126071400689529103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4590875002857068505410941 1721578126071400689529103)
            ·
              refine ⟨2582367189107101034293655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721578126071400689529103 2582367189107101034293655)
              ·
                refine ⟨3873550783660651551440483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582367189107101034293655 3873550783660651551440483)
                ·
                  refine ⟨5810326175490977327160725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3873550783660651551440483 5810326175490977327160725)
                  ·
                    refine ⟨272359039476139562210659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5810326175490977327160725 272359039476139562210659)
                    ·
                      rfl

theorem cell22_795626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_795626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795626 prefixEnd_795626 := by exact prefixLift 795626
  have htrace : WordTrace (prefixWord ++ tailWord_795626) baseStart_795626 baseEnd_795626 := by
    simpa [prefixWord, tailWord_795626, baseEnd_795626] using wordTrace_append hprefix tailTrace_795626
  have hstable : (prefixWord ++ tailWord_795626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795626).length < 2 ^ (prefixWord ++ tailWord_795626).sum := by decide
  have hdescent : baseEnd_795626 < baseStart_795626 := by decide
  rcases family_descends (prefixWord ++ tailWord_795626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795630 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_795630 : Nat := 118140960795 + 795630 * 2 ^ 59
def prefixEnd_795630 : Nat := 4983230072969 + 3 ^ 40 * 795630 * 2
def baseEnd_795630 : Nat := 90786802919294961703549

theorem tailTrace_795630 : CollatzResearch.WordTrace tailWord_795630 prefixEnd_795630 90786802919294961703549 := by
  unfold tailWord_795630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627376263446983453866043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19346006738383911753952229 3627376263446983453866043)
  ·
    refine ⟨5441064395170475180799065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3627376263446983453866043 5441064395170475180799065)
    ·
      refine ⟨4080798296377856385599299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5441064395170475180799065 4080798296377856385599299)
      ·
        refine ⟨6121197444566784578398949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080798296377856385599299 6121197444566784578398949)
        ·
          refine ⟨1147724520856272108449803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6121197444566784578398949 1147724520856272108449803)
          ·
            refine ⟨1721586781284408162674705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147724520856272108449803 1721586781284408162674705)
            ·
              refine ⟨1291190085963306122006029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721586781284408162674705 1291190085963306122006029)
              ·
                refine ⟨484196282236239795752261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291190085963306122006029 484196282236239795752261)
                ·
                  refine ⟨90786802919294961703549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484196282236239795752261 90786802919294961703549)
                  ·
                    rfl

theorem cell22_795630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_795630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795630 prefixEnd_795630 := by exact prefixLift 795630
  have htrace : WordTrace (prefixWord ++ tailWord_795630) baseStart_795630 baseEnd_795630 := by
    simpa [prefixWord, tailWord_795630, baseEnd_795630] using wordTrace_append hprefix tailTrace_795630
  have hstable : (prefixWord ++ tailWord_795630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795630).length < 2 ^ (prefixWord ++ tailWord_795630).sum := by decide
  have hdescent : baseEnd_795630 < baseStart_795630 := by decide
  rcases family_descends (prefixWord ++ tailWord_795630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795636 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 5]
def baseStart_795636 : Nat := 118140960795 + 795636 * 2 ^ 59
def prefixEnd_795636 : Nat := 4983230072969 + 3 ^ 40 * 795636 * 2
def baseEnd_795636 : Nat := 90787487560167623153543

theorem tailTrace_795636 : CollatzResearch.WordTrace tailWord_795636 prefixEnd_795636 90787487560167623153543 := by
  unfold tailWord_795636
  simp only [CollatzResearch.WordTrace]
  refine ⟨14509614472777065327823381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19346152630369420437097841 14509614472777065327823381)
  ·
    refine ⟨680138178411424937241721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14509614472777065327823381 680138178411424937241721)
    ·
      refine ⟨510103633808568702931291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680138178411424937241721 510103633808568702931291)
      ·
        refine ⟨765155450712853054396937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510103633808568702931291 765155450712853054396937)
        ·
          refine ⟨573866588034639790797703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765155450712853054396937 573866588034639790797703)
          ·
            refine ⟨860799882051959686196555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573866588034639790797703 860799882051959686196555)
            ·
              refine ⟨1291199823077939529294833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860799882051959686196555 1291199823077939529294833)
              ·
                refine ⟨968399867308454646971125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291199823077939529294833 968399867308454646971125)
                ·
                  refine ⟨90787487560167623153543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 968399867308454646971125 90787487560167623153543)
                  ·
                    rfl

theorem cell22_795636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_795636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795636 prefixEnd_795636 := by exact prefixLift 795636
  have htrace : WordTrace (prefixWord ++ tailWord_795636) baseStart_795636 baseEnd_795636 := by
    simpa [prefixWord, tailWord_795636, baseEnd_795636] using wordTrace_append hprefix tailTrace_795636
  have hstable : (prefixWord ++ tailWord_795636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795636).length < 2 ^ (prefixWord ++ tailWord_795636).sum := by decide
  have hdescent : baseEnd_795636 < baseStart_795636 := by decide
  rcases family_descends (prefixWord ++ tailWord_795636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795748 : List Nat := [2, 3, 1, 1, 2, 1, 1, 7, 4]
def baseStart_795748 : Nat := 118140960795 + 795748 * 2 ^ 59
def prefixEnd_795748 : Nat := 4983230072969 + 3 ^ 40 * 795748 * 2
def baseEnd_795748 : Nat := 90800267523123970220095

theorem tailTrace_795748 : CollatzResearch.WordTrace tailWord_795748 prefixEnd_795748 90800267523123970220095 := by
  unfold tailWord_795748
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511656960574186891861949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19348875947432249189149265 14511656960574186891861949)
  ·
    refine ⟨5441871360215320084448231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14511656960574186891861949 5441871360215320084448231)
    ·
      refine ⟨8162807040322980126672347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5441871360215320084448231 8162807040322980126672347)
      ·
        refine ⟨12244210560484470190008521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8162807040322980126672347 12244210560484470190008521)
        ·
          refine ⟨9183157920363352642506391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12244210560484470190008521 9183157920363352642506391)
          ·
            refine ⟨13774736880545028963759587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9183157920363352642506391 13774736880545028963759587)
            ·
              refine ⟨20662105320817543445639381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13774736880545028963759587 20662105320817543445639381)
              ·
                refine ⟨484268093456661174507173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20662105320817543445639381 484268093456661174507173)
                ·
                  refine ⟨90800267523123970220095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484268093456661174507173 90800267523123970220095)
                  ·
                    rfl

theorem cell22_795748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_795748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795748 prefixEnd_795748 := by exact prefixLift 795748
  have htrace : WordTrace (prefixWord ++ tailWord_795748) baseStart_795748 baseEnd_795748 := by
    simpa [prefixWord, tailWord_795748, baseEnd_795748] using wordTrace_append hprefix tailTrace_795748
  have hstable : (prefixWord ++ tailWord_795748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795748).length < 2 ^ (prefixWord ++ tailWord_795748).sum := by decide
  have hdescent : baseEnd_795748 < baseStart_795748 := by decide
  rcases family_descends (prefixWord ++ tailWord_795748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795761 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_795761 : Nat := 118140960795 + 795761 * 2 ^ 59
def prefixEnd_795761 : Nat := 4983230072969 + 3 ^ 40 * 795761 * 2
def baseEnd_795761 : Nat := 272405252735044210085245

theorem tailTrace_795761 : CollatzResearch.WordTrace tailWord_795761 prefixEnd_795761 272405252735044210085245 := by
  unfold tailWord_795761
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023788070101277003947137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19349192046734184669298091 29023788070101277003947137)
  ·
    refine ⟨21767841052575957752960353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29023788070101277003947137 21767841052575957752960353)
    ·
      refine ⟨16325880789431968314720265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21767841052575957752960353 16325880789431968314720265)
      ·
        refine ⟨12244410592073976236040199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16325880789431968314720265 12244410592073976236040199)
        ·
          refine ⟨18366615888110964354060299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244410592073976236040199 18366615888110964354060299)
          ·
            refine ⟨27549923832166446531090449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18366615888110964354060299 27549923832166446531090449)
            ·
              refine ⟨20662442874124834898317837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27549923832166446531090449 20662442874124834898317837)
              ·
                refine ⟨7748416077796813086869189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20662442874124834898317837 7748416077796813086869189)
                ·
                  refine ⟨1452828014586902453787973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7748416077796813086869189 1452828014586902453787973)
                  ·
                    refine ⟨272405252735044210085245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1452828014586902453787973 272405252735044210085245)
                    ·
                      rfl

theorem cell22_795761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_795761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795761 prefixEnd_795761 := by exact prefixLift 795761
  have htrace : WordTrace (prefixWord ++ tailWord_795761) baseStart_795761 baseEnd_795761 := by
    simpa [prefixWord, tailWord_795761, baseEnd_795761] using wordTrace_append hprefix tailTrace_795761
  have hstable : (prefixWord ++ tailWord_795761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795761).length < 2 ^ (prefixWord ++ tailWord_795761).sum := by decide
  have hdescent : baseEnd_795761 < baseStart_795761 := by decide
  rcases family_descends (prefixWord ++ tailWord_795761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795776 : List Nat := [2, 1, 1, 2, 1, 3, 5, 7]
def baseStart_795776 : Nat := 118140960795 + 795776 * 2 ^ 59
def prefixEnd_795776 : Nat := 4983230072969 + 3 ^ 40 * 795776 * 2
def baseEnd_795776 : Nat := 30267820837954352328911

theorem tailTrace_795776 : CollatzResearch.WordTrace tailWord_795776 prefixEnd_795776 30267820837954352328911 := by
  unfold tailWord_795776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512167582523467282871591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19349556776697956377162121 14512167582523467282871591)
  ·
    refine ⟨21768251373785200924307387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14512167582523467282871591 21768251373785200924307387)
    ·
      refine ⟨32652377060677801386461081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21768251373785200924307387 32652377060677801386461081)
      ·
        refine ⟨24489282795508351039845811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32652377060677801386461081 24489282795508351039845811)
        ·
          refine ⟨36733924193262526559768717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24489282795508351039845811 36733924193262526559768717)
          ·
            refine ⟨13775221572473447459913269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36733924193262526559768717 13775221572473447459913269)
            ·
              refine ⟨1291427022419385699366869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13775221572473447459913269 1291427022419385699366869)
              ·
                refine ⟨30267820837954352328911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1291427022419385699366869 30267820837954352328911)
                ·
                  rfl

theorem cell22_795776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_795776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795776 prefixEnd_795776 := by exact prefixLift 795776
  have htrace : WordTrace (prefixWord ++ tailWord_795776) baseStart_795776 baseEnd_795776 := by
    simpa [prefixWord, tailWord_795776, baseEnd_795776] using wordTrace_append hprefix tailTrace_795776
  have hstable : (prefixWord ++ tailWord_795776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795776).length < 2 ^ (prefixWord ++ tailWord_795776).sum := by decide
  have hdescent : baseEnd_795776 < baseStart_795776 := by decide
  rcases family_descends (prefixWord ++ tailWord_795776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795780 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_795780 : Nat := 118140960795 + 795780 * 2 ^ 59
def prefixEnd_795780 : Nat := 4983230072969 + 3 ^ 40 * 795780 * 2
def baseEnd_795780 : Nat := 272411756823334493860187

theorem tailTrace_795780 : CollatzResearch.WordTrace tailWord_795780 prefixEnd_795780 272411756823334493860187 := by
  unfold tailWord_795780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512240528516221624444397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19349654038021628832592529 14512240528516221624444397)
  ·
    refine ⟨5442090198193583109166649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14512240528516221624444397 5442090198193583109166649)
    ·
      refine ⟨4081567648645187331874987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5442090198193583109166649 4081567648645187331874987)
      ·
        refine ⟨6122351472967780997812481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081567648645187331874987 6122351472967780997812481)
        ·
          refine ⟨4591763604725835748359361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122351472967780997812481 4591763604725835748359361)
          ·
            refine ⟨3443822703544376811269521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4591763604725835748359361 3443822703544376811269521)
            ·
              refine ⟨2582867027658282608452141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443822703544376811269521 2582867027658282608452141)
              ·
                refine ⟨968575135371855978169553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2582867027658282608452141 968575135371855978169553)
                ·
                  refine ⟨726431351528891983627165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968575135371855978169553 726431351528891983627165)
                  ·
                    refine ⟨272411756823334493860187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726431351528891983627165 272411756823334493860187)
                    ·
                      rfl

theorem cell22_795780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_795780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795780 prefixEnd_795780 := by exact prefixLift 795780
  have htrace : WordTrace (prefixWord ++ tailWord_795780) baseStart_795780 baseEnd_795780 := by
    simpa [prefixWord, tailWord_795780, baseEnd_795780] using wordTrace_append hprefix tailTrace_795780
  have hstable : (prefixWord ++ tailWord_795780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795780).length < 2 ^ (prefixWord ++ tailWord_795780).sum := by decide
  have hdescent : baseEnd_795780 < baseStart_795780 := by decide
  rcases family_descends (prefixWord ++ tailWord_795780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795808 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_795808 : Nat := 118140960795 + 795808 * 2 ^ 59
def prefixEnd_795808 : Nat := 4983230072969 + 3 ^ 40 * 795808 * 2
def baseEnd_795808 : Nat := 272421341795551754160101

theorem tailTrace_795808 : CollatzResearch.WordTrace tailWord_795808 prefixEnd_795808 272421341795551754160101 := by
  unfold tailWord_795808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512751150465502015454039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19350334867287336020605385 14512751150465502015454039)
  ·
    refine ⟨21769126725698253023181059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14512751150465502015454039 21769126725698253023181059)
    ·
      refine ⟨32653690088547379534771589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21769126725698253023181059 32653690088547379534771589)
      ·
        refine ⟨6122566891602633662769673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32653690088547379534771589 6122566891602633662769673)
        ·
          refine ⟨4591925168701975247077255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122566891602633662769673 4591925168701975247077255)
          ·
            refine ⟨6887887753052962870615883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591925168701975247077255 6887887753052962870615883)
            ·
              refine ⟨10331831629579444305923825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6887887753052962870615883 10331831629579444305923825)
              ·
                refine ⟨7748873722184583229442869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10331831629579444305923825 7748873722184583229442869)
                ·
                  refine ⟨726456911454804677760269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7748873722184583229442869 726456911454804677760269)
                  ·
                    refine ⟨272421341795551754160101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726456911454804677760269 272421341795551754160101)
                    ·
                      rfl

theorem cell22_795808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_795808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795808 prefixEnd_795808 := by exact prefixLift 795808
  have htrace : WordTrace (prefixWord ++ tailWord_795808) baseStart_795808 baseEnd_795808 := by
    simpa [prefixWord, tailWord_795808, baseEnd_795808] using wordTrace_append hprefix tailTrace_795808
  have hstable : (prefixWord ++ tailWord_795808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795808).length < 2 ^ (prefixWord ++ tailWord_795808).sum := by decide
  have hdescent : baseEnd_795808 < baseStart_795808 := by decide
  rcases family_descends (prefixWord ++ tailWord_795808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795825 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 3, 3]
def baseStart_795825 : Nat := 118140960795 + 795825 * 2 ^ 59
def prefixEnd_795825 : Nat := 4983230072969 + 3 ^ 40 * 795825 * 2
def baseEnd_795825 : Nat := 272427161242969376485049

theorem tailTrace_795825 : CollatzResearch.WordTrace tailWord_795825 prefixEnd_795825 272427161242969376485049 := by
  unfold tailWord_795825
  simp only [CollatzResearch.WordTrace]
  refine ⟨29026122341869415934276929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19350748227912943956184619 29026122341869415934276929)
  ·
    refine ⟨21769591756402061950707697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29026122341869415934276929 21769591756402061950707697)
    ·
      refine ⟨16327193817301546463030773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21769591756402061950707697 16327193817301546463030773)
      ·
        refine ⟨1530674420372019980909135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16327193817301546463030773 1530674420372019980909135)
        ·
          refine ⟨2296011630558029971363703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530674420372019980909135 2296011630558029971363703)
          ·
            refine ⟨3444017445837044957045555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296011630558029971363703 3444017445837044957045555)
            ·
              refine ⟨5166026168755567435568333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444017445837044957045555 5166026168755567435568333)
              ·
                refine ⟨1937259813283337788338125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5166026168755567435568333 1937259813283337788338125)
                ·
                  refine ⟨726472429981251670626797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1937259813283337788338125 726472429981251670626797)
                  ·
                    refine ⟨272427161242969376485049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726472429981251670626797 272427161242969376485049)
                    ·
                      rfl

theorem cell22_795825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 3].length) (baseStart_795825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795825 prefixEnd_795825 := by exact prefixLift 795825
  have htrace : WordTrace (prefixWord ++ tailWord_795825) baseStart_795825 baseEnd_795825 := by
    simpa [prefixWord, tailWord_795825, baseEnd_795825] using wordTrace_append hprefix tailTrace_795825
  have hstable : (prefixWord ++ tailWord_795825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795825).length < 2 ^ (prefixWord ++ tailWord_795825).sum := by decide
  have hdescent : baseEnd_795825 < baseStart_795825 := by decide
  rcases family_descends (prefixWord ++ tailWord_795825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795881 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_795881 : Nat := 118140960795 + 795881 * 2 ^ 59
def prefixEnd_795881 : Nat := 4983230072969 + 3 ^ 40 * 795881 * 2
def baseEnd_795881 : Nat := 272446331187403897084877

theorem tailTrace_795881 : CollatzResearch.WordTrace tailWord_795881 prefixEnd_795881 272446331187403897084877 := by
  unfold tailWord_795881
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028164829666537498315497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19352109886444358332210331 29028164829666537498315497)
  ·
    refine ⟨21771123622249903123736623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29028164829666537498315497 21771123622249903123736623)
    ·
      refine ⟨32656685433374854685604935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21771123622249903123736623 32656685433374854685604935)
      ·
        refine ⟨48985028150062282028407403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32656685433374854685604935 48985028150062282028407403)
        ·
          refine ⟨73477542225093423042611105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48985028150062282028407403 73477542225093423042611105)
          ·
            refine ⟨55108156668820067281958329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73477542225093423042611105 55108156668820067281958329)
            ·
              refine ⟨41331117501615050461468747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55108156668820067281958329 41331117501615050461468747)
              ·
                refine ⟨61996676252422575692203121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41331117501615050461468747 61996676252422575692203121)
                ·
                  refine ⟨46497507189316931769152341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61996676252422575692203121 46497507189316931769152341)
                  ·
                    refine ⟨272446331187403897084877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46497507189316931769152341 272446331187403897084877)
                    ·
                      rfl

theorem cell22_795881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_795881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795881 prefixEnd_795881 := by exact prefixLift 795881
  have htrace : WordTrace (prefixWord ++ tailWord_795881) baseStart_795881 baseEnd_795881 := by
    simpa [prefixWord, tailWord_795881, baseEnd_795881] using wordTrace_append hprefix tailTrace_795881
  have hstable : (prefixWord ++ tailWord_795881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795881).length < 2 ^ (prefixWord ++ tailWord_795881).sum := by decide
  have hdescent : baseEnd_795881 < baseStart_795881 := by decide
  rcases family_descends (prefixWord ++ tailWord_795881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795883 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 6]
def baseStart_795883 : Nat := 118140960795 + 795883 * 2 ^ 59
def prefixEnd_795883 : Nat := 4983230072969 + 3 ^ 40 * 795883 * 2
def baseEnd_795883 : Nat := 90815671942758852844957

theorem tailTrace_795883 : CollatzResearch.WordTrace tailWord_795883 prefixEnd_795883 90815671942758852844957 := by
  unfold tailWord_795883
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028237775659291839888303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19352158517106194559925535 29028237775659291839888303)
  ·
    refine ⟨43542356663488937759832455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29028237775659291839888303 43542356663488937759832455)
    ·
      refine ⟨65313534995233406639748683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43542356663488937759832455 65313534995233406639748683)
      ·
        refine ⟨97970302492850109959623025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65313534995233406639748683 97970302492850109959623025)
        ·
          refine ⟨73477726869637582469717269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97970302492850109959623025 73477726869637582469717269)
          ·
            refine ⟨3444268447014261678267997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73477726869637582469717269 3444268447014261678267997)
            ·
              refine ⟨1291600667630348129350499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444268447014261678267997 1291600667630348129350499)
              ·
                refine ⟨1937401001445522194025749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291600667630348129350499 1937401001445522194025749)
                ·
                  refine ⟨90815671942758852844957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1937401001445522194025749 90815671942758852844957)
                  ·
                    rfl

theorem cell22_795883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 6].length) (baseStart_795883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795883 prefixEnd_795883 := by exact prefixLift 795883
  have htrace : WordTrace (prefixWord ++ tailWord_795883) baseStart_795883 baseEnd_795883 := by
    simpa [prefixWord, tailWord_795883, baseEnd_795883] using wordTrace_append hprefix tailTrace_795883
  have hstable : (prefixWord ++ tailWord_795883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795883).length < 2 ^ (prefixWord ++ tailWord_795883).sum := by decide
  have hdescent : baseEnd_795883 < baseStart_795883 := by decide
  rcases family_descends (prefixWord ++ tailWord_795883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795898 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_795898 : Nat := 118140960795 + 795898 * 2 ^ 59
def prefixEnd_795898 : Nat := 4983230072969 + 3 ^ 40 * 795898 * 2
def baseEnd_795898 : Nat := 272452150634821519409825

theorem tailTrace_795898 : CollatzResearch.WordTrace tailWord_795898 prefixEnd_795898 272452150634821519409825 := by
  unfold tailWord_795898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257196217651237350421087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19352523247069966267789565 7257196217651237350421087)
  ·
    refine ⟨10885794326476856025631631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257196217651237350421087 10885794326476856025631631)
    ·
      refine ⟨16328691489715284038447447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10885794326476856025631631 16328691489715284038447447)
      ·
        refine ⟨24493037234572926057671171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16328691489715284038447447 24493037234572926057671171)
        ·
          refine ⟨36739555851859389086506757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24493037234572926057671171 36739555851859389086506757)
          ·
            refine ⟨6888666722223635453720017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36739555851859389086506757 6888666722223635453720017)
            ·
              refine ⟨5166500041667726590290013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6888666722223635453720017 5166500041667726590290013)
              ·
                refine ⟨1937437515625397471358755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5166500041667726590290013 1937437515625397471358755)
                ·
                  refine ⟨2906156273438096207038133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1937437515625397471358755 2906156273438096207038133)
                  ·
                    refine ⟨272452150634821519409825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2906156273438096207038133 272452150634821519409825)
                    ·
                      rfl

theorem cell22_795898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_795898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795898 prefixEnd_795898 := by exact prefixLift 795898
  have htrace : WordTrace (prefixWord ++ tailWord_795898) baseStart_795898 baseEnd_795898 := by
    simpa [prefixWord, tailWord_795898, baseEnd_795898] using wordTrace_append hprefix tailTrace_795898
  have hstable : (prefixWord ++ tailWord_795898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795898).length < 2 ^ (prefixWord ++ tailWord_795898).sum := by decide
  have hdescent : baseEnd_795898 < baseStart_795898 := by decide
  rcases family_descends (prefixWord ++ tailWord_795898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795902 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_795902 : Nat := 118140960795 + 795902 * 2 ^ 59
def prefixEnd_795902 : Nat := 4983230072969 + 3 ^ 40 * 795902 * 2
def baseEnd_795902 : Nat := 272453519916566842309813

theorem tailTrace_795902 : CollatzResearch.WordTrace tailWord_795902 prefixEnd_795902 272453519916566842309813 := by
  unfold tailWord_795902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628616345323807260603745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19352620508393638723219973 3628616345323807260603745)
  ·
    refine ⟨2721462258992855445452809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3628616345323807260603745 2721462258992855445452809)
    ·
      refine ⟨2041096694244641584089607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2721462258992855445452809 2041096694244641584089607)
      ·
        refine ⟨3061645041366962376134411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041096694244641584089607 3061645041366962376134411)
        ·
          refine ⟨4592467562050443564201617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061645041366962376134411 4592467562050443564201617)
          ·
            refine ⟨3444350671537832673151213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4592467562050443564201617 3444350671537832673151213)
            ·
              refine ⟨1291631501826687252431705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444350671537832673151213 1291631501826687252431705)
              ·
                refine ⟨968723626370015439323779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291631501826687252431705 968723626370015439323779)
                ·
                  refine ⟨1453085439555023158985669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 968723626370015439323779 1453085439555023158985669)
                  ·
                    refine ⟨272453519916566842309813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453085439555023158985669 272453519916566842309813)
                    ·
                      rfl

theorem cell22_795902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_795902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795902 prefixEnd_795902 := by exact prefixLift 795902
  have htrace : WordTrace (prefixWord ++ tailWord_795902) baseStart_795902 baseEnd_795902 := by
    simpa [prefixWord, tailWord_795902, baseEnd_795902] using wordTrace_append hprefix tailTrace_795902
  have hstable : (prefixWord ++ tailWord_795902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795902).length < 2 ^ (prefixWord ++ tailWord_795902).sum := by decide
  have hdescent : baseEnd_795902 < baseStart_795902 := by decide
  rcases family_descends (prefixWord ++ tailWord_795902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795930 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_795930 : Nat := 118140960795 + 795930 * 2 ^ 59
def prefixEnd_795930 : Nat := 4983230072969 + 3 ^ 40 * 795930 * 2
def baseEnd_795930 : Nat := 272463104888784102609727

theorem tailTrace_795930 : CollatzResearch.WordTrace tailWord_795930 prefixEnd_795930 272463104888784102609727 := by
  unfold tailWord_795930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257488001622254716712311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19353301337659345911232829 7257488001622254716712311)
  ·
    refine ⟨10886232002433382075068467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257488001622254716712311 10886232002433382075068467)
    ·
      refine ⟨16329348003650073112602701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10886232002433382075068467 16329348003650073112602701)
      ·
        refine ⟨6123505501368777417226013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16329348003650073112602701 6123505501368777417226013)
        ·
          refine ⟨2296314563013291531459755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6123505501368777417226013 2296314563013291531459755)
          ·
            refine ⟨3444471844519937297189633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296314563013291531459755 3444471844519937297189633)
            ·
              refine ⟨2583353883389952972892225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444471844519937297189633 2583353883389952972892225)
              ·
                refine ⟨1937515412542464729669169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583353883389952972892225 1937515412542464729669169)
                ·
                  refine ⟨1453136559406848547251877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1937515412542464729669169 1453136559406848547251877)
                  ·
                    refine ⟨272463104888784102609727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453136559406848547251877 272463104888784102609727)
                    ·
                      rfl

theorem cell22_795930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_795930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795930 prefixEnd_795930 := by exact prefixLift 795930
  have htrace : WordTrace (prefixWord ++ tailWord_795930) baseStart_795930 baseEnd_795930 := by
    simpa [prefixWord, tailWord_795930, baseEnd_795930] using wordTrace_append hprefix tailTrace_795930
  have hstable : (prefixWord ++ tailWord_795930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795930).length < 2 ^ (prefixWord ++ tailWord_795930).sum := by decide
  have hdescent : baseEnd_795930 < baseStart_795930 := by decide
  rcases family_descends (prefixWord ++ tailWord_795930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795949 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_795949 : Nat := 118140960795 + 795949 * 2 ^ 59
def prefixEnd_795949 : Nat := 4983230072969 + 3 ^ 40 * 795949 * 2
def baseEnd_795949 : Nat := 272469608977074386384669

theorem tailTrace_795949 : CollatzResearch.WordTrace tailWord_795949 prefixEnd_795949 272469608977074386384669 := by
  unfold tailWord_795949
  simp only [CollatzResearch.WordTrace]
  refine ⟨29030644993420185111790901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19353763328946790074527267 29030644993420185111790901)
  ·
    refine ⟨2721622968133142354230397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29030644993420185111790901 2721622968133142354230397)
    ·
      refine ⟨1020608613049928382836399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2721622968133142354230397 1020608613049928382836399)
      ·
        refine ⟨1530912919574892574254599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020608613049928382836399 1530912919574892574254599)
        ·
          refine ⟨2296369379362338861381899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530912919574892574254599 2296369379362338861381899)
          ·
            refine ⟨3444554069043508292072849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296369379362338861381899 3444554069043508292072849)
            ·
              refine ⟨2583415551782631219054637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3444554069043508292072849 2583415551782631219054637)
              ·
                refine ⟨968780831918486707145489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583415551782631219054637 968780831918486707145489)
                ·
                  refine ⟨726585623938865030359117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968780831918486707145489 726585623938865030359117)
                  ·
                    refine ⟨272469608977074386384669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726585623938865030359117 272469608977074386384669)
                    ·
                      rfl

theorem cell22_795949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_795949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795949 prefixEnd_795949 := by exact prefixLift 795949
  have htrace : WordTrace (prefixWord ++ tailWord_795949) baseStart_795949 baseEnd_795949 := by
    simpa [prefixWord, tailWord_795949, baseEnd_795949] using wordTrace_append hprefix tailTrace_795949
  have hstable : (prefixWord ++ tailWord_795949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795949).length < 2 ^ (prefixWord ++ tailWord_795949).sum := by decide
  have hdescent : baseEnd_795949 < baseStart_795949 := by decide
  rcases family_descends (prefixWord ++ tailWord_795949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795977 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 1, 3]
def baseStart_795977 : Nat := 118140960795 + 795977 * 2 ^ 59
def prefixEnd_795977 : Nat := 4983230072969 + 3 ^ 40 * 795977 * 2
def baseEnd_795977 : Nat := 272479193949291646684583

theorem tailTrace_795977 : CollatzResearch.WordTrace tailWord_795977 prefixEnd_795977 272479193949291646684583 := by
  unfold tailWord_795977
  simp only [CollatzResearch.WordTrace]
  refine ⟨29031666237318745893810185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19354444158212497262540123 29031666237318745893810185)
  ·
    refine ⟨21773749677989059420357639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29031666237318745893810185 21773749677989059420357639)
    ·
      refine ⟨32660624516983589130536459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21773749677989059420357639 32660624516983589130536459)
      ·
        refine ⟨48990936775475383695804689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32660624516983589130536459 48990936775475383695804689)
        ·
          refine ⟨36743202581606537771853517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48990936775475383695804689 36743202581606537771853517)
          ·
            refine ⟨13778700968102451664445069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36743202581606537771853517 13778700968102451664445069)
            ·
              refine ⟨5167012863038419374166901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13778700968102451664445069 5167012863038419374166901)
              ·
                refine ⟨484407455909851816328147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5167012863038419374166901 484407455909851816328147)
                ·
                  refine ⟨726611183864777724492221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484407455909851816328147 726611183864777724492221)
                  ·
                    refine ⟨272479193949291646684583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726611183864777724492221 272479193949291646684583)
                    ·
                      rfl

theorem cell22_795977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 1, 3].length) (baseStart_795977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_795977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_795977 prefixEnd_795977 := by exact prefixLift 795977
  have htrace : WordTrace (prefixWord ++ tailWord_795977) baseStart_795977 baseEnd_795977 := by
    simpa [prefixWord, tailWord_795977, baseEnd_795977] using wordTrace_append hprefix tailTrace_795977
  have hstable : (prefixWord ++ tailWord_795977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795977).length < 2 ^ (prefixWord ++ tailWord_795977).sum := by decide
  have hdescent : baseEnd_795977 < baseStart_795977 := by decide
  rcases family_descends (prefixWord ++ tailWord_795977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796052 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_796052 : Nat := 118140960795 + 796052 * 2 ^ 59
def prefixEnd_796052 : Nat := 4983230072969 + 3 ^ 40 * 796052 * 2
def baseEnd_796052 : Nat := 90834955994005483686451

theorem tailTrace_796052 : CollatzResearch.WordTrace tailWord_796052 prefixEnd_796052 90834955994005483686451 := by
  unfold tailWord_796052
  simp only [CollatzResearch.WordTrace]
  refine ⟨14517200856023516851395205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19356267808031355801860273 14517200856023516851395205)
  ·
    refine ⟨2721975160504409409636601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14517200856023516851395205 2721975160504409409636601)
    ·
      refine ⟨2041481370378307057227451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2721975160504409409636601 2041481370378307057227451)
      ·
        refine ⟨3062222055567460585841177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041481370378307057227451 3062222055567460585841177)
        ·
          refine ⟨2296666541675595439380883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3062222055567460585841177 2296666541675595439380883)
          ·
            refine ⟨3444999812513393159071325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296666541675595439380883 3444999812513393159071325)
            ·
              refine ⟨1291874929692522434651747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3444999812513393159071325 1291874929692522434651747)
              ·
                refine ⟨1937812394538783651977621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291874929692522434651747 1937812394538783651977621)
                ·
                  refine ⟨90834955994005483686451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1937812394538783651977621 90834955994005483686451)
                  ·
                    rfl

theorem cell22_796052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_796052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796052 prefixEnd_796052 := by exact prefixLift 796052
  have htrace : WordTrace (prefixWord ++ tailWord_796052) baseStart_796052 baseEnd_796052 := by
    simpa [prefixWord, tailWord_796052, baseEnd_796052] using wordTrace_append hprefix tailTrace_796052
  have hstable : (prefixWord ++ tailWord_796052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796052).length < 2 ^ (prefixWord ++ tailWord_796052).sum := by decide
  have hdescent : baseEnd_796052 < baseStart_796052 := by decide
  rcases family_descends (prefixWord ++ tailWord_796052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796067 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 2, 3]
def baseStart_796067 : Nat := 118140960795 + 796067 * 2 ^ 59
def prefixEnd_796067 : Nat := 4983230072969 + 3 ^ 40 * 796067 * 2
def baseEnd_796067 : Nat := 272510002788561411934307

theorem tailTrace_796067 : CollatzResearch.WordTrace tailWord_796067 prefixEnd_796067 272510002788561411934307 := by
  unfold tailWord_796067
  simp only [CollatzResearch.WordTrace]
  refine ⟨29034948806992691264586455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19356632537995127509724303 29034948806992691264586455)
  ·
    refine ⟨43552423210489036896879683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29034948806992691264586455 43552423210489036896879683)
    ·
      refine ⟨65328634815733555345319525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43552423210489036896879683 65328634815733555345319525)
      ·
        refine ⟨12249119027950041627247411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65328634815733555345319525 12249119027950041627247411)
        ·
          refine ⟨18373678541925062440871117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12249119027950041627247411 18373678541925062440871117)
          ·
            refine ⟨6890129453221898415326669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18373678541925062440871117 6890129453221898415326669)
            ·
              refine ⟨2583798544958211905747501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6890129453221898415326669 2583798544958211905747501)
              ·
                refine ⟨968924454359329464655313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583798544958211905747501 968924454359329464655313)
                ·
                  refine ⟨726693340769497098491485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 968924454359329464655313 726693340769497098491485)
                  ·
                    refine ⟨272510002788561411934307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726693340769497098491485 272510002788561411934307)
                    ·
                      rfl

theorem cell22_796067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 3].length) (baseStart_796067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796067 prefixEnd_796067 := by exact prefixLift 796067
  have htrace : WordTrace (prefixWord ++ tailWord_796067) baseStart_796067 baseEnd_796067 := by
    simpa [prefixWord, tailWord_796067, baseEnd_796067] using wordTrace_append hprefix tailTrace_796067
  have hstable : (prefixWord ++ tailWord_796067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796067).length < 2 ^ (prefixWord ++ tailWord_796067).sum := by decide
  have hdescent : baseEnd_796067 < baseStart_796067 := by decide
  rcases family_descends (prefixWord ++ tailWord_796067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796110 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_796110 : Nat := 118140960795 + 796110 * 2 ^ 59
def prefixEnd_796110 : Nat := 4983230072969 + 3 ^ 40 * 796110 * 2
def baseEnd_796110 : Nat := 272524722567323633109175

theorem tailTrace_796110 : CollatzResearch.WordTrace tailWord_796110 prefixEnd_796110 272524722567323633109175 := by
  unfold tailWord_796110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629564643229613701050223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19357678097224606405601189 3629564643229613701050223)
  ·
    refine ⟨5444346964844420551575335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629564643229613701050223 5444346964844420551575335)
    ·
      refine ⟨8166520447266630827363003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444346964844420551575335 8166520447266630827363003)
      ·
        refine ⟨12249780670899946241044505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8166520447266630827363003 12249780670899946241044505)
        ·
          refine ⟨9187335503174959680783379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12249780670899946241044505 9187335503174959680783379)
          ·
            refine ⟨13781003254762439521175069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9187335503174959680783379 13781003254762439521175069)
            ·
              refine ⟨5167876220535914820440651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13781003254762439521175069 5167876220535914820440651)
              ·
                refine ⟨7751814330803872230660977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5167876220535914820440651 7751814330803872230660977)
                ·
                  refine ⟨5813860748102904172995733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7751814330803872230660977 5813860748102904172995733)
                  ·
                    refine ⟨272524722567323633109175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5813860748102904172995733 272524722567323633109175)
                    ·
                      rfl

theorem cell22_796110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_796110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796110 prefixEnd_796110 := by exact prefixLift 796110
  have htrace : WordTrace (prefixWord ++ tailWord_796110) baseStart_796110 baseEnd_796110 := by
    simpa [prefixWord, tailWord_796110, baseEnd_796110] using wordTrace_append hprefix tailTrace_796110
  have hstable : (prefixWord ++ tailWord_796110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796110).length < 2 ^ (prefixWord ++ tailWord_796110).sum := by decide
  have hdescent : baseEnd_796110 < baseStart_796110 := by decide
  rcases family_descends (prefixWord ++ tailWord_796110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796146 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_796146 : Nat := 118140960795 + 796146 * 2 ^ 59
def prefixEnd_796146 : Nat := 4983230072969 + 3 ^ 40 * 796146 * 2
def baseEnd_796146 : Nat := 272537046103031539209065

theorem tailTrace_796146 : CollatzResearch.WordTrace tailWord_796146 prefixEnd_796146 272537046103031539209065 := by
  unfold tailWord_796146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259457543426621939178073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19358553449137658504474861 7259457543426621939178073)
  ·
    refine ⟨5444593157569966454383555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7259457543426621939178073 5444593157569966454383555)
    ·
      refine ⟨8166889736354949681575333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444593157569966454383555 8166889736354949681575333)
      ·
        refine ⟨1531291825566553065295375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8166889736354949681575333 1531291825566553065295375)
        ·
          refine ⟨2296937738349829597943063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531291825566553065295375 2296937738349829597943063)
          ·
            refine ⟨3445406607524744396914595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296937738349829597943063 3445406607524744396914595)
            ·
              refine ⟨5168109911287116595371893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445406607524744396914595 5168109911287116595371893)
              ·
                refine ⟨484510304183167180816115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5168109911287116595371893 484510304183167180816115)
                ·
                  refine ⟨726765456274750771224173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484510304183167180816115 726765456274750771224173)
                  ·
                    refine ⟨272537046103031539209065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726765456274750771224173 272537046103031539209065)
                    ·
                      rfl

theorem cell22_796146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_796146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796146 prefixEnd_796146 := by exact prefixLift 796146
  have htrace : WordTrace (prefixWord ++ tailWord_796146) baseStart_796146 baseEnd_796146 := by
    simpa [prefixWord, tailWord_796146, baseEnd_796146] using wordTrace_append hprefix tailTrace_796146
  have hstable : (prefixWord ++ tailWord_796146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796146).length < 2 ^ (prefixWord ++ tailWord_796146).sum := by decide
  have hdescent : baseEnd_796146 < baseStart_796146 := by decide
  rcases family_descends (prefixWord ++ tailWord_796146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796189 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_796189 : Nat := 118140960795 + 796189 * 2 ^ 59
def prefixEnd_796189 : Nat := 4983230072969 + 3 ^ 40 * 796189 * 2
def baseEnd_796189 : Nat := 272551765881793760383933

theorem tailTrace_796189 : CollatzResearch.WordTrace tailWord_796189 prefixEnd_796189 272551765881793760383933 := by
  unfold tailWord_796189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29039398512550706100527621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19359599008367137400351747 29039398512550706100527621)
  ·
    refine ⟨5444887221103257393848929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29039398512550706100527621 5444887221103257393848929)
    ·
      refine ⟨4083665415827443045386697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5444887221103257393848929 4083665415827443045386697)
      ·
        refine ⟨3062749061870582284040023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4083665415827443045386697 3062749061870582284040023)
        ·
          refine ⟨4594123592805873426060035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062749061870582284040023 4594123592805873426060035)
          ·
            refine ⟨6891185389208810139090053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594123592805873426060035 6891185389208810139090053)
            ·
              refine ⟨1292097260476651901079385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6891185389208810139090053 1292097260476651901079385)
              ·
                refine ⟨969072945357488925809539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292097260476651901079385 969072945357488925809539)
                ·
                  refine ⟨1453609418036233388714309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 969072945357488925809539 1453609418036233388714309)
                  ·
                    refine ⟨272551765881793760383933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453609418036233388714309 272551765881793760383933)
                    ·
                      rfl

theorem cell22_796189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_796189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796189 prefixEnd_796189 := by exact prefixLift 796189
  have htrace : WordTrace (prefixWord ++ tailWord_796189) baseStart_796189 baseEnd_796189 := by
    simpa [prefixWord, tailWord_796189, baseEnd_796189] using wordTrace_append hprefix tailTrace_796189
  have hstable : (prefixWord ++ tailWord_796189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796189).length < 2 ^ (prefixWord ++ tailWord_796189).sum := by decide
  have hdescent : baseEnd_796189 < baseStart_796189 := by decide
  rcases family_descends (prefixWord ++ tailWord_796189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796202 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_796202 : Nat := 118140960795 + 796202 * 2 ^ 59
def prefixEnd_796202 : Nat := 4983230072969 + 3 ^ 40 * 796202 * 2
def baseEnd_796202 : Nat := 272556216047466059808893

theorem tailTrace_796202 : CollatzResearch.WordTrace tailWord_796202 prefixEnd_796202 272556216047466059808893 := by
  unfold tailWord_796202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259968165375902330187715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19359915107669072880500573 7259968165375902330187715)
  ·
    refine ⟨10889952248063853495281573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7259968165375902330187715 10889952248063853495281573)
    ·
      refine ⟨2041866046511972530365295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10889952248063853495281573 2041866046511972530365295)
      ·
        refine ⟨3062799069767958795547943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2041866046511972530365295 3062799069767958795547943)
        ·
          refine ⟨4594198604651938193321915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062799069767958795547943 4594198604651938193321915)
          ·
            refine ⟨6891297906977907289982873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594198604651938193321915 6891297906977907289982873)
            ·
              refine ⟨5168473430233430467487155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6891297906977907289982873 5168473430233430467487155)
              ·
                refine ⟨7752710145350145701230733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168473430233430467487155 7752710145350145701230733)
                ·
                  refine ⟨2907266304506304637961525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7752710145350145701230733 2907266304506304637961525)
                  ·
                    refine ⟨272556216047466059808893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2907266304506304637961525 272556216047466059808893)
                    ·
                      rfl

theorem cell22_796202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_796202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796202 prefixEnd_796202 := by exact prefixLift 796202
  have htrace : WordTrace (prefixWord ++ tailWord_796202) baseStart_796202 baseEnd_796202 := by
    simpa [prefixWord, tailWord_796202, baseEnd_796202] using wordTrace_append hprefix tailTrace_796202
  have hstable : (prefixWord ++ tailWord_796202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796202).length < 2 ^ (prefixWord ++ tailWord_796202).sum := by decide
  have hdescent : baseEnd_796202 < baseStart_796202 := by decide
  rcases family_descends (prefixWord ++ tailWord_796202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796215 : List Nat := [1, 1, 3, 1, 2, 4, 10]
def baseStart_796215 : Nat := 118140960795 + 796215 * 2 ^ 59
def prefixEnd_796215 : Nat := 4983230072969 + 3 ^ 40 * 796215 * 2
def baseEnd_796215 : Nat := 10094839489375494786439

theorem tailTrace_796215 : CollatzResearch.WordTrace tailWord_796215 prefixEnd_796215 10094839489375494786439 := by
  unfold tailWord_796215
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040346810456512540974099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19360231206971008360649399 29040346810456512540974099)
  ·
    refine ⟨43560520215684768811461149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29040346810456512540974099 43560520215684768811461149)
    ·
      refine ⟨16335195080881788304297931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43560520215684768811461149 16335195080881788304297931)
      ·
        refine ⟨24502792621322682456446897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16335195080881788304297931 24502792621322682456446897)
        ·
          refine ⟨18377094465992011842335173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24502792621322682456446897 18377094465992011842335173)
          ·
            refine ⟨3445705212373502220437845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18377094465992011842335173 3445705212373502220437845)
            ·
              refine ⟨10094839489375494786439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3445705212373502220437845 10094839489375494786439)
              ·
                rfl

theorem cell22_796215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 10].length) (baseStart_796215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796215 prefixEnd_796215 := by exact prefixLift 796215
  have htrace : WordTrace (prefixWord ++ tailWord_796215) baseStart_796215 baseEnd_796215 := by
    simpa [prefixWord, tailWord_796215, baseEnd_796215] using wordTrace_append hprefix tailTrace_796215
  have hstable : (prefixWord ++ tailWord_796215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796215).length < 2 ^ (prefixWord ++ tailWord_796215).sum := by decide
  have hdescent : baseEnd_796215 < baseStart_796215 := by decide
  rcases family_descends (prefixWord ++ tailWord_796215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796217 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_796217 : Nat := 118140960795 + 796217 * 2 ^ 59
def prefixEnd_796217 : Nat := 4983230072969 + 3 ^ 40 * 796217 * 2
def baseEnd_796217 : Nat := 272561350854011020683847

theorem tailTrace_796217 : CollatzResearch.WordTrace tailWord_796217 prefixEnd_796217 272561350854011020683847 := by
  unfold tailWord_796217
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040419756449266882546905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19360279837632844588364603 29040419756449266882546905)
  ·
    refine ⟨21780314817336950161910179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29040419756449266882546905 21780314817336950161910179)
    ·
      refine ⟨32670472226005425242865269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21780314817336950161910179 32670472226005425242865269)
      ·
        refine ⟨3062856771188008616518619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32670472226005425242865269 3062856771188008616518619)
        ·
          refine ⟨4594285156782012924777929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062856771188008616518619 4594285156782012924777929)
          ·
            refine ⟨3445713867586509693583447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594285156782012924777929 3445713867586509693583447)
            ·
              refine ⟨5168570801379764540375171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445713867586509693583447 5168570801379764540375171)
              ·
                refine ⟨7752856202069646810562757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5168570801379764540375171 7752856202069646810562757)
                ·
                  refine ⟨1453660537888058776980517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7752856202069646810562757 1453660537888058776980517)
                  ·
                    refine ⟨272561350854011020683847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1453660537888058776980517 272561350854011020683847)
                    ·
                      rfl

theorem cell22_796217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_796217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796217 prefixEnd_796217 := by exact prefixLift 796217
  have htrace : WordTrace (prefixWord ++ tailWord_796217) baseStart_796217 baseEnd_796217 := by
    simpa [prefixWord, tailWord_796217, baseEnd_796217] using wordTrace_append hprefix tailTrace_796217
  have hstable : (prefixWord ++ tailWord_796217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796217).length < 2 ^ (prefixWord ++ tailWord_796217).sum := by decide
  have hdescent : baseEnd_796217 < baseStart_796217 := by decide
  rcases family_descends (prefixWord ++ tailWord_796217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796221 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 6]
def baseStart_796221 : Nat := 118140960795 + 796221 * 2 ^ 59
def prefixEnd_796221 : Nat := 4983230072969 + 3 ^ 40 * 796221 * 2
def baseEnd_796221 : Nat := 90854240045252114527945

theorem tailTrace_796221 : CollatzResearch.WordTrace tailWord_796221 prefixEnd_796221 90854240045252114527945 := by
  unfold tailWord_796221
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040565648434775565692517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19360377098956517043795011 29040565648434775565692517)
  ·
    refine ⟨5445106059081520418567347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29040565648434775565692517 5445106059081520418567347)
    ·
      refine ⟨8167659088622280627851021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445106059081520418567347 8167659088622280627851021)
      ·
        refine ⟨3062872158233355235444133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8167659088622280627851021 3062872158233355235444133)
        ·
          refine ⟨574288529668754106645775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3062872158233355235444133 574288529668754106645775)
          ·
            refine ⟨861432794503131159968663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574288529668754106645775 861432794503131159968663)
            ·
              refine ⟨1292149191754696739952995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861432794503131159968663 1292149191754696739952995)
              ·
                refine ⟨1938223787632045109929493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292149191754696739952995 1938223787632045109929493)
                ·
                  refine ⟨90854240045252114527945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1938223787632045109929493 90854240045252114527945)
                  ·
                    rfl

theorem cell22_796221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_796221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796221 prefixEnd_796221 := by exact prefixLift 796221
  have htrace : WordTrace (prefixWord ++ tailWord_796221) baseStart_796221 baseEnd_796221 := by
    simpa [prefixWord, tailWord_796221, baseEnd_796221] using wordTrace_append hprefix tailTrace_796221
  have hstable : (prefixWord ++ tailWord_796221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796221).length < 2 ^ (prefixWord ++ tailWord_796221).sum := by decide
  have hdescent : baseEnd_796221 < baseStart_796221 := by decide
  rcases family_descends (prefixWord ++ tailWord_796221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796236 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_796236 : Nat := 118140960795 + 796236 * 2 ^ 59
def prefixEnd_796236 : Nat := 4983230072969 + 3 ^ 40 * 796236 * 2
def baseEnd_796236 : Nat := 272567854942301304458789

theorem tailTrace_796236 : CollatzResearch.WordTrace tailWord_796236 prefixEnd_796236 272567854942301304458789 := by
  unfold tailWord_796236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14520556371690216563744281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19360741828920288751659041 14520556371690216563744281)
  ·
    refine ⟨10890417278767662422808211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14520556371690216563744281 10890417278767662422808211)
    ·
      refine ⟨16335625918151493634212317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10890417278767662422808211 16335625918151493634212317)
      ·
        refine ⟨6125859719306810112829619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16335625918151493634212317 6125859719306810112829619)
        ·
          refine ⟨9188789578960215169244429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125859719306810112829619 9188789578960215169244429)
          ·
            refine ⟨3445796092110080688466661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9188789578960215169244429 3445796092110080688466661)
            ·
              refine ⟨646086767270640129087499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3445796092110080688466661 646086767270640129087499)
              ·
                refine ⟨969130150905960193631249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646086767270640129087499 969130150905960193631249)
                ·
                  refine ⟨726847613179470145223437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 969130150905960193631249 726847613179470145223437)
                  ·
                    refine ⟨272567854942301304458789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726847613179470145223437 272567854942301304458789)
                    ·
                      rfl

theorem cell22_796236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_796236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796236 prefixEnd_796236 := by exact prefixLift 796236
  have htrace : WordTrace (prefixWord ++ tailWord_796236) baseStart_796236 baseEnd_796236 := by
    simpa [prefixWord, tailWord_796236, baseEnd_796236] using wordTrace_append hprefix tailTrace_796236
  have hstable : (prefixWord ++ tailWord_796236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796236).length < 2 ^ (prefixWord ++ tailWord_796236).sum := by decide
  have hdescent : baseEnd_796236 < baseStart_796236 := by decide
  rcases family_descends (prefixWord ++ tailWord_796236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796281 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 1, 3]
def baseStart_796281 : Nat := 118140960795 + 796281 * 2 ^ 59
def prefixEnd_796281 : Nat := 4983230072969 + 3 ^ 40 * 796281 * 2
def baseEnd_796281 : Nat := 272583259361936187083651

theorem tailTrace_796281 : CollatzResearch.WordTrace tailWord_796281 prefixEnd_796281 272583259361936187083651 := by
  unfold tailWord_796281
  simp only [CollatzResearch.WordTrace]
  refine ⟨29042754028217405812876697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19361836018811603875251131 29042754028217405812876697)
  ·
    refine ⟨21782065521163054359657523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29042754028217405812876697 21782065521163054359657523)
    ·
      refine ⟨32673098281744581539486285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21782065521163054359657523 32673098281744581539486285)
      ·
        refine ⟨12252411855654218077307357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32673098281744581539486285 12252411855654218077307357)
        ·
          refine ⟨4594654445870331778990259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12252411855654218077307357 4594654445870331778990259)
          ·
            refine ⟨6891981668805497668485389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4594654445870331778990259 6891981668805497668485389)
            ·
              refine ⟨2584493125802061625682021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6891981668805497668485389 2584493125802061625682021)
              ·
                refine ⟨484592461087886554815379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2584493125802061625682021 484592461087886554815379)
                ·
                  refine ⟨726888691631829832223069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 484592461087886554815379 726888691631829832223069)
                  ·
                    refine ⟨272583259361936187083651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 726888691631829832223069 272583259361936187083651)
                    ·
                      rfl

theorem cell22_796281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 1, 3].length) (baseStart_796281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796281 prefixEnd_796281 := by exact prefixLift 796281
  have htrace : WordTrace (prefixWord ++ tailWord_796281) baseStart_796281 baseEnd_796281 := by
    simpa [prefixWord, tailWord_796281, baseEnd_796281] using wordTrace_append hprefix tailTrace_796281
  have hstable : (prefixWord ++ tailWord_796281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796281).length < 2 ^ (prefixWord ++ tailWord_796281).sum := by decide
  have hdescent : baseEnd_796281 < baseStart_796281 := by decide
  rcases family_descends (prefixWord ++ tailWord_796281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796328 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 7]
def baseStart_796328 : Nat := 118140960795 + 796328 * 2 ^ 59
def prefixEnd_796328 : Nat := 4983230072969 + 3 ^ 40 * 796328 * 2
def baseEnd_796328 : Nat := 90866449474147910386169

theorem tailTrace_796328 : CollatzResearch.WordTrace tailWord_796328 prefixEnd_796328 90866449474147910386169 := by
  unfold tailWord_796328
  simp only [CollatzResearch.WordTrace]
  refine ⟨14522234129523566419918819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19362978839364755226558425 14522234129523566419918819)
  ·
    refine ⟨21783351194285349629878229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14522234129523566419918819 21783351194285349629878229)
    ·
      refine ⟨510547293616062881950271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21783351194285349629878229 510547293616062881950271)
      ·
        refine ⟨765820940424094322925407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510547293616062881950271 765820940424094322925407)
        ·
          refine ⟨1148731410636141484388111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765820940424094322925407 1148731410636141484388111)
          ·
            refine ⟨1723097115954212226582167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148731410636141484388111 1723097115954212226582167)
            ·
              refine ⟨2584645673931318339873251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723097115954212226582167 2584645673931318339873251)
              ·
                refine ⟨3876968510896977509809877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584645673931318339873251 3876968510896977509809877)
                ·
                  refine ⟨90866449474147910386169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3876968510896977509809877 90866449474147910386169)
                  ·
                    rfl

theorem cell22_796328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 7].length) (baseStart_796328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796328 prefixEnd_796328 := by exact prefixLift 796328
  have htrace : WordTrace (prefixWord ++ tailWord_796328) baseStart_796328 baseEnd_796328 := by
    simpa [prefixWord, tailWord_796328, baseEnd_796328] using wordTrace_append hprefix tailTrace_796328
  have hstable : (prefixWord ++ tailWord_796328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796328).length < 2 ^ (prefixWord ++ tailWord_796328).sum := by decide
  have hdescent : baseEnd_796328 < baseStart_796328 := by decide
  rcases family_descends (prefixWord ++ tailWord_796328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796339 : List Nat := [1, 1, 1, 2, 3, 3, 1, 6, 4]
def baseStart_796339 : Nat := 118140960795 + 796339 * 2 ^ 59
def prefixEnd_796339 : Nat := 4983230072969 + 3 ^ 40 * 796339 * 2
def baseEnd_796339 : Nat := 90867704649081123044491

theorem tailTrace_796339 : CollatzResearch.WordTrace tailWord_796339 prefixEnd_796339 90867704649081123044491 := by
  unfold tailWord_796339
  simp only [CollatzResearch.WordTrace]
  refine ⟨29044869462007281718488071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19363246308004854478992047 29044869462007281718488071)
  ·
    refine ⟨43567304193010922577732107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29044869462007281718488071 43567304193010922577732107)
    ·
      refine ⟨65350956289516383866598161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43567304193010922577732107 65350956289516383866598161)
      ·
        refine ⟨49013217217137287899948621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65350956289516383866598161 49013217217137287899948621)
        ·
          refine ⟨18379956456426482962480733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49013217217137287899948621 18379956456426482962480733)
          ·
            refine ⟨6892483671159931110930275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18379956456426482962480733 6892483671159931110930275)
            ·
              refine ⟨10338725506739896666395413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892483671159931110930275 10338725506739896666395413)
              ·
                refine ⟨484627758128432656237285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10338725506739896666395413 484627758128432656237285)
                ·
                  refine ⟨90867704649081123044491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484627758128432656237285 90867704649081123044491)
                  ·
                    rfl

theorem cell22_796339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 6, 4].length) (baseStart_796339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796339 prefixEnd_796339 := by exact prefixLift 796339
  have htrace : WordTrace (prefixWord ++ tailWord_796339) baseStart_796339 baseEnd_796339 := by
    simpa [prefixWord, tailWord_796339, baseEnd_796339] using wordTrace_append hprefix tailTrace_796339
  have hstable : (prefixWord ++ tailWord_796339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796339).length < 2 ^ (prefixWord ++ tailWord_796339).sum := by decide
  have hdescent : baseEnd_796339 < baseStart_796339 := by decide
  rcases family_descends (prefixWord ++ tailWord_796339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796352 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_796352 : Nat := 118140960795 + 796352 * 2 ^ 59
def prefixEnd_796352 : Nat := 4983230072969 + 3 ^ 40 * 796352 * 2
def baseEnd_796352 : Nat := 272607564112915668558433

theorem tailTrace_796352 : CollatzResearch.WordTrace tailWord_796352 prefixEnd_796352 272607564112915668558433 := by
  unfold tailWord_796352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14522671805480092469355655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19363562407306789959140873 14522671805480092469355655)
  ·
    refine ⟨21784007708220138704033483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14522671805480092469355655 21784007708220138704033483)
    ·
      refine ⟨32676011562330208056050225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21784007708220138704033483 32676011562330208056050225)
      ·
        refine ⟨24507008671747656042037669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32676011562330208056050225 24507008671747656042037669)
        ·
          refine ⟨4595064125952685507882063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24507008671747656042037669 4595064125952685507882063)
          ·
            refine ⟨6892596188929028261823095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595064125952685507882063 6892596188929028261823095)
            ·
              refine ⟨10338894283393542392734643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892596188929028261823095 10338894283393542392734643)
              ·
                refine ⟨15508341425090313589101965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10338894283393542392734643 15508341425090313589101965)
                ·
                  refine ⟨5815628034408867595913237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15508341425090313589101965 5815628034408867595913237)
                  ·
                    refine ⟨272607564112915668558433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5815628034408867595913237 272607564112915668558433)
                    ·
                      rfl

theorem cell22_796352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_796352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796352 prefixEnd_796352 := by exact prefixLift 796352
  have htrace : WordTrace (prefixWord ++ tailWord_796352) baseStart_796352 baseEnd_796352 := by
    simpa [prefixWord, tailWord_796352, baseEnd_796352] using wordTrace_append hprefix tailTrace_796352
  have hstable : (prefixWord ++ tailWord_796352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796352).length < 2 ^ (prefixWord ++ tailWord_796352).sum := by decide
  have hdescent : baseEnd_796352 < baseStart_796352 := by decide
  rcases family_descends (prefixWord ++ tailWord_796352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796444 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_796444 : Nat := 118140960795 + 796444 * 2 ^ 59
def prefixEnd_796444 : Nat := 4983230072969 + 3 ^ 40 * 796444 * 2
def baseEnd_796444 : Nat := 272639057593058095258151

theorem tailTrace_796444 : CollatzResearch.WordTrace tailWord_796444 prefixEnd_796444 272639057593058095258151 := by
  unfold tailWord_796444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14524349563313442325530193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19365799417751256434040257 14524349563313442325530193)
  ·
    refine ⟨10893262172485081744147645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14524349563313442325530193 10893262172485081744147645)
    ·
      refine ⟨4084973314681905654055367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10893262172485081744147645 4084973314681905654055367)
      ·
        refine ⟨6127459972022858481083051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084973314681905654055367 6127459972022858481083051)
        ·
          refine ⟨9191189958034287721624577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127459972022858481083051 9191189958034287721624577)
          ·
            refine ⟨6893392468525715791218433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9191189958034287721624577 6893392468525715791218433)
            ·
              refine ⟨5170044351394286843413825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6893392468525715791218433 5170044351394286843413825)
              ·
                refine ⟨3877533263545715132560369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5170044351394286843413825 3877533263545715132560369)
                ·
                  refine ⟨2908149947659286349420277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3877533263545715132560369 2908149947659286349420277)
                  ·
                    refine ⟨272639057593058095258151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2908149947659286349420277 272639057593058095258151)
                    ·
                      rfl

theorem cell22_796444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_796444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796444 prefixEnd_796444 := by exact prefixLift 796444
  have htrace : WordTrace (prefixWord ++ tailWord_796444) baseStart_796444 baseEnd_796444 := by
    simpa [prefixWord, tailWord_796444, baseEnd_796444] using wordTrace_append hprefix tailTrace_796444
  have hstable : (prefixWord ++ tailWord_796444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796444).length < 2 ^ (prefixWord ++ tailWord_796444).sum := by decide
  have hdescent : baseEnd_796444 < baseStart_796444 := by decide
  rcases family_descends (prefixWord ++ tailWord_796444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796474 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_796474 : Nat := 118140960795 + 796474 * 2 ^ 59
def prefixEnd_796474 : Nat := 4983230072969 + 3 ^ 40 * 796474 * 2
def baseEnd_796474 : Nat := 90883109068716005669353

theorem tailTrace_796474 : CollatzResearch.WordTrace tailWord_796474 prefixEnd_796474 90883109068716005669353 := by
  unfold tailWord_796474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262448329129549943663119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19366528877678799849768317 7262448329129549943663119)
  ·
    refine ⟨10893672493694324915494679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7262448329129549943663119 10893672493694324915494679)
    ·
      refine ⟨16340508740541487373242019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10893672493694324915494679 16340508740541487373242019)
      ·
        refine ⟨24510763110812231059863029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16340508740541487373242019 24510763110812231059863029)
        ·
          refine ⟨2297884041638646661862159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24510763110812231059863029 2297884041638646661862159)
          ·
            refine ⟨3446826062457969992793239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297884041638646661862159 3446826062457969992793239)
            ·
              refine ⟨5170239093686954989189859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446826062457969992793239 5170239093686954989189859)
              ·
                refine ⟨7755358640530432483784789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170239093686954989189859 7755358640530432483784789)
                ·
                  refine ⟨90883109068716005669353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7755358640530432483784789 90883109068716005669353)
                  ·
                    rfl

theorem cell22_796474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_796474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796474 prefixEnd_796474 := by exact prefixLift 796474
  have htrace : WordTrace (prefixWord ++ tailWord_796474) baseStart_796474 baseEnd_796474 := by
    simpa [prefixWord, tailWord_796474, baseEnd_796474] using wordTrace_append hprefix tailTrace_796474
  have hstable : (prefixWord ++ tailWord_796474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796474).length < 2 ^ (prefixWord ++ tailWord_796474).sum := by decide
  have hdescent : baseEnd_796474 < baseStart_796474 := by decide
  rcases family_descends (prefixWord ++ tailWord_796474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796489 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_796489 : Nat := 118140960795 + 796489 * 2 ^ 59
def prefixEnd_796489 : Nat := 4983230072969 + 3 ^ 40 * 796489 * 2
def baseEnd_796489 : Nat := 272654462012692977883013

theorem tailTrace_796489 : CollatzResearch.WordTrace tailWord_796489 prefixEnd_796489 272654462012692977883013 := by
  unfold tailWord_796489
  simp only [CollatzResearch.WordTrace]
  refine ⟨29050340411463857336448521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19366893607642571557632347 29050340411463857336448521)
  ·
    refine ⟨21787755308597893002336391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29050340411463857336448521 21787755308597893002336391)
    ·
      refine ⟨32681632962896839503504587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21787755308597893002336391 32681632962896839503504587)
      ·
        refine ⟨49022449444345259255256881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32681632962896839503504587 49022449444345259255256881)
        ·
          refine ⟨36766837083258944441442661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49022449444345259255256881 36766837083258944441442661)
          ·
            refine ⟨6893781953111052082770499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36766837083258944441442661 6893781953111052082770499)
            ·
              refine ⟨10340672929666578124155749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893781953111052082770499 10340672929666578124155749)
              ·
                refine ⟨1938876174312483398279203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10340672929666578124155749 1938876174312483398279203)
                ·
                  refine ⟨2908314261468725097418805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1938876174312483398279203 2908314261468725097418805)
                  ·
                    refine ⟨272654462012692977883013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2908314261468725097418805 272654462012692977883013)
                    ·
                      rfl

theorem cell22_796489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_796489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796489 prefixEnd_796489 := by exact prefixLift 796489
  have htrace : WordTrace (prefixWord ++ tailWord_796489) baseStart_796489 baseEnd_796489 := by
    simpa [prefixWord, tailWord_796489, baseEnd_796489] using wordTrace_append hprefix tailTrace_796489
  have hstable : (prefixWord ++ tailWord_796489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796489).length < 2 ^ (prefixWord ++ tailWord_796489).sum := by decide
  have hdescent : baseEnd_796489 < baseStart_796489 := by decide
  rcases family_descends (prefixWord ++ tailWord_796489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796506 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_796506 : Nat := 118140960795 + 796506 * 2 ^ 59
def prefixEnd_796506 : Nat := 4983230072969 + 3 ^ 40 * 796506 * 2
def baseEnd_796506 : Nat := 272660281460110600207961

theorem tailTrace_796506 : CollatzResearch.WordTrace tailWord_796506 prefixEnd_796506 272660281460110600207961 := by
  unfold tailWord_796506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7262740113100567309954343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19367306968268179493211581 7262740113100567309954343)
  ·
    refine ⟨10894110169650850964931515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7262740113100567309954343 10894110169650850964931515)
    ·
      refine ⟨16341165254476276447397273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10894110169650850964931515 16341165254476276447397273)
      ·
        refine ⟨12255873940857207335547955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16341165254476276447397273 12255873940857207335547955)
        ·
          refine ⟨18383810911285811003321933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12255873940857207335547955 18383810911285811003321933)
          ·
            refine ⟨6893929091732179126245725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18383810911285811003321933 6893929091732179126245725)
            ·
              refine ⟨2585223409399567172342147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6893929091732179126245725 2585223409399567172342147)
              ·
                refine ⟨3877835114099350758513221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585223409399567172342147 3877835114099350758513221)
                ·
                  refine ⟨727094083893628267221229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3877835114099350758513221 727094083893628267221229)
                  ·
                    refine ⟨272660281460110600207961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727094083893628267221229 272660281460110600207961)
                    ·
                      rfl

theorem cell22_796506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_796506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796506 prefixEnd_796506 := by exact prefixLift 796506
  have htrace : WordTrace (prefixWord ++ tailWord_796506) baseStart_796506 baseEnd_796506 := by
    simpa [prefixWord, tailWord_796506, baseEnd_796506] using wordTrace_append hprefix tailTrace_796506
  have hstable : (prefixWord ++ tailWord_796506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796506).length < 2 ^ (prefixWord ++ tailWord_796506).sum := by decide
  have hdescent : baseEnd_796506 < baseStart_796506 := by decide
  rcases family_descends (prefixWord ++ tailWord_796506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796508 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_796508 : Nat := 118140960795 + 796508 * 2 ^ 59
def prefixEnd_796508 : Nat := 4983230072969 + 3 ^ 40 * 796508 * 2
def baseEnd_796508 : Nat := 90886988700327753885985

theorem tailTrace_796508 : CollatzResearch.WordTrace tailWord_796508 prefixEnd_796508 90886988700327753885985 := by
  unfold tailWord_796508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525516699197511790695089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19367355598930015720926785 14525516699197511790695089)
  ·
    refine ⟨10894137524398133843021317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14525516699197511790695089 10894137524398133843021317)
    ·
      refine ⟨2042650785824650095566497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10894137524398133843021317 2042650785824650095566497)
      ·
        refine ⟨1531988089368487571674873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2042650785824650095566497 1531988089368487571674873)
        ·
          refine ⟨1148991067026365678756155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1531988089368487571674873 1148991067026365678756155)
          ·
            refine ⟨1723486600539548518134233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148991067026365678756155 1723486600539548518134233)
            ·
              refine ⟨1292614950404661388600675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723486600539548518134233 1292614950404661388600675)
              ·
                refine ⟨1938922425606992082901013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292614950404661388600675 1938922425606992082901013)
                ·
                  refine ⟨90886988700327753885985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1938922425606992082901013 90886988700327753885985)
                  ·
                    rfl

theorem cell22_796508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_796508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796508 prefixEnd_796508 := by exact prefixLift 796508
  have htrace : WordTrace (prefixWord ++ tailWord_796508) baseStart_796508 baseEnd_796508 := by
    simpa [prefixWord, tailWord_796508, baseEnd_796508] using wordTrace_append hprefix tailTrace_796508
  have hstable : (prefixWord ++ tailWord_796508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796508).length < 2 ^ (prefixWord ++ tailWord_796508).sum := by decide
  have hdescent : baseEnd_796508 < baseStart_796508 := by decide
  rcases family_descends (prefixWord ++ tailWord_796508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796519 : List Nat := [1, 1, 5, 1, 2, 1, 2, 9]
def baseStart_796519 : Nat := 118140960795 + 796519 * 2 ^ 59
def prefixEnd_796519 : Nat := 4983230072969 + 3 ^ 40 * 796519 * 2
def baseEnd_796519 : Nat := 30296081291753655514769

theorem tailTrace_796519 : CollatzResearch.WordTrace tailWord_796519 prefixEnd_796519 30296081291753655514769 := by
  unfold tailWord_796519
  simp only [CollatzResearch.WordTrace]
  refine ⟨29051434601355172460040611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19367623067570114973360407 29051434601355172460040611)
  ·
    refine ⟨43577151902032758690060917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29051434601355172460040611 43577151902032758690060917)
    ·
      refine ⟨4085357990815571127193211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43577151902032758690060917 4085357990815571127193211)
      ·
        refine ⟨6128036986223356690789817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085357990815571127193211 6128036986223356690789817)
        ·
          refine ⟨4596027739667517518092363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6128036986223356690789817 4596027739667517518092363)
          ·
            refine ⟨6894041609501276277138545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596027739667517518092363 6894041609501276277138545)
            ·
              refine ⟨5170531207125957207853909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6894041609501276277138545 5170531207125957207853909)
              ·
                refine ⟨30296081291753655514769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5170531207125957207853909 30296081291753655514769)
                ·
                  rfl

theorem cell22_796519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 9].length) (baseStart_796519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796519 prefixEnd_796519 := by exact prefixLift 796519
  have htrace : WordTrace (prefixWord ++ tailWord_796519) baseStart_796519 baseEnd_796519 := by
    simpa [prefixWord, tailWord_796519, baseEnd_796519] using wordTrace_append hprefix tailTrace_796519
  have hstable : (prefixWord ++ tailWord_796519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796519).length < 2 ^ (prefixWord ++ tailWord_796519).sum := by decide
  have hdescent : baseEnd_796519 < baseStart_796519 := by decide
  rcases family_descends (prefixWord ++ tailWord_796519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796542 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_796542 : Nat := 118140960795 + 796542 * 2 ^ 59
def prefixEnd_796542 : Nat := 4983230072969 + 3 ^ 40 * 796542 * 2
def baseEnd_796542 : Nat := 90890868331939502102617

theorem tailTrace_796542 : CollatzResearch.WordTrace tailWord_796542 prefixEnd_796542 90890868331939502102617 := by
  unfold tailWord_796542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631534185033980923515985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19368182320181231592085253 3631534185033980923515985)
  ·
    refine ⟨2723650638775485692636989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3631534185033980923515985 2723650638775485692636989)
    ·
      refine ⟨1021368989540807134738871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2723650638775485692636989 1021368989540807134738871)
      ·
        refine ⟨1532053484311210702108307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021368989540807134738871 1532053484311210702108307)
        ·
          refine ⟨2298080226466816053162461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532053484311210702108307 2298080226466816053162461)
          ·
            refine ⟨861780084925056019935923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2298080226466816053162461 861780084925056019935923)
            ·
              refine ⟨1292670127387584029903885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861780084925056019935923 1292670127387584029903885)
              ·
                refine ⟨484751297770344011213957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1292670127387584029903885 484751297770344011213957)
                ·
                  refine ⟨90890868331939502102617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484751297770344011213957 90890868331939502102617)
                  ·
                    rfl

theorem cell22_796542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_796542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796542 prefixEnd_796542 := by exact prefixLift 796542
  have htrace : WordTrace (prefixWord ++ tailWord_796542) baseStart_796542 baseEnd_796542 := by
    simpa [prefixWord, tailWord_796542, baseEnd_796542] using wordTrace_append hprefix tailTrace_796542
  have hstable : (prefixWord ++ tailWord_796542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796542).length < 2 ^ (prefixWord ++ tailWord_796542).sum := by decide
  have hdescent : baseEnd_796542 < baseStart_796542 := by decide
  rcases family_descends (prefixWord ++ tailWord_796542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796579 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_796579 : Nat := 118140960795 + 796579 * 2 ^ 59
def prefixEnd_796579 : Nat := 4983230072969 + 3 ^ 40 * 796579 * 2
def baseEnd_796579 : Nat := 272685270851962743132737

theorem tailTrace_796579 : CollatzResearch.WordTrace tailWord_796579 prefixEnd_796579 272685270851962743132737 := by
  unfold tailWord_796579
  simp only [CollatzResearch.WordTrace]
  refine ⟨29053622981137802707224791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19369081987425201804816527 29053622981137802707224791)
  ·
    refine ⟨43580434471706704060837187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29053622981137802707224791 43580434471706704060837187)
    ·
      refine ⟨65370651707560056091255781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43580434471706704060837187 65370651707560056091255781)
      ·
        refine ⟨12256997195167510517110459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65370651707560056091255781 12256997195167510517110459)
        ·
          refine ⟨18385495792751265775665689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12256997195167510517110459 18385495792751265775665689)
          ·
            refine ⟨13789121844563449331749267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18385495792751265775665689 13789121844563449331749267)
            ·
              refine ⟨20683682766845173997623901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13789121844563449331749267 20683682766845173997623901)
              ·
                refine ⟨7756381037566940249108963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20683682766845173997623901 7756381037566940249108963)
                ·
                  refine ⟨11634571556350410373663445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7756381037566940249108963 11634571556350410373663445)
                  ·
                    refine ⟨272685270851962743132737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11634571556350410373663445 272685270851962743132737)
                    ·
                      rfl

theorem cell22_796579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_796579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796579 prefixEnd_796579 := by exact prefixLift 796579
  have htrace : WordTrace (prefixWord ++ tailWord_796579) baseStart_796579 baseEnd_796579 := by
    simpa [prefixWord, tailWord_796579, baseEnd_796579] using wordTrace_append hprefix tailTrace_796579
  have hstable : (prefixWord ++ tailWord_796579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796579).length < 2 ^ (prefixWord ++ tailWord_796579).sum := by decide
  have hdescent : baseEnd_796579 < baseStart_796579 := by decide
  rcases family_descends (prefixWord ++ tailWord_796579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796630 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_796630 : Nat := 118140960795 + 796630 * 2 ^ 59
def prefixEnd_796630 : Nat := 4983230072969 + 3 ^ 40 * 796630 * 2
def baseEnd_796630 : Nat := 272702729194215610107581

theorem tailTrace_796630 : CollatzResearch.WordTrace tailWord_796630 prefixEnd_796630 272702729194215610107581 := by
  unfold tailWord_796630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815967693997064901083209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19370322069302025611554229 1815967693997064901083209)
  ·
    refine ⟨1361975770497798675812407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1815967693997064901083209 1361975770497798675812407)
    ·
      refine ⟨2042963655746698013718611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1361975770497798675812407 2042963655746698013718611)
      ·
        refine ⟨3064445483620047020577917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042963655746698013718611 3064445483620047020577917)
        ·
          refine ⟨1149167056357517632716719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3064445483620047020577917 1149167056357517632716719)
          ·
            refine ⟨1723750584536276449075079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149167056357517632716719 1723750584536276449075079)
            ·
              refine ⟨2585625876804414673612619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723750584536276449075079 2585625876804414673612619)
              ·
                refine ⟨3878438815206622010418929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585625876804414673612619 3878438815206622010418929)
                ·
                  refine ⟨2908829111404966507814197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878438815206622010418929 2908829111404966507814197)
                  ·
                    refine ⟨272702729194215610107581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2908829111404966507814197 272702729194215610107581)
                    ·
                      rfl

theorem cell22_796630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_796630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796630 prefixEnd_796630 := by exact prefixLift 796630
  have htrace : WordTrace (prefixWord ++ tailWord_796630) baseStart_796630 baseEnd_796630 := by
    simpa [prefixWord, tailWord_796630, baseEnd_796630] using wordTrace_append hprefix tailTrace_796630
  have hstable : (prefixWord ++ tailWord_796630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796630).length < 2 ^ (prefixWord ++ tailWord_796630).sum := by decide
  have hdescent : baseEnd_796630 < baseStart_796630 := by decide
  rcases family_descends (prefixWord ++ tailWord_796630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796641 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_796641 : Nat := 118140960795 + 796641 * 2 ^ 59
def prefixEnd_796641 : Nat := 4983230072969 + 3 ^ 40 * 796641 * 2
def baseEnd_796641 : Nat := 272706494719015248082547

theorem tailTrace_796641 : CollatzResearch.WordTrace tailWord_796641 prefixEnd_796641 272706494719015248082547 := by
  unfold tailWord_796641
  simp only [CollatzResearch.WordTrace]
  refine ⟨29055884306913187295981777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19370589537942124863987851 29055884306913187295981777)
  ·
    refine ⟨21791913230184890471986333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29055884306913187295981777 21791913230184890471986333)
    ·
      refine ⟨8171967461319333926994875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21791913230184890471986333 8171967461319333926994875)
      ·
        refine ⟨12257951191979000890492313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8171967461319333926994875 12257951191979000890492313)
        ·
          refine ⟨9193463393984250667869235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12257951191979000890492313 9193463393984250667869235)
          ·
            refine ⟨13790195090976376001803853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9193463393984250667869235 13790195090976376001803853)
            ·
              refine ⟨5171323159116141000676445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13790195090976376001803853 5171323159116141000676445)
              ·
                refine ⟨1939246184668552875253667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5171323159116141000676445 1939246184668552875253667)
                ·
                  refine ⟨2908869277002829312880501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939246184668552875253667 2908869277002829312880501)
                  ·
                    refine ⟨272706494719015248082547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2908869277002829312880501 272706494719015248082547)
                    ·
                      rfl

theorem cell22_796641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_796641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796641 prefixEnd_796641 := by exact prefixLift 796641
  have htrace : WordTrace (prefixWord ++ tailWord_796641) baseStart_796641 baseEnd_796641 := by
    simpa [prefixWord, tailWord_796641, baseEnd_796641] using wordTrace_append hprefix tailTrace_796641
  have hstable : (prefixWord ++ tailWord_796641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796641).length < 2 ^ (prefixWord ++ tailWord_796641).sum := by decide
  have hdescent : baseEnd_796641 < baseStart_796641 := by decide
  rcases family_descends (prefixWord ++ tailWord_796641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796703 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 3, 3]
def baseStart_796703 : Nat := 118140960795 + 796703 * 2 ^ 59
def prefixEnd_796703 : Nat := 4983230072969 + 3 ^ 40 * 796703 * 2
def baseEnd_796703 : Nat := 272727718586067753032357

theorem tailTrace_796703 : CollatzResearch.WordTrace tailWord_796703 prefixEnd_796703 272727718586067753032357 := by
  unfold tailWord_796703
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058145632688571884738763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372097088459047923159175 29058145632688571884738763)
  ·
    refine ⟨43587218449032857827108145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29058145632688571884738763 43587218449032857827108145)
    ·
      refine ⟨32690413836774643370331109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43587218449032857827108145 32690413836774643370331109)
      ·
        refine ⟨6129452594395245631937083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32690413836774643370331109 6129452594395245631937083)
        ·
          refine ⟨9194178891592868447905625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6129452594395245631937083 9194178891592868447905625)
          ·
            refine ⟨6895634168694651335929219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9194178891592868447905625 6895634168694651335929219)
            ·
              refine ⟨10343451253041977003893829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6895634168694651335929219 10343451253041977003893829)
              ·
                refine ⟨1939397109945370688230093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10343451253041977003893829 1939397109945370688230093)
                ·
                  refine ⟨727273916229514008086285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1939397109945370688230093 727273916229514008086285)
                  ·
                    refine ⟨272727718586067753032357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727273916229514008086285 272727718586067753032357)
                    ·
                      rfl

theorem cell22_796703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3, 3].length) (baseStart_796703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796703 prefixEnd_796703 := by exact prefixLift 796703
  have htrace : WordTrace (prefixWord ++ tailWord_796703) baseStart_796703 baseEnd_796703 := by
    simpa [prefixWord, tailWord_796703, baseEnd_796703] using wordTrace_append hprefix tailTrace_796703
  have hstable : (prefixWord ++ tailWord_796703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796703).length < 2 ^ (prefixWord ++ tailWord_796703).sum := by decide
  have hdescent : baseEnd_796703 < baseStart_796703 := by decide
  rcases family_descends (prefixWord ++ tailWord_796703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796705 : List Nat := [1, 2, 3, 2, 4, 2, 2, 6]
def baseStart_796705 : Nat := 118140960795 + 796705 * 2 ^ 59
def prefixEnd_796705 : Nat := 4983230072969 + 3 ^ 40 * 796705 * 2
def baseEnd_796705 : Nat := 30303155914104490498039

theorem tailTrace_796705 : CollatzResearch.WordTrace tailWord_796705 prefixEnd_796705 30303155914104490498039 := by
  unfold tailWord_796705
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058218578681326226311569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372145719120884150874379 29058218578681326226311569)
  ·
    refine ⟨21793663934010994669733677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29058218578681326226311569 21793663934010994669733677)
    ·
      refine ⟨8172623975254123001150129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21793663934010994669733677 8172623975254123001150129)
      ·
        refine ⟨6129467981440592250862597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8172623975254123001150129 6129467981440592250862597)
        ·
          refine ⟨1149275246520111047036737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6129467981440592250862597 1149275246520111047036737)
          ·
            refine ⟨861956434890083285277553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149275246520111047036737 861956434890083285277553)
            ·
              refine ⟨646467326167562463958165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861956434890083285277553 646467326167562463958165)
              ·
                refine ⟨30303155914104490498039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 646467326167562463958165 30303155914104490498039)
                ·
                  rfl

theorem cell22_796705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 6].length) (baseStart_796705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796705 prefixEnd_796705 := by exact prefixLift 796705
  have htrace : WordTrace (prefixWord ++ tailWord_796705) baseStart_796705 baseEnd_796705 := by
    simpa [prefixWord, tailWord_796705, baseEnd_796705] using wordTrace_append hprefix tailTrace_796705
  have hstable : (prefixWord ++ tailWord_796705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796705).length < 2 ^ (prefixWord ++ tailWord_796705).sum := by decide
  have hdescent : baseEnd_796705 < baseStart_796705 := by decide
  rcases family_descends (prefixWord ++ tailWord_796705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796733 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 5]
def baseStart_796733 : Nat := 118140960795 + 796733 * 2 ^ 59
def prefixEnd_796733 : Nat := 4983230072969 + 3 ^ 40 * 796733 * 2
def baseEnd_796733 : Nat := 90912662733052558260755

theorem tailTrace_796733 : CollatzResearch.WordTrace tailWord_796733 prefixEnd_796733 90912662733052558260755 := by
  unfold tailWord_796733
  simp only [CollatzResearch.WordTrace]
  refine ⟨29059239822579887008330853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372826548386591338887235 29059239822579887008330853)
  ·
    refine ⟨5448607466733728814062035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29059239822579887008330853 5448607466733728814062035)
    ·
      refine ⟨8172911200100593221093053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5448607466733728814062035 8172911200100593221093053)
      ·
        refine ⟨3064841700037722457909895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8172911200100593221093053 3064841700037722457909895)
        ·
          refine ⟨4597262550056583686864843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064841700037722457909895 4597262550056583686864843)
          ·
            refine ⟨6895893825084875530297265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597262550056583686864843 6895893825084875530297265)
            ·
              refine ⟨5171920368813656647722949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6895893825084875530297265 5171920368813656647722949)
              ·
                refine ⟨969735069152560621448053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5171920368813656647722949 969735069152560621448053)
                ·
                  refine ⟨90912662733052558260755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 969735069152560621448053 90912662733052558260755)
                  ·
                    rfl

theorem cell22_796733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_796733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796733 prefixEnd_796733 := by exact prefixLift 796733
  have htrace : WordTrace (prefixWord ++ tailWord_796733) baseStart_796733 baseEnd_796733 := by
    simpa [prefixWord, tailWord_796733, baseEnd_796733] using wordTrace_append hprefix tailTrace_796733
  have hstable : (prefixWord ++ tailWord_796733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796733).length < 2 ^ (prefixWord ++ tailWord_796733).sum := by decide
  have hdescent : baseEnd_796733 < baseStart_796733 := by decide
  rcases family_descends (prefixWord ++ tailWord_796733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796737 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 3, 3]
def baseStart_796737 : Nat := 118140960795 + 796737 * 2 ^ 59
def prefixEnd_796737 : Nat := 4983230072969 + 3 ^ 40 * 796737 * 2
def baseEnd_796737 : Nat := 272739357480902997682253

theorem tailTrace_796737 : CollatzResearch.WordTrace tailWord_796737 prefixEnd_796737 272739357480902997682253 := by
  unfold tailWord_796737
  simp only [CollatzResearch.WordTrace]
  refine ⟨29059385714565395691476465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372923809710263794317643 29059385714565395691476465)
  ·
    refine ⟨21794539285924046768607349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29059385714565395691476465 21794539285924046768607349)
    ·
      refine ⟨2043238058055379384556939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21794539285924046768607349 2043238058055379384556939)
      ·
        refine ⟨3064857087083069076835409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043238058055379384556939 3064857087083069076835409)
        ·
          refine ⟨2298642815312301807626557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3064857087083069076835409 2298642815312301807626557)
          ·
            refine ⟨861991055742113177859959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2298642815312301807626557 861991055742113177859959)
            ·
              refine ⟨1292986583613169766789939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861991055742113177859959 1292986583613169766789939)
              ·
                refine ⟨1939479875419754650184909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1292986583613169766789939 1939479875419754650184909)
                ·
                  refine ⟨727304953282407993819341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1939479875419754650184909 727304953282407993819341)
                  ·
                    refine ⟨272739357480902997682253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727304953282407993819341 272739357480902997682253)
                    ·
                      rfl

theorem cell22_796737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_796737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796737 prefixEnd_796737 := by exact prefixLift 796737
  have htrace : WordTrace (prefixWord ++ tailWord_796737) baseStart_796737 baseEnd_796737 := by
    simpa [prefixWord, tailWord_796737, baseEnd_796737] using wordTrace_append hprefix tailTrace_796737
  have hstable : (prefixWord ++ tailWord_796737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796737).length < 2 ^ (prefixWord ++ tailWord_796737).sum := by decide
  have hdescent : baseEnd_796737 < baseStart_796737 := by decide
  rcases family_descends (prefixWord ++ tailWord_796737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796746 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_796746 : Nat := 118140960795 + 796746 * 2 ^ 59
def prefixEnd_796746 : Nat := 4983230072969 + 3 ^ 40 * 796746 * 2
def baseEnd_796746 : Nat := 272742438364829974207225

theorem tailTrace_796746 : CollatzResearch.WordTrace tailWord_796746 prefixEnd_796746 272742438364829974207225 := by
  unfold tailWord_796746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264928492883197557138523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19373142647688526819036061 7264928492883197557138523)
  ·
    refine ⟨10897392739324796335707785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264928492883197557138523 10897392739324796335707785)
    ·
      refine ⟨8173044554493597251780839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10897392739324796335707785 8173044554493597251780839)
      ·
        refine ⟨12259566831740395877671259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173044554493597251780839 12259566831740395877671259)
        ·
          refine ⟨18389350247610593816506889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259566831740395877671259 18389350247610593816506889)
          ·
            refine ⟨13792012685707945362380167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18389350247610593816506889 13792012685707945362380167)
            ·
              refine ⟨20688019028561918043570251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13792012685707945362380167 20688019028561918043570251)
              ·
                refine ⟨31032028542842877065355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20688019028561918043570251 31032028542842877065355377)
                ·
                  refine ⟨23274021407132157799016533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31032028542842877065355377 23274021407132157799016533)
                  ·
                    refine ⟨272742438364829974207225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23274021407132157799016533 272742438364829974207225)
                    ·
                      rfl

theorem cell22_796746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_796746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796746 prefixEnd_796746 := by exact prefixLift 796746
  have htrace : WordTrace (prefixWord ++ tailWord_796746) baseStart_796746 baseEnd_796746 := by
    simpa [prefixWord, tailWord_796746, baseEnd_796746] using wordTrace_append hprefix tailTrace_796746
  have hstable : (prefixWord ++ tailWord_796746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796746).length < 2 ^ (prefixWord ++ tailWord_796746).sum := by decide
  have hdescent : baseEnd_796746 < baseStart_796746 := by decide
  rcases family_descends (prefixWord ++ tailWord_796746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796750 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_796750 : Nat := 118140960795 + 796750 * 2 ^ 59
def prefixEnd_796750 : Nat := 4983230072969 + 3 ^ 40 * 796750 * 2
def baseEnd_796750 : Nat := 90914602548858432369071

theorem tailTrace_796750 : CollatzResearch.WordTrace tailWord_796750 prefixEnd_796750 90914602548858432369071 := by
  unfold tailWord_796750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632482482939787363962463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19373239909012199274466469 3632482482939787363962463)
  ·
    refine ⟨5448723724409681045943695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632482482939787363962463 5448723724409681045943695)
    ·
      refine ⟨8173085586614521568915543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5448723724409681045943695 8173085586614521568915543)
      ·
        refine ⟨12259628379921782353373315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173085586614521568915543 12259628379921782353373315)
        ·
          refine ⟨18389442569882673530059973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12259628379921782353373315 18389442569882673530059973)
          ·
            refine ⟨3448020481853001286886245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18389442569882673530059973 3448020481853001286886245)
            ·
              refine ⟨646503840347437741291171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3448020481853001286886245 646503840347437741291171)
              ·
                refine ⟨969755760521156611936757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646503840347437741291171 969755760521156611936757)
                ·
                  refine ⟨90914602548858432369071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 969755760521156611936757 90914602548858432369071)
                  ·
                    rfl

theorem cell22_796750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_796750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796750 prefixEnd_796750 := by exact prefixLift 796750
  have htrace : WordTrace (prefixWord ++ tailWord_796750) baseStart_796750 baseEnd_796750 := by
    simpa [prefixWord, tailWord_796750, baseEnd_796750] using wordTrace_append hprefix tailTrace_796750
  have hstable : (prefixWord ++ tailWord_796750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796750).length < 2 ^ (prefixWord ++ tailWord_796750).sum := by decide
  have hdescent : baseEnd_796750 < baseStart_796750 := by decide
  rcases family_descends (prefixWord ++ tailWord_796750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796761 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 8]
def baseStart_796761 : Nat := 118140960795 + 796761 * 2 ^ 59
def prefixEnd_796761 : Nat := 4983230072969 + 3 ^ 40 * 796761 * 2
def baseEnd_796761 : Nat := 90915857723791645027393

theorem tailTrace_796761 : CollatzResearch.WordTrace tailWord_796761 prefixEnd_796761 90915857723791645027393 := by
  unfold tailWord_796761
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060261066478447790350137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19373507377652298526900091 29060261066478447790350137)
  ·
    refine ⟨21795195799858835842762603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29060261066478447790350137 21795195799858835842762603)
    ·
      refine ⟨32692793699788253764143905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21795195799858835842762603 32692793699788253764143905)
      ·
        refine ⟨24519595274841190323107929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32692793699788253764143905 24519595274841190323107929)
        ·
          refine ⟨18389696456130892742330947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24519595274841190323107929 18389696456130892742330947)
          ·
            refine ⟨27584544684196339113496421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18389696456130892742330947 27584544684196339113496421)
            ·
              refine ⟨5172102128286813583780579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27584544684196339113496421 5172102128286813583780579)
              ·
                refine ⟨7758153192430220375670869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172102128286813583780579 7758153192430220375670869)
                ·
                  refine ⟨90915857723791645027393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7758153192430220375670869 90915857723791645027393)
                  ·
                    rfl

theorem cell22_796761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_796761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796761 prefixEnd_796761 := by exact prefixLift 796761
  have htrace : WordTrace (prefixWord ++ tailWord_796761) baseStart_796761 baseEnd_796761 := by
    simpa [prefixWord, tailWord_796761, baseEnd_796761] using wordTrace_append hprefix tailTrace_796761
  have hstable : (prefixWord ++ tailWord_796761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796761).length < 2 ^ (prefixWord ++ tailWord_796761).sum := by decide
  have hdescent : baseEnd_796761 < baseStart_796761 := by decide
  rcases family_descends (prefixWord ++ tailWord_796761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796810 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_796810 : Nat := 118140960795 + 796810 * 2 ^ 59
def prefixEnd_796810 : Nat := 4983230072969 + 3 ^ 40 * 796810 * 2
def baseEnd_796810 : Nat := 272764346872755140607029

theorem tailTrace_796810 : CollatzResearch.WordTrace tailWord_796810 prefixEnd_796810 272764346872755140607029 := by
  unfold tailWord_796810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265512060825232289720971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19374698828867286105922589 7265512060825232289720971)
  ·
    refine ⟨10898268091237848434581457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265512060825232289720971 10898268091237848434581457)
    ·
      refine ⟨8173701068428386325936093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10898268091237848434581457 8173701068428386325936093)
      ·
        refine ⟨3065137900660644872226035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8173701068428386325936093 3065137900660644872226035)
        ·
          refine ⟨4597706850990967308339053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065137900660644872226035 4597706850990967308339053)
          ·
            refine ⟨1724140069121612740627145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4597706850990967308339053 1724140069121612740627145)
            ·
              refine ⟨1293105051841209555470359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724140069121612740627145 1293105051841209555470359)
              ·
                refine ⟨1939657577761814333205539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293105051841209555470359 1939657577761814333205539)
                ·
                  refine ⟨2909486366642721499808309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939657577761814333205539 2909486366642721499808309)
                  ·
                    refine ⟨272764346872755140607029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2909486366642721499808309 272764346872755140607029)
                    ·
                      rfl

theorem cell22_796810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_796810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796810 prefixEnd_796810 := by exact prefixLift 796810
  have htrace : WordTrace (prefixWord ++ tailWord_796810) baseStart_796810 baseEnd_796810 := by
    simpa [prefixWord, tailWord_796810, baseEnd_796810] using wordTrace_append hprefix tailTrace_796810
  have hstable : (prefixWord ++ tailWord_796810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796810).length < 2 ^ (prefixWord ++ tailWord_796810).sum := by decide
  have hdescent : baseEnd_796810 < baseStart_796810 := by decide
  rcases family_descends (prefixWord ++ tailWord_796810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796855 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 3, 3]
def baseStart_796855 : Nat := 118140960795 + 796855 * 2 ^ 59
def prefixEnd_796855 : Nat := 4983230072969 + 3 ^ 40 * 796855 * 2
def baseEnd_796855 : Nat := 272779751292390023231891

theorem tailTrace_796855 : CollatzResearch.WordTrace tailWord_796855 prefixEnd_796855 272779751292390023231891 := by
  unfold tailWord_796855
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063689528137901844272019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375793018758601229514679 29063689528137901844272019)
  ·
    refine ⟨43595534292206852766408029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29063689528137901844272019 43595534292206852766408029)
    ·
      refine ⟨16348325359577569787403011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43595534292206852766408029 16348325359577569787403011)
      ·
        refine ⟨24522488039366354681104517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16348325359577569787403011 24522488039366354681104517)
        ·
          refine ⟨4597966507381191502707097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24522488039366354681104517 4597966507381191502707097)
          ·
            refine ⟨3448474880535893627030323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597966507381191502707097 3448474880535893627030323)
            ·
              refine ⟨5172712320803840440545485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448474880535893627030323 5172712320803840440545485)
              ·
                refine ⟨1939767120301440165204557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5172712320803840440545485 1939767120301440165204557)
                ·
                  refine ⟨727412670113040061951709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1939767120301440165204557 727412670113040061951709)
                  ·
                    refine ⟨272779751292390023231891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727412670113040061951709 272779751292390023231891)
                    ·
                      rfl

theorem cell22_796855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_796855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796855 prefixEnd_796855 := by exact prefixLift 796855
  have htrace : WordTrace (prefixWord ++ tailWord_796855) baseStart_796855 baseEnd_796855 := by
    simpa [prefixWord, tailWord_796855, baseEnd_796855] using wordTrace_append hprefix tailTrace_796855
  have hstable : (prefixWord ++ tailWord_796855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796855).length < 2 ^ (prefixWord ++ tailWord_796855).sum := by decide
  have hdescent : baseEnd_796855 < baseStart_796855 := by decide
  rcases family_descends (prefixWord ++ tailWord_796855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796932 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_796932 : Nat := 118140960795 + 796932 * 2 ^ 59
def prefixEnd_796932 : Nat := 4983230072969 + 3 ^ 40 * 796932 * 2
def baseEnd_796932 : Nat := 272806109965987489056655

theorem tailTrace_796932 : CollatzResearch.WordTrace tailWord_796932 prefixEnd_796932 272806109965987489056655 := by
  unfold tailWord_796932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14533248974429471997412525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19377665299239295996550033 14533248974429471997412525)
  ·
    refine ⟨5449968365411051999029697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14533248974429471997412525 5449968365411051999029697)
    ·
      refine ⟨4087476274058288999272273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5449968365411051999029697 4087476274058288999272273)
      ·
        refine ⟨3065607205543716749454205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4087476274058288999272273 3065607205543716749454205)
        ·
          refine ⟨1149602702078893781045327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3065607205543716749454205 1149602702078893781045327)
          ·
            refine ⟨1724404053118340671567991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149602702078893781045327 1724404053118340671567991)
            ·
              refine ⟨2586606079677511007351987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724404053118340671567991 2586606079677511007351987)
              ·
                refine ⟨3879909119516266511027981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586606079677511007351987 3879909119516266511027981)
                ·
                  refine ⟨1454965919818599941635493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3879909119516266511027981 1454965919818599941635493)
                  ·
                    refine ⟨272806109965987489056655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1454965919818599941635493 272806109965987489056655)
                    ·
                      rfl

theorem cell22_796932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_796932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796932 prefixEnd_796932 := by exact prefixLift 796932
  have htrace : WordTrace (prefixWord ++ tailWord_796932) baseStart_796932 baseEnd_796932 := by
    simpa [prefixWord, tailWord_796932, baseEnd_796932] using wordTrace_append hprefix tailTrace_796932
  have hstable : (prefixWord ++ tailWord_796932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796932).length < 2 ^ (prefixWord ++ tailWord_796932).sum := by decide
  have hdescent : baseEnd_796932 < baseStart_796932 := by decide
  rcases family_descends (prefixWord ++ tailWord_796932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796943 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_796943 : Nat := 118140960795 + 796943 * 2 ^ 59
def prefixEnd_796943 : Nat := 4983230072969 + 3 ^ 40 * 796943 * 2
def baseEnd_796943 : Nat := 272809875490787127031621

theorem tailTrace_796943 : CollatzResearch.WordTrace tailWord_796943 prefixEnd_796943 272809875490787127031621 := by
  unfold tailWord_796943
  simp only [CollatzResearch.WordTrace]
  refine ⟨29066899151819092873475483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19377932767879395248983655 29066899151819092873475483)
  ·
    refine ⟨43600348727728639310213225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29066899151819092873475483 43600348727728639310213225)
    ·
      refine ⟨32700261545796479482659919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43600348727728639310213225 32700261545796479482659919)
      ·
        refine ⟨49050392318694719223989879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32700261545796479482659919 49050392318694719223989879)
        ·
          refine ⟨73575588478042078835984819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49050392318694719223989879 73575588478042078835984819)
          ·
            refine ⟨110363382717063118253977229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73575588478042078835984819 110363382717063118253977229)
            ·
              refine ⟨41386268518898669345241461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110363382717063118253977229 41386268518898669345241461)
              ·
                refine ⟨3879962673646750251116387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41386268518898669345241461 3879962673646750251116387)
                ·
                  refine ⟨5819944010470125376674581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879962673646750251116387 5819944010470125376674581)
                  ·
                    refine ⟨272809875490787127031621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5819944010470125376674581 272809875490787127031621)
                    ·
                      rfl

theorem cell22_796943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_796943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796943 prefixEnd_796943 := by exact prefixLift 796943
  have htrace : WordTrace (prefixWord ++ tailWord_796943) baseStart_796943 baseEnd_796943 := by
    simpa [prefixWord, tailWord_796943, baseEnd_796943] using wordTrace_append hprefix tailTrace_796943
  have hstable : (prefixWord ++ tailWord_796943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796943).length < 2 ^ (prefixWord ++ tailWord_796943).sum := by decide
  have hdescent : baseEnd_796943 < baseStart_796943 := by decide
  rcases family_descends (prefixWord ++ tailWord_796943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796945 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_796945 : Nat := 118140960795 + 796945 * 2 ^ 59
def prefixEnd_796945 : Nat := 4983230072969 + 3 ^ 40 * 796945 * 2
def baseEnd_796945 : Nat := 272810560131659788481615

theorem tailTrace_796945 : CollatzResearch.WordTrace tailWord_796945 prefixEnd_796945 272810560131659788481615 := by
  unfold tailWord_796945
  simp only [CollatzResearch.WordTrace]
  refine ⟨29066972097811847215048289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19377981398541231476698859 29066972097811847215048289)
  ·
    refine ⟨21800229073358885411286217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29066972097811847215048289 21800229073358885411286217)
    ·
      refine ⟨16350171805019164058464663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21800229073358885411286217 16350171805019164058464663)
      ·
        refine ⟨24525257707528746087696995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16350171805019164058464663 24525257707528746087696995)
        ·
          refine ⟨36787886561293119131545493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24525257707528746087696995 36787886561293119131545493)
          ·
            refine ⟨1724432182560614959291195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36787886561293119131545493 1724432182560614959291195)
            ·
              refine ⟨2586648273840922438936793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724432182560614959291195 2586648273840922438936793)
              ·
                refine ⟨1939986205380691829202595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2586648273840922438936793 1939986205380691829202595)
                ·
                  refine ⟨2909979308071037743803893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939986205380691829202595 2909979308071037743803893)
                  ·
                    refine ⟨272810560131659788481615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2909979308071037743803893 272810560131659788481615)
                    ·
                      rfl

theorem cell22_796945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_796945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796945 prefixEnd_796945 := by exact prefixLift 796945
  have htrace : WordTrace (prefixWord ++ tailWord_796945) baseStart_796945 baseEnd_796945 := by
    simpa [prefixWord, tailWord_796945, baseEnd_796945] using wordTrace_append hprefix tailTrace_796945
  have hstable : (prefixWord ++ tailWord_796945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796945).length < 2 ^ (prefixWord ++ tailWord_796945).sum := by decide
  have hdescent : baseEnd_796945 < baseStart_796945 := by decide
  rcases family_descends (prefixWord ++ tailWord_796945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796964 : List Nat := [2, 3, 1, 3, 1, 2, 4, 2, 4]
def baseStart_796964 : Nat := 118140960795 + 796964 * 2 ^ 59
def prefixEnd_796964 : Nat := 4983230072969 + 3 ^ 40 * 796964 * 2
def baseEnd_796964 : Nat := 90939021406650024085519

theorem tailTrace_796964 : CollatzResearch.WordTrace tailWord_796964 prefixEnd_796964 90939021406650024085519 := by
  unfold tailWord_796964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14533832542371506729994973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19378443389828675639993297 14533832542371506729994973)
  ·
    refine ⟨5450187203389315023748115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14533832542371506729994973 5450187203389315023748115)
    ·
      refine ⟨8175280805083972535622173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5450187203389315023748115 8175280805083972535622173)
      ·
        refine ⟨3065730301906489700858315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8175280805083972535622173 3065730301906489700858315)
        ·
          refine ⟨4598595452859734551287473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065730301906489700858315 4598595452859734551287473)
          ·
            refine ⟨3448946589644800913465605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4598595452859734551287473 3448946589644800913465605)
            ·
              refine ⟨646677485558400171274801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3448946589644800913465605 646677485558400171274801)
              ·
                refine ⟨485008114168800128456101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646677485558400171274801 485008114168800128456101)
                ·
                  refine ⟨90939021406650024085519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485008114168800128456101 90939021406650024085519)
                  ·
                    rfl

theorem cell22_796964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_796964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_796964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_796964 prefixEnd_796964 := by exact prefixLift 796964
  have htrace : WordTrace (prefixWord ++ tailWord_796964) baseStart_796964 baseEnd_796964 := by
    simpa [prefixWord, tailWord_796964, baseEnd_796964] using wordTrace_append hprefix tailTrace_796964
  have hstable : (prefixWord ++ tailWord_796964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796964).length < 2 ^ (prefixWord ++ tailWord_796964).sum := by decide
  have hdescent : baseEnd_796964 < baseStart_796964 := by decide
  rcases family_descends (prefixWord ++ tailWord_796964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797024 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 3, 3]
def baseStart_797024 : Nat := 118140960795 + 797024 * 2 ^ 59
def prefixEnd_797024 : Nat := 4983230072969 + 3 ^ 40 * 797024 * 2
def baseEnd_797024 : Nat := 272837603446129915756373

theorem tailTrace_797024 : CollatzResearch.WordTrace tailWord_797024 prefixEnd_797024 272837603446129915756373 := by
  unfold tailWord_797024
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534926732262821853587063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19379902309683762471449417 14534926732262821853587063)
  ·
    refine ⟨21802390098394232780380595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14534926732262821853587063 21802390098394232780380595)
    ·
      refine ⟨32703585147591349170570893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21802390098394232780380595 32703585147591349170570893)
      ·
        refine ⟨12263844430346755938964085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32703585147591349170570893 12263844430346755938964085)
        ·
          refine ⟨1149735415345008369277883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12263844430346755938964085 1149735415345008369277883)
          ·
            refine ⟨1724603123017512553916825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149735415345008369277883 1724603123017512553916825)
            ·
              refine ⟨1293452342263134415437619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724603123017512553916825 1293452342263134415437619)
              ·
                refine ⟨1940178513394701623156429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293452342263134415437619 1940178513394701623156429)
                ·
                  refine ⟨727566942523013108683661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1940178513394701623156429 727566942523013108683661)
                  ·
                    refine ⟨272837603446129915756373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727566942523013108683661 272837603446129915756373)
                    ·
                      rfl

theorem cell22_797024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 3, 3].length) (baseStart_797024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797024 prefixEnd_797024 := by exact prefixLift 797024
  have htrace : WordTrace (prefixWord ++ tailWord_797024) baseStart_797024 baseEnd_797024 := by
    simpa [prefixWord, tailWord_797024, baseEnd_797024] using wordTrace_append hprefix tailTrace_797024
  have hstable : (prefixWord ++ tailWord_797024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797024).length < 2 ^ (prefixWord ++ tailWord_797024).sum := by decide
  have hdescent : baseEnd_797024 < baseStart_797024 := by decide
  rcases family_descends (prefixWord ++ tailWord_797024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797067 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 1, 4]
def baseStart_797067 : Nat := 118140960795 + 797067 * 2 ^ 59
def prefixEnd_797067 : Nat := 4983230072969 + 3 ^ 40 * 797067 * 2
def baseEnd_797067 : Nat := 272852323224892136931241

theorem tailTrace_797067 : CollatzResearch.WordTrace tailWord_797067 prefixEnd_797067 272852323224892136931241 := by
  unfold tailWord_797067
  simp only [CollatzResearch.WordTrace]
  refine ⟨29071421803369862050989455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19380947868913241367326303 29071421803369862050989455)
  ·
    refine ⟨43607132705054793076484183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29071421803369862050989455 43607132705054793076484183)
    ·
      refine ⟨65410699057582189614726275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43607132705054793076484183 65410699057582189614726275)
      ·
        refine ⟨98116048586373284422089413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65410699057582189614726275 98116048586373284422089413)
        ·
          refine ⟨18396759109944990829141765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98116048586373284422089413 18396759109944990829141765)
          ·
            refine ⟨3449392333114685780464081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18396759109944990829141765 3449392333114685780464081)
            ·
              refine ⟨2587044249836014335348061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3449392333114685780464081 2587044249836014335348061)
              ·
                refine ⟨970141593688505375755523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2587044249836014335348061 970141593688505375755523)
                ·
                  refine ⟨1455212390532758063633285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970141593688505375755523 1455212390532758063633285)
                  ·
                    refine ⟨272852323224892136931241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1455212390532758063633285 272852323224892136931241)
                    ·
                      rfl

theorem cell22_797067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 4].length) (baseStart_797067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797067 prefixEnd_797067 := by exact prefixLift 797067
  have htrace : WordTrace (prefixWord ++ tailWord_797067) baseStart_797067 baseEnd_797067 := by
    simpa [prefixWord, tailWord_797067, baseEnd_797067] using wordTrace_append hprefix tailTrace_797067
  have hstable : (prefixWord ++ tailWord_797067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797067).length < 2 ^ (prefixWord ++ tailWord_797067).sum := by decide
  have hdescent : baseEnd_797067 < baseStart_797067 := by decide
  rcases family_descends (prefixWord ++ tailWord_797067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797082 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_797082 : Nat := 118140960795 + 797082 * 2 ^ 59
def prefixEnd_797082 : Nat := 4983230072969 + 3 ^ 40 * 797082 * 2
def baseEnd_797082 : Nat := 90952486010479032602065

theorem tailTrace_797082 : CollatzResearch.WordTrace tailWord_797082 prefixEnd_797082 90952486010479032602065 := by
  unfold tailWord_797082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7267992224578879903196375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19381312598877013075190333 7267992224578879903196375)
  ·
    refine ⟨10901988336868319854794563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7267992224578879903196375 10901988336868319854794563)
    ·
      refine ⟨16352982505302479782191845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10901988336868319854794563 16352982505302479782191845)
      ·
        refine ⟨3066184219744214959160971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16352982505302479782191845 3066184219744214959160971)
        ·
          refine ⟨4599276329616322438741457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066184219744214959160971 4599276329616322438741457)
          ·
            refine ⟨3449457247212241829056093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4599276329616322438741457 3449457247212241829056093)
            ·
              refine ⟨1293546467704590685896035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3449457247212241829056093 1293546467704590685896035)
              ·
                refine ⟨1940319701556886028844053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293546467704590685896035 1940319701556886028844053)
                ·
                  refine ⟨90952486010479032602065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1940319701556886028844053 90952486010479032602065)
                  ·
                    rfl

theorem cell22_797082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_797082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797082 prefixEnd_797082 := by exact prefixLift 797082
  have htrace : WordTrace (prefixWord ++ tailWord_797082) baseStart_797082 baseEnd_797082 := by
    simpa [prefixWord, tailWord_797082, baseEnd_797082] using wordTrace_append hprefix tailTrace_797082
  have hstable : (prefixWord ++ tailWord_797082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797082).length < 2 ^ (prefixWord ++ tailWord_797082).sum := by decide
  have hdescent : baseEnd_797082 < baseStart_797082 := by decide
  rcases family_descends (prefixWord ++ tailWord_797082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797159 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 3, 3]
def baseStart_797159 : Nat := 118140960795 + 797159 * 2 ^ 59
def prefixEnd_797159 : Nat := 4983230072969 + 3 ^ 40 * 797159 * 2
def baseEnd_797159 : Nat := 272883816705034563630959

theorem tailTrace_797159 : CollatzResearch.WordTrace tailWord_797159 prefixEnd_797159 272883816705034563630959 := by
  unfold tailWord_797159
  simp only [CollatzResearch.WordTrace]
  refine ⟨29074777319036561763338531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19383184879357707842225687 29074777319036561763338531)
  ·
    refine ⟨43612165978554842645007797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29074777319036561763338531 43612165978554842645007797)
    ·
      refine ⟨4088640560489516497969481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43612165978554842645007797 4088640560489516497969481)
      ·
        refine ⟨3066480420367137373477111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4088640560489516497969481 3066480420367137373477111)
        ·
          refine ⟨4599720630550706060215667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066480420367137373477111 4599720630550706060215667)
          ·
            refine ⟨6899580945826059090323501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599720630550706060215667 6899580945826059090323501)
            ·
              refine ⟨2587342854684772158871313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6899580945826059090323501 2587342854684772158871313)
              ·
                refine ⟨1940507141013579119153485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2587342854684772158871313 1940507141013579119153485)
                ·
                  refine ⟨727690177880092169682557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1940507141013579119153485 727690177880092169682557)
                  ·
                    refine ⟨272883816705034563630959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727690177880092169682557 272883816705034563630959)
                    ·
                      rfl

theorem cell22_797159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_797159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797159 prefixEnd_797159 := by exact prefixLift 797159
  have htrace : WordTrace (prefixWord ++ tailWord_797159) baseStart_797159 baseEnd_797159 := by
    simpa [prefixWord, tailWord_797159, baseEnd_797159] using wordTrace_append hprefix tailTrace_797159
  have hstable : (prefixWord ++ tailWord_797159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797159).length < 2 ^ (prefixWord ++ tailWord_797159).sum := by decide
  have hdescent : baseEnd_797159 < baseStart_797159 := by decide
  rcases family_descends (prefixWord ++ tailWord_797159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797176 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 1, 3]
def baseStart_797176 : Nat := 118140960795 + 797176 * 2 ^ 59
def prefixEnd_797176 : Nat := 4983230072969 + 3 ^ 40 * 797176 * 2
def baseEnd_797176 : Nat := 272889636152452185955907

theorem tailTrace_797176 : CollatzResearch.WordTrace tailWord_797176 prefixEnd_797176 272889636152452185955907 := by
  unfold tailWord_797176
  simp only [CollatzResearch.WordTrace]
  refine ⟨14537698679987486833353691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19383598239983315777804921 14537698679987486833353691)
  ·
    refine ⟨21806548019981230250030537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14537698679987486833353691 21806548019981230250030537)
    ·
      refine ⟨16354911014985922687522903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21806548019981230250030537 16354911014985922687522903)
      ·
        refine ⟨24532366522478884031284355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354911014985922687522903 24532366522478884031284355)
        ·
          refine ⟨36798549783718326046926533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24532366522478884031284355 36798549783718326046926533)
          ·
            refine ⟨6899728084447186133798725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36798549783718326046926533 6899728084447186133798725)
            ·
              refine ⟨1293699015833847400087261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6899728084447186133798725 1293699015833847400087261)
              ·
                refine ⟨485137130937692775032723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293699015833847400087261 485137130937692775032723)
                ·
                  refine ⟨727705696406539162549085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485137130937692775032723 727705696406539162549085)
                  ·
                    refine ⟨272889636152452185955907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727705696406539162549085 272889636152452185955907)
                    ·
                      rfl

theorem cell22_797176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_797176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797176 prefixEnd_797176 := by exact prefixLift 797176
  have htrace : WordTrace (prefixWord ++ tailWord_797176) baseStart_797176 baseEnd_797176 := by
    simpa [prefixWord, tailWord_797176, baseEnd_797176] using wordTrace_append hprefix tailTrace_797176
  have hstable : (prefixWord ++ tailWord_797176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797176).length < 2 ^ (prefixWord ++ tailWord_797176).sum := by decide
  have hdescent : baseEnd_797176 < baseStart_797176 := by decide
  rcases family_descends (prefixWord ++ tailWord_797176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797217 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 6]
def baseStart_797217 : Nat := 118140960795 + 797217 * 2 ^ 59
def prefixEnd_797217 : Nat := 4983230072969 + 3 ^ 40 * 797217 * 2
def baseEnd_797217 : Nat := 90967890430113915226927

theorem tailTrace_797217 : CollatzResearch.WordTrace tailWord_797217 prefixEnd_797217 90967890430113915226927 := by
  unfold tailWord_797217
  simp only [CollatzResearch.WordTrace]
  refine ⟨29076892752826437668949905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19384595168550958445966603 29076892752826437668949905)
  ·
    refine ⟨21807669564619828251712429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29076892752826437668949905 21807669564619828251712429)
    ·
      refine ⟨8177876086732435594392161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21807669564619828251712429 8177876086732435594392161)
      ·
        refine ⟨6133407065049326695794121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8177876086732435594392161 6133407065049326695794121)
        ·
          refine ⟨4600055298786995021845591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6133407065049326695794121 4600055298786995021845591)
          ·
            refine ⟨6900082948180492532768387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600055298786995021845591 6900082948180492532768387)
            ·
              refine ⟨10350124422270738799152581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900082948180492532768387 10350124422270738799152581)
              ·
                refine ⟨1940648329175763524841109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10350124422270738799152581 1940648329175763524841109)
                ·
                  refine ⟨90967890430113915226927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1940648329175763524841109 90967890430113915226927)
                  ·
                    rfl

theorem cell22_797217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_797217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797217 prefixEnd_797217 := by exact prefixLift 797217
  have htrace : WordTrace (prefixWord ++ tailWord_797217) baseStart_797217 baseEnd_797217 := by
    simpa [prefixWord, tailWord_797217, baseEnd_797217] using wordTrace_append hprefix tailTrace_797217
  have hstable : (prefixWord ++ tailWord_797217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797217).length < 2 ^ (prefixWord ++ tailWord_797217).sum := by decide
  have hdescent : baseEnd_797217 < baseStart_797217 := by decide
  rcases family_descends (prefixWord ++ tailWord_797217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797219 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 1, 4]
def baseStart_797219 : Nat := 118140960795 + 797219 * 2 ^ 59
def prefixEnd_797219 : Nat := 4983230072969 + 3 ^ 40 * 797219 * 2
def baseEnd_797219 : Nat := 272904355931214407130775

theorem tailTrace_797219 : CollatzResearch.WordTrace tailWord_797219 prefixEnd_797219 272904355931214407130775 := by
  unfold tailWord_797219
  simp only [CollatzResearch.WordTrace]
  refine ⟨29076965698819192010522711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19384643799212794673681807 29076965698819192010522711)
  ·
    refine ⟨43615448548228788015784067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29076965698819192010522711 43615448548228788015784067)
    ·
      refine ⟨65423172822343182023676101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43615448548228788015784067 65423172822343182023676101)
      ·
        refine ⟨12266844904189346629439269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65423172822343182023676101 12266844904189346629439269)
        ·
          refine ⟨2300033419535502493019863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12266844904189346629439269 2300033419535502493019863)
          ·
            refine ⟨3450050129303253739529795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300033419535502493019863 3450050129303253739529795)
            ·
              refine ⟨5175075193954880609294693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450050129303253739529795 5175075193954880609294693)
              ·
                refine ⟨970326598866540114242755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5175075193954880609294693 970326598866540114242755)
                ·
                  refine ⟨1455489898299810171364133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970326598866540114242755 1455489898299810171364133)
                  ·
                    refine ⟨272904355931214407130775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1455489898299810171364133 272904355931214407130775)
                    ·
                      rfl

theorem cell22_797219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 4].length) (baseStart_797219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797219 prefixEnd_797219 := by exact prefixLift 797219
  have htrace : WordTrace (prefixWord ++ tailWord_797219) baseStart_797219 baseEnd_797219 := by
    simpa [prefixWord, tailWord_797219, baseEnd_797219] using wordTrace_append hprefix tailTrace_797219
  have hstable : (prefixWord ++ tailWord_797219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797219).length < 2 ^ (prefixWord ++ tailWord_797219).sum := by decide
  have hdescent : baseEnd_797219 < baseStart_797219 := by decide
  rcases family_descends (prefixWord ++ tailWord_797219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797232 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_797232 : Nat := 118140960795 + 797232 * 2 ^ 59
def prefixEnd_797232 : Nat := 4983230072969 + 3 ^ 40 * 797232 * 2
def baseEnd_797232 : Nat := 272908806096886706555735

theorem tailTrace_797232 : CollatzResearch.WordTrace tailWord_797232 prefixEnd_797232 272908806096886706555735 := by
  unfold tailWord_797232
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538719923886047615372975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19384959898514730153830633 14538719923886047615372975)
  ·
    refine ⟨21808079885829071423059463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14538719923886047615372975 21808079885829071423059463)
    ·
      refine ⟨32712119828743607134589195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21808079885829071423059463 32712119828743607134589195)
      ·
        refine ⟨49068179743115410701883793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32712119828743607134589195 49068179743115410701883793)
        ·
          refine ⟨36801134807336558026412845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49068179743115410701883793 36801134807336558026412845)
          ·
            refine ⟨13800425552751209259904817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36801134807336558026412845 13800425552751209259904817)
            ·
              refine ⟨10350319164563406944928613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13800425552751209259904817 10350319164563406944928613)
              ·
                refine ⟨1940684843355638802174115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10350319164563406944928613 1940684843355638802174115)
                ·
                  refine ⟨2911027265033458203261173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940684843355638802174115 2911027265033458203261173)
                  ·
                    refine ⟨272908806096886706555735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2911027265033458203261173 272908806096886706555735)
                    ·
                      rfl

theorem cell22_797232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_797232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797232 prefixEnd_797232 := by exact prefixLift 797232
  have htrace : WordTrace (prefixWord ++ tailWord_797232) baseStart_797232 baseEnd_797232 := by
    simpa [prefixWord, tailWord_797232, baseEnd_797232] using wordTrace_append hprefix tailTrace_797232
  have hstable : (prefixWord ++ tailWord_797232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797232).length < 2 ^ (prefixWord ++ tailWord_797232).sum := by decide
  have hdescent : baseEnd_797232 < baseStart_797232 := by decide
  rcases family_descends (prefixWord ++ tailWord_797232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797262 : List Nat := [4, 1, 1, 1, 1, 2, 3, 9]
def baseStart_797262 : Nat := 118140960795 + 797262 * 2 ^ 59
def prefixEnd_797262 : Nat := 4983230072969 + 3 ^ 40 * 797262 * 2
def baseEnd_797262 : Nat := 30324341745552958700627

theorem tailTrace_797262 : CollatzResearch.WordTrace tailWord_797262 prefixEnd_797262 30324341745552958700627 := by
  unfold tailWord_797262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634816754707926294292255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19385689358442273569558693 3634816754707926294292255)
  ·
    refine ⟨5452225132061889441438383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3634816754707926294292255 5452225132061889441438383)
    ·
      refine ⟨8178337698092834162157575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452225132061889441438383 8178337698092834162157575)
      ·
        refine ⟨12267506547139251243236363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178337698092834162157575 12267506547139251243236363)
        ·
          refine ⟨18401259820708876864854545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12267506547139251243236363 18401259820708876864854545)
          ·
            refine ⟨13800944865531657648640909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18401259820708876864854545 13800944865531657648640909)
            ·
              refine ⟨5175354324574371618240341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13800944865531657648640909 5175354324574371618240341)
              ·
                refine ⟨30324341745552958700627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5175354324574371618240341 30324341745552958700627)
                ·
                  rfl

theorem cell22_797262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_797262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797262 prefixEnd_797262 := by exact prefixLift 797262
  have htrace : WordTrace (prefixWord ++ tailWord_797262) baseStart_797262 baseEnd_797262 := by
    simpa [prefixWord, tailWord_797262, baseEnd_797262] using wordTrace_append hprefix tailTrace_797262
  have hstable : (prefixWord ++ tailWord_797262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797262).length < 2 ^ (prefixWord ++ tailWord_797262).sum := by decide
  have hdescent : baseEnd_797262 < baseStart_797262 := by decide
  rcases family_descends (prefixWord ++ tailWord_797262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797266 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_797266 : Nat := 118140960795 + 797266 * 2 ^ 59
def prefixEnd_797266 : Nat := 4983230072969 + 3 ^ 40 * 797266 * 2
def baseEnd_797266 : Nat := 272920444991721951205631

theorem tailTrace_797266 : CollatzResearch.WordTrace tailWord_797266 prefixEnd_797266 272920444991721951205631 := by
  unfold tailWord_797266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269669982412229759370913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19385786619765946024989101 7269669982412229759370913)
  ·
    refine ⟨5452252486809172319528185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7269669982412229759370913 5452252486809172319528185)
    ·
      refine ⟨4089189365106879239646139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5452252486809172319528185 4089189365106879239646139)
      ·
        refine ⟨6133784047660318859469209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4089189365106879239646139 6133784047660318859469209)
        ·
          refine ⟨4600338035745239144601907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6133784047660318859469209 4600338035745239144601907)
          ·
            refine ⟨6900507053617858716902861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600338035745239144601907 6900507053617858716902861)
            ·
              refine ⟨2587690145106697018838573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6900507053617858716902861 2587690145106697018838573)
              ·
                refine ⟨970383804415011382064465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2587690145106697018838573 970383804415011382064465)
                ·
                  refine ⟨727787853311258536548349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 970383804415011382064465 727787853311258536548349)
                  ·
                    refine ⟨272920444991721951205631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727787853311258536548349 272920444991721951205631)
                    ·
                      rfl

theorem cell22_797266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_797266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797266 prefixEnd_797266 := by exact prefixLift 797266
  have htrace : WordTrace (prefixWord ++ tailWord_797266) baseStart_797266 baseEnd_797266 := by
    simpa [prefixWord, tailWord_797266, baseEnd_797266] using wordTrace_append hprefix tailTrace_797266
  have hstable : (prefixWord ++ tailWord_797266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797266).length < 2 ^ (prefixWord ++ tailWord_797266).sum := by decide
  have hdescent : baseEnd_797266 < baseStart_797266 := by decide
  rcases family_descends (prefixWord ++ tailWord_797266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797302 : List Nat := [5, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_797302 : Nat := 118140960795 + 797302 * 2 ^ 59
def prefixEnd_797302 : Nat := 4983230072969 + 3 ^ 40 * 797302 * 2
def baseEnd_797302 : Nat := 90977589509143285768507

theorem tailTrace_797302 : CollatzResearch.WordTrace tailWord_797302 prefixEnd_797302 90977589509143285768507 := by
  unfold tailWord_797302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1817499559844906074112135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19386661971678998123862773 1817499559844906074112135)
  ·
    refine ⟨2726249339767359111168203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1817499559844906074112135 2726249339767359111168203)
    ·
      refine ⟨4089374009651038666752305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2726249339767359111168203 4089374009651038666752305)
      ·
        refine ⟨3067030507238279000064229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4089374009651038666752305 3067030507238279000064229)
        ·
          refine ⟨575068220107177312512043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3067030507238279000064229 575068220107177312512043)
          ·
            refine ⟨862602330160765968768065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575068220107177312512043 862602330160765968768065)
            ·
              refine ⟨646951747620574476576049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862602330160765968768065 646951747620574476576049)
              ·
                refine ⟨485213810715430857432037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646951747620574476576049 485213810715430857432037)
                ·
                  refine ⟨90977589509143285768507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485213810715430857432037 90977589509143285768507)
                  ·
                    rfl

theorem cell22_797302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_797302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797302 prefixEnd_797302 := by exact prefixLift 797302
  have htrace : WordTrace (prefixWord ++ tailWord_797302) baseStart_797302 baseEnd_797302 := by
    simpa [prefixWord, tailWord_797302, baseEnd_797302] using wordTrace_append hprefix tailTrace_797302
  have hstable : (prefixWord ++ tailWord_797302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797302).length < 2 ^ (prefixWord ++ tailWord_797302).sum := by decide
  have hdescent : baseEnd_797302 < baseStart_797302 := by decide
  rcases family_descends (prefixWord ++ tailWord_797302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797345 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 1, 3]
def baseStart_797345 : Nat := 118140960795 + 797345 * 2 ^ 59
def prefixEnd_797345 : Nat := 4983230072969 + 3 ^ 40 * 797345 * 2
def baseEnd_797345 : Nat := 272947488306192078480389

theorem tailTrace_797345 : CollatzResearch.WordTrace tailWord_797345 prefixEnd_797345 272947488306192078480389 := by
  unfold tailWord_797345
  simp only [CollatzResearch.WordTrace]
  refine ⟨29081561296362715529609489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19387707530908477019739659 29081561296362715529609489)
  ·
    refine ⟨21811170972272036647207117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29081561296362715529609489 21811170972272036647207117)
    ·
      refine ⟨8179189114602013742702669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21811170972272036647207117 8179189114602013742702669)
      ·
        refine ⟨3067195917975755153513501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8179189114602013742702669 3067195917975755153513501)
        ·
          refine ⟨1150198469240908182567563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3067195917975755153513501 1150198469240908182567563)
          ·
            refine ⟨1725297703861362273851345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150198469240908182567563 1725297703861362273851345)
            ·
              refine ⟨1293973277896021705388509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725297703861362273851345 1293973277896021705388509)
              ·
                refine ⟨485239979211008139520691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293973277896021705388509 485239979211008139520691)
                ·
                  refine ⟨727859968816512209281037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485239979211008139520691 727859968816512209281037)
                  ·
                    refine ⟨272947488306192078480389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727859968816512209281037 272947488306192078480389)
                    ·
                      rfl

theorem cell22_797345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_797345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797345 prefixEnd_797345 := by exact prefixLift 797345
  have htrace : WordTrace (prefixWord ++ tailWord_797345) baseStart_797345 baseEnd_797345 := by
    simpa [prefixWord, tailWord_797345, baseEnd_797345] using wordTrace_append hprefix tailTrace_797345
  have hstable : (prefixWord ++ tailWord_797345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797345).length < 2 ^ (prefixWord ++ tailWord_797345).sum := by decide
  have hdescent : baseEnd_797345 < baseStart_797345 := by decide
  rcases family_descends (prefixWord ++ tailWord_797345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797358 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_797358 : Nat := 118140960795 + 797358 * 2 ^ 59
def prefixEnd_797358 : Nat := 4983230072969 + 3 ^ 40 * 797358 * 2
def baseEnd_797358 : Nat := 90983979490621459301783

theorem tailTrace_797358 : CollatzResearch.WordTrace tailWord_797358 prefixEnd_797358 90983979490621459301783 := by
  unfold tailWord_797358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635254430664452343729091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19388023630210412499888485 3635254430664452343729091)
  ·
    refine ⟨5452881645996678515593637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3635254430664452343729091 5452881645996678515593637)
    ·
      refine ⟨1022415308624377221673807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5452881645996678515593637 1022415308624377221673807)
      ·
        refine ⟨1533622962936565832510711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022415308624377221673807 1533622962936565832510711)
        ·
          refine ⟨2300434444404848748766067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533622962936565832510711 2300434444404848748766067)
          ·
            refine ⟨3450651666607273123149101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300434444404848748766067 3450651666607273123149101)
            ·
              refine ⟨1293994374977727421180913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3450651666607273123149101 1293994374977727421180913)
              ·
                refine ⟨970495781233295565885685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293994374977727421180913 970495781233295565885685)
                ·
                  refine ⟨90983979490621459301783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 970495781233295565885685 90983979490621459301783)
                  ·
                    rfl

theorem cell22_797358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_797358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797358 prefixEnd_797358 := by exact prefixLift 797358
  have htrace : WordTrace (prefixWord ++ tailWord_797358) baseStart_797358 baseEnd_797358 := by
    simpa [prefixWord, tailWord_797358, baseEnd_797358] using wordTrace_append hprefix tailTrace_797358
  have hstable : (prefixWord ++ tailWord_797358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797358).length < 2 ^ (prefixWord ++ tailWord_797358).sum := by decide
  have hdescent : baseEnd_797358 < baseStart_797358 := by decide
  rcases family_descends (prefixWord ++ tailWord_797358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797388 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_797388 : Nat := 118140960795 + 797388 * 2 ^ 59
def prefixEnd_797388 : Nat := 4983230072969 + 3 ^ 40 * 797388 * 2
def baseEnd_797388 : Nat := 272962208084954299655257

theorem tailTrace_797388 : CollatzResearch.WordTrace tailWord_797388 prefixEnd_797388 272962208084954299655257 := by
  unfold tailWord_797388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14541564817603466936712409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19388753090137955915616545 14541564817603466936712409)
  ·
    refine ⟨10906173613202600202534307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14541564817603466936712409 10906173613202600202534307)
    ·
      refine ⟨16359260419803900303801461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10906173613202600202534307 16359260419803900303801461)
      ·
        refine ⟨1533680664356615653481387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16359260419803900303801461 1533680664356615653481387)
        ·
          refine ⟨2300520996534923480222081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533680664356615653481387 2300520996534923480222081)
          ·
            refine ⟨1725390747401192610166561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300520996534923480222081 1725390747401192610166561)
            ·
              refine ⟨1294043060550894457624921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725390747401192610166561 1294043060550894457624921)
              ·
                refine ⟨970532295413170843218691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294043060550894457624921 970532295413170843218691)
                ·
                  refine ⟨1455798443119756264828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970532295413170843218691 1455798443119756264828037)
                  ·
                    refine ⟨272962208084954299655257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1455798443119756264828037 272962208084954299655257)
                    ·
                      rfl

theorem cell22_797388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_797388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797388 prefixEnd_797388 := by exact prefixLift 797388
  have htrace : WordTrace (prefixWord ++ tailWord_797388) baseStart_797388 baseEnd_797388 := by
    simpa [prefixWord, tailWord_797388, baseEnd_797388] using wordTrace_append hprefix tailTrace_797388
  have hstable : (prefixWord ++ tailWord_797388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797388).length < 2 ^ (prefixWord ++ tailWord_797388).sum := by decide
  have hdescent : baseEnd_797388 < baseStart_797388 := by decide
  rcases family_descends (prefixWord ++ tailWord_797388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797399 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 1, 6]
def baseStart_797399 : Nat := 118140960795 + 797399 * 2 ^ 59
def prefixEnd_797399 : Nat := 4983230072969 + 3 ^ 40 * 797399 * 2
def baseEnd_797399 : Nat := 272965973609753937630223

theorem tailTrace_797399 : CollatzResearch.WordTrace tailWord_797399 prefixEnd_797399 272965973609753937630223 := by
  unfold tailWord_797399
  simp only [CollatzResearch.WordTrace]
  refine ⟨29083530838167082752075251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19389020558778055168050167 29083530838167082752075251)
  ·
    refine ⟨43625296257250624128112877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29083530838167082752075251 43625296257250624128112877)
    ·
      refine ⟨16359486096468984048042329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43625296257250624128112877 16359486096468984048042329)
      ·
        refine ⟨12269614572351738036031747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16359486096468984048042329 12269614572351738036031747)
        ·
          refine ⟨18404421858527607054047621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12269614572351738036031747 18404421858527607054047621)
          ·
            refine ⟨3450829098473926322633929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18404421858527607054047621 3450829098473926322633929)
            ·
              refine ⟨2588121823855444741975447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450829098473926322633929 2588121823855444741975447)
              ·
                refine ⟨3882182735783167112963171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588121823855444741975447 3882182735783167112963171)
                ·
                  refine ⟨5823274103674750669444757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882182735783167112963171 5823274103674750669444757)
                  ·
                    refine ⟨272965973609753937630223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5823274103674750669444757 272965973609753937630223)
                    ·
                      rfl

theorem cell22_797399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_797399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797399 prefixEnd_797399 := by exact prefixLift 797399
  have htrace : WordTrace (prefixWord ++ tailWord_797399) baseStart_797399 baseEnd_797399 := by
    simpa [prefixWord, tailWord_797399, baseEnd_797399] using wordTrace_append hprefix tailTrace_797399
  have hstable : (prefixWord ++ tailWord_797399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797399).length < 2 ^ (prefixWord ++ tailWord_797399).sum := by decide
  have hdescent : baseEnd_797399 < baseStart_797399 := by decide
  rcases family_descends (prefixWord ++ tailWord_797399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797480 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 1, 3]
def baseStart_797480 : Nat := 118140960795 + 797480 * 2 ^ 59
def prefixEnd_797480 : Nat := 4983230072969 + 3 ^ 40 * 797480 * 2
def baseEnd_797480 : Nat := 272993701565096726354975

theorem tailTrace_797480 : CollatzResearch.WordTrace tailWord_797480 prefixEnd_797480 272993701565096726354975 := by
  unfold tailWord_797480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14543242575436816792886947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19390990100582422390515929 14543242575436816792886947)
  ·
    refine ⟨21814863863155225189330421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14543242575436816792886947 21814863863155225189330421)
    ·
      refine ⟨2045143487170802361499727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21814863863155225189330421 2045143487170802361499727)
      ·
        refine ⟨3067715230756203542249591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045143487170802361499727 3067715230756203542249591)
        ·
          refine ⟨4601572846134305313374387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067715230756203542249591 4601572846134305313374387)
          ·
            refine ⟨6902359269201457970061581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601572846134305313374387 6902359269201457970061581)
            ·
              refine ⟨2588384725950546738773093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6902359269201457970061581 2588384725950546738773093)
              ·
                refine ⟨485322136115727513519955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2588384725950546738773093 485322136115727513519955)
                ·
                  refine ⟨727983204173591270279933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485322136115727513519955 727983204173591270279933)
                  ·
                    refine ⟨272993701565096726354975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 727983204173591270279933 272993701565096726354975)
                    ·
                      rfl

theorem cell22_797480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_797480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797480 prefixEnd_797480 := by exact prefixLift 797480
  have htrace : WordTrace (prefixWord ++ tailWord_797480) baseStart_797480 baseEnd_797480 := by
    simpa [prefixWord, tailWord_797480, baseEnd_797480] using wordTrace_append hprefix tailTrace_797480
  have hstable : (prefixWord ++ tailWord_797480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797480).length < 2 ^ (prefixWord ++ tailWord_797480).sum := by decide
  have hdescent : baseEnd_797480 < baseStart_797480 := by decide
  rcases family_descends (prefixWord ++ tailWord_797480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797491 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 2, 5]
def baseStart_797491 : Nat := 118140960795 + 797491 * 2 ^ 59
def prefixEnd_797491 : Nat := 4983230072969 + 3 ^ 40 * 797491 * 2
def baseEnd_797491 : Nat := 272997467089896364329941

theorem tailTrace_797491 : CollatzResearch.WordTrace tailWord_797491 prefixEnd_797491 272997467089896364329941 := by
  unfold tailWord_797491
  simp only [CollatzResearch.WordTrace]
  refine ⟨29086886353833782464424327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19391257569222521642949551 29086886353833782464424327)
  ·
    refine ⟨43630329530750673696636491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29086886353833782464424327 43630329530750673696636491)
    ·
      refine ⟨65445494296126010544954737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43630329530750673696636491 65445494296126010544954737)
      ·
        refine ⟨49084120722094507908716053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65445494296126010544954737 49084120722094507908716053)
        ·
          refine ⟨2300818158848180058221065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49084120722094507908716053 2300818158848180058221065)
          ·
            refine ⟨1725613619136135043665799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300818158848180058221065 1725613619136135043665799)
            ·
              refine ⟨2588420428704202565498699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725613619136135043665799 2588420428704202565498699)
              ·
                refine ⟨3882630643056303848248049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588420428704202565498699 3882630643056303848248049)
                ·
                  refine ⟨2911972982292227886186037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882630643056303848248049 2911972982292227886186037)
                  ·
                    refine ⟨272997467089896364329941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2911972982292227886186037 272997467089896364329941)
                    ·
                      rfl

theorem cell22_797491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_797491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797491 prefixEnd_797491 := by exact prefixLift 797491
  have htrace : WordTrace (prefixWord ++ tailWord_797491) baseStart_797491 baseEnd_797491 := by
    simpa [prefixWord, tailWord_797491, baseEnd_797491] using wordTrace_append hprefix tailTrace_797491
  have hstable : (prefixWord ++ tailWord_797491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797491).length < 2 ^ (prefixWord ++ tailWord_797491).sum := by decide
  have hdescent : baseEnd_797491 < baseStart_797491 := by decide
  rcases family_descends (prefixWord ++ tailWord_797491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797553 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 1, 5]
def baseStart_797553 : Nat := 118140960795 + 797553 * 2 ^ 59
def prefixEnd_797553 : Nat := 4983230072969 + 3 ^ 40 * 797553 * 2
def baseEnd_797553 : Nat := 273018690956948869279751

theorem tailTrace_797553 : CollatzResearch.WordTrace tailWord_797553 prefixEnd_797553 273018690956948869279751 := by
  unfold tailWord_797553
  simp only [CollatzResearch.WordTrace]
  refine ⟨29089147679609167053181313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19392765119739444702120875 29089147679609167053181313)
  ·
    refine ⟨21816860759706875289885985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29089147679609167053181313 21816860759706875289885985)
    ·
      refine ⟨16362645569780156467414489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21816860759706875289885985 16362645569780156467414489)
      ·
        refine ⟨12271984177335117350560867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16362645569780156467414489 12271984177335117350560867)
        ·
          refine ⟨18407976266002676025841301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12271984177335117350560867 18407976266002676025841301)
          ·
            refine ⟨862873887468875438711311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18407976266002676025841301 862873887468875438711311)
            ·
              refine ⟨1294310831203313158066967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862873887468875438711311 1294310831203313158066967)
              ·
                refine ⟨1941466246804969737100451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294310831203313158066967 1941466246804969737100451)
                ·
                  refine ⟨2912199370207454605650677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941466246804969737100451 2912199370207454605650677)
                  ·
                    refine ⟨273018690956948869279751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2912199370207454605650677 273018690956948869279751)
                    ·
                      rfl

theorem cell22_797553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 5].length) (baseStart_797553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797553 prefixEnd_797553 := by exact prefixLift 797553
  have htrace : WordTrace (prefixWord ++ tailWord_797553) baseStart_797553 baseEnd_797553 := by
    simpa [prefixWord, tailWord_797553, baseEnd_797553] using wordTrace_append hprefix tailTrace_797553
  have hstable : (prefixWord ++ tailWord_797553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797553).length < 2 ^ (prefixWord ++ tailWord_797553).sum := by decide
  have hdescent : baseEnd_797553 < baseStart_797553 := by decide
  rcases family_descends (prefixWord ++ tailWord_797553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797611 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 5]
def baseStart_797611 : Nat := 118140960795 + 797611 * 2 ^ 59
def prefixEnd_797611 : Nat := 4983230072969 + 3 ^ 40 * 797611 * 2
def baseEnd_797611 : Nat := 91012848514085350443191

theorem tailTrace_797611 : CollatzResearch.WordTrace tailWord_797611 prefixEnd_797611 91012848514085350443191 := by
  unfold tailWord_797611
  simp only [CollatzResearch.WordTrace]
  refine ⟨29091263113399042958792687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19394175408932695305861791 29091263113399042958792687)
  ·
    refine ⟨43636894670098564438189031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29091263113399042958792687 43636894670098564438189031)
    ·
      refine ⟨65455342005147846657283547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43636894670098564438189031 65455342005147846657283547)
      ·
        refine ⟨98183013007721769985925321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65455342005147846657283547 98183013007721769985925321)
        ·
          refine ⟨73637259755791327489443991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98183013007721769985925321 73637259755791327489443991)
          ·
            refine ⟨110455889633686991234165987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73637259755791327489443991 110455889633686991234165987)
            ·
              refine ⟨165683834450530486851248981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110455889633686991234165987 165683834450530486851248981)
              ·
                refine ⟨970803717483577071394037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 165683834450530486851248981 970803717483577071394037)
                ·
                  refine ⟨91012848514085350443191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 970803717483577071394037 91012848514085350443191)
                  ·
                    rfl

theorem cell22_797611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 5].length) (baseStart_797611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797611 prefixEnd_797611 := by exact prefixLift 797611
  have htrace : WordTrace (prefixWord ++ tailWord_797611) baseStart_797611 baseEnd_797611 := by
    simpa [prefixWord, tailWord_797611, baseEnd_797611] using wordTrace_append hprefix tailTrace_797611
  have hstable : (prefixWord ++ tailWord_797611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797611).length < 2 ^ (prefixWord ++ tailWord_797611).sum := by decide
  have hdescent : baseEnd_797611 < baseStart_797611 := by decide
  rcases family_descends (prefixWord ++ tailWord_797611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797638 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_797638 : Nat := 118140960795 + 797638 * 2 ^ 59
def prefixEnd_797638 : Nat := 4983230072969 + 3 ^ 40 * 797638 * 2
def baseEnd_797638 : Nat := 273047788194036980904491

theorem tailTrace_797638 : CollatzResearch.WordTrace tailWord_797638 prefixEnd_797638 273047788194036980904491 := by
  unfold tailWord_797638
  simp only [CollatzResearch.WordTrace]
  refine ⟨909132746384413330313299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19394831922867484380017045 909132746384413330313299)
  ·
    refine ⟨1363699119576619995469949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 909132746384413330313299 1363699119576619995469949)
    ·
      refine ⟨511387169841232498301231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1363699119576619995469949 511387169841232498301231)
      ·
        refine ⟨767080754761848747451847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511387169841232498301231 767080754761848747451847)
        ·
          refine ⟨1150621132142773121177771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767080754761848747451847 1150621132142773121177771)
          ·
            refine ⟨1725931698214159681766657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150621132142773121177771 1725931698214159681766657)
            ·
              refine ⟨1294448773660619761324993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1725931698214159681766657 1294448773660619761324993)
              ·
                refine ⟨970836580245464820993745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294448773660619761324993 970836580245464820993745)
                ·
                  refine ⟨728127435184098615745309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 970836580245464820993745 728127435184098615745309)
                  ·
                    refine ⟨273047788194036980904491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728127435184098615745309 273047788194036980904491)
                    ·
                      rfl

theorem cell22_797638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_797638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797638 prefixEnd_797638 := by exact prefixLift 797638
  have htrace : WordTrace (prefixWord ++ tailWord_797638) baseStart_797638 baseEnd_797638 := by
    simpa [prefixWord, tailWord_797638, baseEnd_797638] using wordTrace_append hprefix tailTrace_797638
  have hstable : (prefixWord ++ tailWord_797638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797638).length < 2 ^ (prefixWord ++ tailWord_797638).sum := by decide
  have hdescent : baseEnd_797638 < baseStart_797638 := by decide
  rcases family_descends (prefixWord ++ tailWord_797638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797641 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_797641 : Nat := 118140960795 + 797641 * 2 ^ 59
def prefixEnd_797641 : Nat := 4983230072969 + 3 ^ 40 * 797641 * 2
def baseEnd_797641 : Nat := 273048815155345973079481

theorem tailTrace_797641 : CollatzResearch.WordTrace tailWord_797641 prefixEnd_797641 273048815155345973079481 := by
  unfold tailWord_797641
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092357303290358082384777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19394904868860238721589851 29092357303290358082384777)
  ·
    refine ⟨21819267977467768561788583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29092357303290358082384777 21819267977467768561788583)
    ·
      refine ⟨32728901966201652842682875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21819267977467768561788583 32728901966201652842682875)
      ·
        refine ⟨49093352949302479264024313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32728901966201652842682875 49093352949302479264024313)
        ·
          refine ⟨36820014711976859448018235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49093352949302479264024313 36820014711976859448018235)
          ·
            refine ⟨55230022067965289172027353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36820014711976859448018235 55230022067965289172027353)
            ·
              refine ⟨41422516550973966879020515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55230022067965289172027353 41422516550973966879020515)
              ·
                refine ⟨62133774826460950318530773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41422516550973966879020515 62133774826460950318530773)
                ·
                  refine ⟨1456260347495178523090565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62133774826460950318530773 1456260347495178523090565)
                  ·
                    refine ⟨273048815155345973079481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1456260347495178523090565 273048815155345973079481)
                    ·
                      rfl

theorem cell22_797641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_797641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797641 prefixEnd_797641 := by exact prefixLift 797641
  have htrace : WordTrace (prefixWord ++ tailWord_797641) baseStart_797641 baseEnd_797641 := by
    simpa [prefixWord, tailWord_797641, baseEnd_797641] using wordTrace_append hprefix tailTrace_797641
  have hstable : (prefixWord ++ tailWord_797641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797641).length < 2 ^ (prefixWord ++ tailWord_797641).sum := by decide
  have hdescent : baseEnd_797641 < baseStart_797641 := by decide
  rcases family_descends (prefixWord ++ tailWord_797641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797658 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_797658 : Nat := 118140960795 + 797658 * 2 ^ 59
def prefixEnd_797658 : Nat := 4983230072969 + 3 ^ 40 * 797658 * 2
def baseEnd_797658 : Nat := 273054634602763595404429

theorem tailTrace_797658 : CollatzResearch.WordTrace tailWord_797658 prefixEnd_797658 273054634602763595404429 := by
  unfold tailWord_797658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273244336057192496438407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19395318229485846657169085 7273244336057192496438407)
  ·
    refine ⟨10909866504085788744657611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7273244336057192496438407 10909866504085788744657611)
    ·
      refine ⟨16364799756128683116986417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10909866504085788744657611 16364799756128683116986417)
      ·
        refine ⟨12273599817096512337739813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16364799756128683116986417 12273599817096512337739813)
        ·
          refine ⟨2301299965705596063326215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12273599817096512337739813 2301299965705596063326215)
          ·
            refine ⟨3451949948558394094989323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301299965705596063326215 3451949948558394094989323)
            ·
              refine ⟨5177924922837591142483985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451949948558394094989323 5177924922837591142483985)
              ·
                refine ⟨3883443692128193356862989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177924922837591142483985 3883443692128193356862989)
                ·
                  refine ⟨1456291384548072508823621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3883443692128193356862989 1456291384548072508823621)
                  ·
                    refine ⟨273054634602763595404429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1456291384548072508823621 273054634602763595404429)
                    ·
                      rfl

theorem cell22_797658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_797658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797658 prefixEnd_797658 := by exact prefixLift 797658
  have htrace : WordTrace (prefixWord ++ tailWord_797658) baseStart_797658 baseEnd_797658 := by
    simpa [prefixWord, tailWord_797658, baseEnd_797658] using wordTrace_append hprefix tailTrace_797658
  have hstable : (prefixWord ++ tailWord_797658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797658).length < 2 ^ (prefixWord ++ tailWord_797658).sum := by decide
  have hdescent : baseEnd_797658 < baseStart_797658 := by decide
  rcases family_descends (prefixWord ++ tailWord_797658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797688 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 4, 3]
def baseStart_797688 : Nat := 118140960795 + 797688 * 2 ^ 59
def prefixEnd_797688 : Nat := 4983230072969 + 3 ^ 40 * 797688 * 2
def baseEnd_797688 : Nat := 273064904215853517154337

theorem tailTrace_797688 : CollatzResearch.WordTrace tailWord_797688 prefixEnd_797688 273064904215853517154337 := by
  unfold tailWord_797688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14547035767060042554672859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19396047689413390072897145 14547035767060042554672859)
  ·
    refine ⟨21820553650590063832009289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14547035767060042554672859 21820553650590063832009289)
    ·
      refine ⟨16365415237942547874006967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21820553650590063832009289 16365415237942547874006967)
      ·
        refine ⟨24548122856913821811010451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16365415237942547874006967 24548122856913821811010451)
        ·
          refine ⟨36822184285370732716515677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24548122856913821811010451 36822184285370732716515677)
          ·
            refine ⟨13808319107014024768693379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36822184285370732716515677 13808319107014024768693379)
            ·
              refine ⟨20712478660521037153040069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13808319107014024768693379 20712478660521037153040069)
              ·
                refine ⟨3883589748847694466195013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20712478660521037153040069 3883589748847694466195013)
                ·
                  refine ⟨728173077908942712411565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3883589748847694466195013 728173077908942712411565)
                  ·
                    refine ⟨273064904215853517154337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728173077908942712411565 273064904215853517154337)
                    ·
                      rfl

theorem cell22_797688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_797688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797688 prefixEnd_797688 := by exact prefixLift 797688
  have htrace : WordTrace (prefixWord ++ tailWord_797688) baseStart_797688 baseEnd_797688 := by
    simpa [prefixWord, tailWord_797688, baseEnd_797688] using wordTrace_append hprefix tailTrace_797688
  have hstable : (prefixWord ++ tailWord_797688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797688).length < 2 ^ (prefixWord ++ tailWord_797688).sum := by decide
  have hdescent : baseEnd_797688 < baseStart_797688 := by decide
  rcases family_descends (prefixWord ++ tailWord_797688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797692 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_797692 : Nat := 118140960795 + 797692 * 2 ^ 59
def prefixEnd_797692 : Nat := 4983230072969 + 3 ^ 40 * 797692 * 2
def baseEnd_797692 : Nat := 273066273497598840054325

theorem tailTrace_797692 : CollatzResearch.WordTrace tailWord_797692 prefixEnd_797692 273066273497598840054325 := by
  unfold tailWord_797692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14547108713052796896245665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19396144950737062528327553 14547108713052796896245665)
  ·
    refine ⟨10910331534789597672184249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14547108713052796896245665 10910331534789597672184249)
    ·
      refine ⟨8182748651092198254138187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10910331534789597672184249 8182748651092198254138187)
      ·
        refine ⟨12274122976638297381207281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182748651092198254138187 12274122976638297381207281)
        ·
          refine ⟨9205592232478723035905461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12274122976638297381207281 9205592232478723035905461)
          ·
            refine ⟨863024271794880284616137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9205592232478723035905461 863024271794880284616137)
            ·
              refine ⟨647268203846160213462103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863024271794880284616137 647268203846160213462103)
              ·
                refine ⟨970902305769240320193155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647268203846160213462103 970902305769240320193155)
                ·
                  refine ⟨1456353458653860480289733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 970902305769240320193155 1456353458653860480289733)
                  ·
                    refine ⟨273066273497598840054325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1456353458653860480289733 273066273497598840054325)
                    ·
                      rfl

theorem cell22_797692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_797692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797692 prefixEnd_797692 := by exact prefixLift 797692
  have htrace : WordTrace (prefixWord ++ tailWord_797692) baseStart_797692 baseEnd_797692 := by
    simpa [prefixWord, tailWord_797692, baseEnd_797692] using wordTrace_append hprefix tailTrace_797692
  have hstable : (prefixWord ++ tailWord_797692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797692).length < 2 ^ (prefixWord ++ tailWord_797692).sum := by decide
  have hdescent : baseEnd_797692 < baseStart_797692 := by decide
  rcases family_descends (prefixWord ++ tailWord_797692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797701 : List Nat := [1, 3, 1, 1, 2, 3, 11]
def baseStart_797701 : Nat := 118140960795 + 797701 * 2 ^ 59
def prefixEnd_797701 : Nat := 4983230072969 + 3 ^ 40 * 797701 * 2
def baseEnd_797701 : Nat := 10113679791908363577011

theorem tailTrace_797701 : CollatzResearch.WordTrace tailWord_797701 prefixEnd_797701 10113679791908363577011 := by
  unfold tailWord_797701
  simp only [CollatzResearch.WordTrace]
  refine ⟨29094545683072988329568957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19396363788715325553045971 29094545683072988329568957)
  ·
    refine ⟨10910454631152370623588359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29094545683072988329568957 10910454631152370623588359)
    ·
      refine ⟨16365681946728555935382539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10910454631152370623588359 16365681946728555935382539)
      ·
        refine ⟨24548522920092833903073809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16365681946728555935382539 24548522920092833903073809)
        ·
          refine ⟨18411392190069625427305357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24548522920092833903073809 18411392190069625427305357)
          ·
            refine ⟨6904272071276109535239509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18411392190069625427305357 6904272071276109535239509)
            ·
              refine ⟨10113679791908363577011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6904272071276109535239509 10113679791908363577011)
              ·
                rfl

theorem cell22_797701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 11].length) (baseStart_797701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797701 prefixEnd_797701 := by exact prefixLift 797701
  have htrace : WordTrace (prefixWord ++ tailWord_797701) baseStart_797701 baseEnd_797701 := by
    simpa [prefixWord, tailWord_797701, baseEnd_797701] using wordTrace_append hprefix tailTrace_797701
  have hstable : (prefixWord ++ tailWord_797701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797701).length < 2 ^ (prefixWord ++ tailWord_797701).sum := by decide
  have hdescent : baseEnd_797701 < baseStart_797701 := by decide
  rcases family_descends (prefixWord ++ tailWord_797701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797703 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 4, 4]
def baseStart_797703 : Nat := 118140960795 + 797703 * 2 ^ 59
def prefixEnd_797703 : Nat := 4983230072969 + 3 ^ 40 * 797703 * 2
def baseEnd_797703 : Nat := 273070039022398478029291

theorem tailTrace_797703 : CollatzResearch.WordTrace tailWord_797703 prefixEnd_797703 273070039022398478029291 := by
  unfold tailWord_797703
  simp only [CollatzResearch.WordTrace]
  refine ⟨29094618629065742671141763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19396412419377161780761175 29094618629065742671141763)
  ·
    refine ⟨43641927943598614006712645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29094618629065742671141763 43641927943598614006712645)
    ·
      refine ⟨8182861489424740126258621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43641927943598614006712645 8182861489424740126258621)
      ·
        refine ⟨3068573058534277547346983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8182861489424740126258621 3068573058534277547346983)
        ·
          refine ⟨4602859587801416321020475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3068573058534277547346983 4602859587801416321020475)
          ·
            refine ⟨6904289381702124481530713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602859587801416321020475 6904289381702124481530713)
            ·
              refine ⟨5178217036276593361148035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904289381702124481530713 5178217036276593361148035)
              ·
                refine ⟨7767325554414890041722053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178217036276593361148035 7767325554414890041722053)
                ·
                  refine ⟨1456373541452791882822885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7767325554414890041722053 1456373541452791882822885)
                  ·
                    refine ⟨273070039022398478029291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1456373541452791882822885 273070039022398478029291)
                    ·
                      rfl

theorem cell22_797703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_797703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797703 prefixEnd_797703 := by exact prefixLift 797703
  have htrace : WordTrace (prefixWord ++ tailWord_797703) baseStart_797703 baseEnd_797703 := by
    simpa [prefixWord, tailWord_797703, baseEnd_797703] using wordTrace_append hprefix tailTrace_797703
  have hstable : (prefixWord ++ tailWord_797703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797703).length < 2 ^ (prefixWord ++ tailWord_797703).sum := by decide
  have hdescent : baseEnd_797703 < baseStart_797703 := by decide
  rcases family_descends (prefixWord ++ tailWord_797703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797722 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_797722 : Nat := 118140960795 + 797722 * 2 ^ 59
def prefixEnd_797722 : Nat := 4983230072969 + 3 ^ 40 * 797722 * 2
def baseEnd_797722 : Nat := 273076543110688761804233

theorem tailTrace_797722 : CollatzResearch.WordTrace tailWord_797722 prefixEnd_797722 273076543110688761804233 := by
  unfold tailWord_797722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273827903999227229020855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19396874410664605944055613 7273827903999227229020855)
  ·
    refine ⟨10910741855998840843531283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7273827903999227229020855 10910741855998840843531283)
    ·
      refine ⟨16366112783998261265296925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10910741855998840843531283 16366112783998261265296925)
      ·
        refine ⟨6137292293999347974486347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16366112783998261265296925 6137292293999347974486347)
        ·
          refine ⟨9205938440999021961729521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137292293999347974486347 9205938440999021961729521)
          ·
            refine ⟨6904453830749266471297141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9205938440999021961729521 6904453830749266471297141)
            ·
              refine ⟨647292546632743731684107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6904453830749266471297141 647292546632743731684107)
              ·
                refine ⟨970938819949115597526161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647292546632743731684107 970938819949115597526161)
                ·
                  refine ⟨728204114961836698144621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 970938819949115597526161 728204114961836698144621)
                  ·
                    refine ⟨273076543110688761804233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728204114961836698144621 273076543110688761804233)
                    ·
                      rfl

theorem cell22_797722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_797722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797722 prefixEnd_797722 := by exact prefixLift 797722
  have htrace : WordTrace (prefixWord ++ tailWord_797722) baseStart_797722 baseEnd_797722 := by
    simpa [prefixWord, tailWord_797722, baseEnd_797722] using wordTrace_append hprefix tailTrace_797722
  have hstable : (prefixWord ++ tailWord_797722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797722).length < 2 ^ (prefixWord ++ tailWord_797722).sum := by decide
  have hdescent : baseEnd_797722 < baseStart_797722 := by decide
  rcases family_descends (prefixWord ++ tailWord_797722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797735 : List Nat := [1, 1, 7, 1, 1, 2, 1, 8]
def baseStart_797735 : Nat := 118140960795 + 797735 * 2 ^ 59
def prefixEnd_797735 : Nat := 4983230072969 + 3 ^ 40 * 797735 * 2
def baseEnd_797735 : Nat := 30342332586262340136577

theorem tailTrace_797735 : CollatzResearch.WordTrace tailWord_797735 prefixEnd_797735 30342332586262340136577 := by
  unfold tailWord_797735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29095785764949812136306659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19397190509966541424204439 29095785764949812136306659)
  ·
    refine ⟨43643678647424718204459989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29095785764949812136306659 43643678647424718204459989)
    ·
      refine ⟨1022898718299016832917031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43643678647424718204459989 1022898718299016832917031)
      ·
        refine ⟨1534348077448525249375547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022898718299016832917031 1534348077448525249375547)
        ·
          refine ⟨2301522116172787874063321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534348077448525249375547 2301522116172787874063321)
          ·
            refine ⟨1726141587129590905547491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301522116172787874063321 1726141587129590905547491)
            ·
              refine ⟨2589212380694386358321237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1726141587129590905547491 2589212380694386358321237)
              ·
                refine ⟨30342332586262340136577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2589212380694386358321237 30342332586262340136577)
                ·
                  rfl

theorem cell22_797735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 8].length) (baseStart_797735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797735 prefixEnd_797735 := by exact prefixLift 797735
  have htrace : WordTrace (prefixWord ++ tailWord_797735) baseStart_797735 baseEnd_797735 := by
    simpa [prefixWord, tailWord_797735, baseEnd_797735] using wordTrace_append hprefix tailTrace_797735
  have hstable : (prefixWord ++ tailWord_797735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797735).length < 2 ^ (prefixWord ++ tailWord_797735).sum := by decide
  have hdescent : baseEnd_797735 < baseStart_797735 := by decide
  rcases family_descends (prefixWord ++ tailWord_797735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797763 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 5]
def baseStart_797763 : Nat := 118140960795 + 797763 * 2 ^ 59
def prefixEnd_797763 : Nat := 4983230072969 + 3 ^ 40 * 797763 * 2
def baseEnd_797763 : Nat := 91030192749526107176369

theorem tailTrace_797763 : CollatzResearch.WordTrace tailWord_797763 prefixEnd_797763 91030192749526107176369 := by
  unfold tailWord_797763
  simp only [CollatzResearch.WordTrace]
  refine ⟨29096807008848372918325943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19397871339232248612217295 29096807008848372918325943)
  ·
    refine ⟨43645210513272559377488915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29096807008848372918325943 43645210513272559377488915)
    ·
      refine ⟨65467815769908839066233373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43645210513272559377488915 65467815769908839066233373)
      ·
        refine ⟨24550430913715814649837515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65467815769908839066233373 24550430913715814649837515)
        ·
          refine ⟨36825646370573721974756273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24550430913715814649837515 36825646370573721974756273)
          ·
            refine ⟨27619234777930291481067205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36825646370573721974756273 27619234777930291481067205)
            ·
              refine ⟨5178606520861929652700101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27619234777930291481067205 5178606520861929652700101)
              ·
                refine ⟨970988722661611809881269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5178606520861929652700101 970988722661611809881269)
                ·
                  refine ⟨91030192749526107176369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 970988722661611809881269 91030192749526107176369)
                  ·
                    rfl

theorem cell22_797763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 5].length) (baseStart_797763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797763 prefixEnd_797763 := by exact prefixLift 797763
  have htrace : WordTrace (prefixWord ++ tailWord_797763) baseStart_797763 baseEnd_797763 := by
    simpa [prefixWord, tailWord_797763, baseEnd_797763] using wordTrace_append hprefix tailTrace_797763
  have hstable : (prefixWord ++ tailWord_797763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797763).length < 2 ^ (prefixWord ++ tailWord_797763).sum := by decide
  have hdescent : baseEnd_797763 < baseStart_797763 := by decide
  rcases family_descends (prefixWord ++ tailWord_797763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797767 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 3, 3]
def baseStart_797767 : Nat := 118140960795 + 797767 * 2 ^ 59
def prefixEnd_797767 : Nat := 4983230072969 + 3 ^ 40 * 797767 * 2
def baseEnd_797767 : Nat := 273091947530323644429095

theorem tailTrace_797767 : CollatzResearch.WordTrace tailWord_797767 prefixEnd_797767 273091947530323644429095 := by
  unfold tailWord_797767
  simp only [CollatzResearch.WordTrace]
  refine ⟨29096952900833881601471555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19397968600555921067647703 29096952900833881601471555)
  ·
    refine ⟨43645429351250822402207333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29096952900833881601471555 43645429351250822402207333)
    ·
      refine ⟨8183518003359529200413875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43645429351250822402207333 8183518003359529200413875)
      ·
        refine ⟨12275277005039293800620813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8183518003359529200413875 12275277005039293800620813)
        ·
          refine ⟨4603228876889735175232805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12275277005039293800620813 4603228876889735175232805)
          ·
            refine ⟨863105414416825345356151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4603228876889735175232805 863105414416825345356151)
            ·
              refine ⟨1294658121625238018034227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863105414416825345356151 1294658121625238018034227)
              ·
                refine ⟨1941987182437857027051341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294658121625238018034227 1941987182437857027051341)
                ·
                  refine ⟨728245193414196385144253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1941987182437857027051341 728245193414196385144253)
                  ·
                    refine ⟨273091947530323644429095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728245193414196385144253 273091947530323644429095)
                    ·
                      rfl

theorem cell22_797767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_797767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797767 prefixEnd_797767 := by exact prefixLift 797767
  have htrace : WordTrace (prefixWord ++ tailWord_797767) baseStart_797767 baseEnd_797767 := by
    simpa [prefixWord, tailWord_797767, baseEnd_797767] using wordTrace_append hprefix tailTrace_797767
  have hstable : (prefixWord ++ tailWord_797767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797767).length < 2 ^ (prefixWord ++ tailWord_797767).sum := by decide
  have hdescent : baseEnd_797767 < baseStart_797767 := by decide
  rcases family_descends (prefixWord ++ tailWord_797767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797874 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_797874 : Nat := 118140960795 + 797874 * 2 ^ 59
def prefixEnd_797874 : Nat := 4983230072969 + 3 ^ 40 * 797874 * 2
def baseEnd_797874 : Nat := 273128575817011032003767

theorem tailTrace_797874 : CollatzResearch.WordTrace tailWord_797874 prefixEnd_797874 273128575817011032003767 := by
  unfold tailWord_797874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7275213877861559718904169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19400570340964159250411117 7275213877861559718904169)
  ·
    refine ⟨5456410408396169789178127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7275213877861559718904169 5456410408396169789178127)
    ·
      refine ⟨8184615612594254683767191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5456410408396169789178127 8184615612594254683767191)
      ·
        refine ⟨12276923418891382025650787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8184615612594254683767191 12276923418891382025650787)
        ·
          refine ⟨18415385128337073038476181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12276923418891382025650787 18415385128337073038476181)
          ·
            refine ⟨863221177890800298678571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18415385128337073038476181 863221177890800298678571)
            ·
              refine ⟨1294831766836200448017857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863221177890800298678571 1294831766836200448017857)
              ·
                refine ⟨971123825127150336013393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1294831766836200448017857 971123825127150336013393)
                ·
                  refine ⟨728342868845362752010045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971123825127150336013393 728342868845362752010045)
                  ·
                    refine ⟨273128575817011032003767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728342868845362752010045 273128575817011032003767)
                    ·
                      rfl

theorem cell22_797874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_797874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797874 prefixEnd_797874 := by exact prefixLift 797874
  have htrace : WordTrace (prefixWord ++ tailWord_797874) baseStart_797874 baseEnd_797874 := by
    simpa [prefixWord, tailWord_797874, baseEnd_797874] using wordTrace_append hprefix tailTrace_797874
  have hstable : (prefixWord ++ tailWord_797874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797874).length < 2 ^ (prefixWord ++ tailWord_797874).sum := by decide
  have hdescent : baseEnd_797874 < baseStart_797874 := by decide
  rcases family_descends (prefixWord ++ tailWord_797874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797883 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_797883 : Nat := 118140960795 + 797883 * 2 ^ 59
def prefixEnd_797883 : Nat := 4983230072969 + 3 ^ 40 * 797883 * 2
def baseEnd_797883 : Nat := 273131656700938008528739

theorem tailTrace_797883 : CollatzResearch.WordTrace tailWord_797883 prefixEnd_797883 273131656700938008528739 := by
  unfold tailWord_797883
  simp only [CollatzResearch.WordTrace]
  refine ⟨29101183768413633412694303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19400789178942422275129535 29101183768413633412694303)
  ·
    refine ⟨43651775652620450119041455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29101183768413633412694303 43651775652620450119041455)
    ·
      refine ⟨65477663478930675178562183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43651775652620450119041455 65477663478930675178562183)
      ·
        refine ⟨98216495218396012767843275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65477663478930675178562183 98216495218396012767843275)
        ·
          refine ⟨147324742827594019151764913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98216495218396012767843275 147324742827594019151764913)
          ·
            refine ⟨110493557120695514363823685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147324742827594019151764913 110493557120695514363823685)
            ·
              refine ⟨20717541960130408943216941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110493557120695514363823685 20717541960130408943216941)
              ·
                refine ⟨7769078235048903353706353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20717541960130408943216941 7769078235048903353706353)
                ·
                  refine ⟨5826808676286677515279765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7769078235048903353706353 5826808676286677515279765)
                  ·
                    refine ⟨273131656700938008528739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5826808676286677515279765 273131656700938008528739)
                    ·
                      rfl

theorem cell22_797883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_797883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797883 prefixEnd_797883 := by exact prefixLift 797883
  have htrace : WordTrace (prefixWord ++ tailWord_797883) baseStart_797883 baseEnd_797883 := by
    simpa [prefixWord, tailWord_797883, baseEnd_797883] using wordTrace_append hprefix tailTrace_797883
  have hstable : (prefixWord ++ tailWord_797883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797883).length < 2 ^ (prefixWord ++ tailWord_797883).sum := by decide
  have hdescent : baseEnd_797883 < baseStart_797883 := by decide
  rcases family_descends (prefixWord ++ tailWord_797883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797919 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 1, 3]
def baseStart_797919 : Nat := 118140960795 + 797919 * 2 ^ 59
def prefixEnd_797919 : Nat := 4983230072969 + 3 ^ 40 * 797919 * 2
def baseEnd_797919 : Nat := 273143980236645914628629

theorem tailTrace_797919 : CollatzResearch.WordTrace tailWord_797919 prefixEnd_797919 273143980236645914628629 := by
  unfold tailWord_797919
  simp only [CollatzResearch.WordTrace]
  refine ⟨29102496796283211561004811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19401664530855474374003207 29102496796283211561004811)
  ·
    refine ⟨43653745194424817341507217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29102496796283211561004811 43653745194424817341507217)
    ·
      refine ⟨32740308895818613006130413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43653745194424817341507217 32740308895818613006130413)
      ·
        refine ⟨12277615835931979877298905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32740308895818613006130413 12277615835931979877298905)
        ·
          refine ⟨9208211876948984907974179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12277615835931979877298905 9208211876948984907974179)
          ·
            refine ⟨13812317815423477361961269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208211876948984907974179 13812317815423477361961269)
            ·
              refine ⟨1294904795195951002683869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13812317815423477361961269 1294904795195951002683869)
              ·
                refine ⟨485589298198481626006451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1294904795195951002683869 485589298198481626006451)
                ·
                  refine ⟨728383947297722439009677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485589298198481626006451 728383947297722439009677)
                  ·
                    refine ⟨273143980236645914628629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728383947297722439009677 273143980236645914628629)
                    ·
                      rfl

theorem cell22_797919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_797919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797919 prefixEnd_797919 := by exact prefixLift 797919
  have htrace : WordTrace (prefixWord ++ tailWord_797919) baseStart_797919 baseEnd_797919 := by
    simpa [prefixWord, tailWord_797919, baseEnd_797919] using wordTrace_append hprefix tailTrace_797919
  have hstable : (prefixWord ++ tailWord_797919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797919).length < 2 ^ (prefixWord ++ tailWord_797919).sum := by decide
  have hdescent : baseEnd_797919 < baseStart_797919 := by decide
  rcases family_descends (prefixWord ++ tailWord_797919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797945 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_797945 : Nat := 118140960795 + 797945 * 2 ^ 59
def prefixEnd_797945 : Nat := 4983230072969 + 3 ^ 40 * 797945 * 2
def baseEnd_797945 : Nat := 273152880567990513478549

theorem tailTrace_797945 : CollatzResearch.WordTrace tailWord_797945 prefixEnd_797945 273152880567990513478549 := by
  unfold tailWord_797945
  simp only [CollatzResearch.WordTrace]
  refine ⟨29103445094189018001451289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19402296729459345334300859 29103445094189018001451289)
  ·
    refine ⟨21827583820641763501088467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29103445094189018001451289 21827583820641763501088467)
    ·
      refine ⟨32741375730962645251632701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21827583820641763501088467 32741375730962645251632701)
      ·
        refine ⟨12278015899110991969362263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32741375730962645251632701 12278015899110991969362263)
        ·
          refine ⟨18417023848666487954043395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12278015899110991969362263 18417023848666487954043395)
          ·
            refine ⟨27625535772999731931065093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18417023848666487954043395 27625535772999731931065093)
            ·
              refine ⟨5179787957437449737074705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27625535772999731931065093 5179787957437449737074705)
              ·
                refine ⟨3884840968078087302806029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5179787957437449737074705 3884840968078087302806029)
                ·
                  refine ⟨1456815363029282738552261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3884840968078087302806029 1456815363029282738552261)
                  ·
                    refine ⟨273152880567990513478549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1456815363029282738552261 273152880567990513478549)
                    ·
                      rfl

theorem cell22_797945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_797945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_797945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_797945 prefixEnd_797945 := by exact prefixLift 797945
  have htrace : WordTrace (prefixWord ++ tailWord_797945) baseStart_797945 baseEnd_797945 := by
    simpa [prefixWord, tailWord_797945, baseEnd_797945] using wordTrace_append hprefix tailTrace_797945
  have hstable : (prefixWord ++ tailWord_797945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797945).length < 2 ^ (prefixWord ++ tailWord_797945).sum := by decide
  have hdescent : baseEnd_797945 < baseStart_797945 := by decide
  rcases family_descends (prefixWord ++ tailWord_797945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798009 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_798009 : Nat := 118140960795 + 798009 * 2 ^ 59
def prefixEnd_798009 : Nat := 4983230072969 + 3 ^ 40 * 798009 * 2
def baseEnd_798009 : Nat := 273174789075915679878353

theorem tailTrace_798009 : CollatzResearch.WordTrace tailWord_798009 prefixEnd_798009 273174789075915679878353 := by
  unfold tailWord_798009
  simp only [CollatzResearch.WordTrace]
  refine ⟨29105779365957156931781081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19403852910638104621187387 29105779365957156931781081)
  ·
    refine ⟨21829334524467867698835811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29105779365957156931781081 21829334524467867698835811)
    ·
      refine ⟨32744001786701801548253717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21829334524467867698835811 32744001786701801548253717)
      ·
        refine ⟨1534875083751646947574393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32744001786701801548253717 1534875083751646947574393)
        ·
          refine ⟨1151156312813735210680795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534875083751646947574393 1151156312813735210680795)
          ·
            refine ⟨1726734469220602816021193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151156312813735210680795 1726734469220602816021193)
            ·
              refine ⟨1295050851915452112015895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726734469220602816021193 1295050851915452112015895)
              ·
                refine ⟨1942576277873178168023843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295050851915452112015895 1942576277873178168023843)
                ·
                  refine ⟨2913864416809767252035765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942576277873178168023843 2913864416809767252035765)
                  ·
                    refine ⟨273174789075915679878353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2913864416809767252035765 273174789075915679878353)
                    ·
                      rfl

theorem cell22_798009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_798009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798009 prefixEnd_798009 := by exact prefixLift 798009
  have htrace : WordTrace (prefixWord ++ tailWord_798009) baseStart_798009 baseEnd_798009 := by
    simpa [prefixWord, tailWord_798009, baseEnd_798009] using wordTrace_append hprefix tailTrace_798009
  have hstable : (prefixWord ++ tailWord_798009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798009).length < 2 ^ (prefixWord ++ tailWord_798009).sum := by decide
  have hdescent : baseEnd_798009 < baseStart_798009 := by decide
  rcases family_descends (prefixWord ++ tailWord_798009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798080 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 8]
def baseStart_798080 : Nat := 118140960795 + 798080 * 2 ^ 59
def prefixEnd_798080 : Nat := 4983230072969 + 3 ^ 40 * 798080 * 2
def baseEnd_798080 : Nat := 273199093826895161353135

theorem tailTrace_798080 : CollatzResearch.WordTrace tailWord_798080 prefixEnd_798080 273199093826895161353135 := by
  unfold tailWord_798080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554184474349968028807847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19405579299133290705077129 14554184474349968028807847)
  ·
    refine ⟨21831276711524952043211771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14554184474349968028807847 21831276711524952043211771)
    ·
      refine ⟨32746915067287428064817657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21831276711524952043211771 32746915067287428064817657)
      ·
        refine ⟨24560186300465571048613243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32746915067287428064817657 24560186300465571048613243)
        ·
          refine ⟨36840279450698356572919865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24560186300465571048613243 36840279450698356572919865)
          ·
            refine ⟨27630209588023767429689899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36840279450698356572919865 27630209588023767429689899)
            ·
              refine ⟨41445314382035651144534849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27630209588023767429689899 41445314382035651144534849)
              ·
                refine ⟨31083985786526738358401137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41445314382035651144534849 31083985786526738358401137)
                ·
                  refine ⟨23312989339895053768800853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31083985786526738358401137 23312989339895053768800853)
                  ·
                    refine ⟨273199093826895161353135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23312989339895053768800853 273199093826895161353135)
                    ·
                      rfl

theorem cell22_798080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_798080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798080 prefixEnd_798080 := by exact prefixLift 798080
  have htrace : WordTrace (prefixWord ++ tailWord_798080) baseStart_798080 baseEnd_798080 := by
    simpa [prefixWord, tailWord_798080, baseEnd_798080] using wordTrace_append hprefix tailTrace_798080
  have hstable : (prefixWord ++ tailWord_798080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798080).length < 2 ^ (prefixWord ++ tailWord_798080).sum := by decide
  have hdescent : baseEnd_798080 < baseStart_798080 := by decide
  rcases family_descends (prefixWord ++ tailWord_798080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798088 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 1, 3]
def baseStart_798088 : Nat := 118140960795 + 798088 * 2 ^ 59
def prefixEnd_798088 : Nat := 4983230072969 + 3 ^ 40 * 798088 * 2
def baseEnd_798088 : Nat := 273201832390385807153111

theorem tailTrace_798088 : CollatzResearch.WordTrace tailWord_798088 prefixEnd_798088 273201832390385807153111 := by
  unfold tailWord_798088
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554330366335476711953459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19405773821780635615937945 14554330366335476711953459)
  ·
    refine ⟨21831495549503215067930189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14554330366335476711953459 21831495549503215067930189)
    ·
      refine ⟨8186810831063705650473821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21831495549503215067930189 8186810831063705650473821)
      ·
        refine ⟨3070054061648889618927683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8186810831063705650473821 3070054061648889618927683)
        ·
          refine ⟨4605081092473334428391525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3070054061648889618927683 4605081092473334428391525)
          ·
            refine ⟨863452704838750205323411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4605081092473334428391525 863452704838750205323411)
            ·
              refine ⟨1295179057258125307985117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863452704838750205323411 1295179057258125307985117)
              ·
                refine ⟨485692146471796990494419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1295179057258125307985117 485692146471796990494419)
                ·
                  refine ⟨728538219707695485741629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 485692146471796990494419 728538219707695485741629)
                  ·
                    refine ⟨273201832390385807153111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728538219707695485741629 273201832390385807153111)
                    ·
                      rfl

theorem cell22_798088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_798088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798088 prefixEnd_798088 := by exact prefixLift 798088
  have htrace : WordTrace (prefixWord ++ tailWord_798088) baseStart_798088 baseEnd_798088 := by
    simpa [prefixWord, tailWord_798088, baseEnd_798088] using wordTrace_append hprefix tailTrace_798088
  have hstable : (prefixWord ++ tailWord_798088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798088).length < 2 ^ (prefixWord ++ tailWord_798088).sum := by decide
  have hdescent : baseEnd_798088 < baseStart_798088 := by decide
  rcases family_descends (prefixWord ++ tailWord_798088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798148 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_798148 : Nat := 118140960795 + 798148 * 2 ^ 59
def prefixEnd_798148 : Nat := 4983230072969 + 3 ^ 40 * 798148 * 2
def baseEnd_798148 : Nat := 273222371616565650652927

theorem tailTrace_798148 : CollatzResearch.WordTrace tailWord_798148 prefixEnd_798148 273222371616565650652927 := by
  unfold tailWord_798148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555424556226791835545549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19407232741635722447394065 14555424556226791835545549)
  ·
    refine ⟨5458284208585046938329581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14555424556226791835545549 5458284208585046938329581)
    ·
      refine ⟨2046856578219392601873593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5458284208585046938329581 2046856578219392601873593)
      ·
        refine ⟨1535142433664544451405195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2046856578219392601873593 1535142433664544451405195)
        ·
          refine ⟨2302713650496816677107793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535142433664544451405195 2302713650496816677107793)
          ·
            refine ⟨1727035237872612507830845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2302713650496816677107793 1727035237872612507830845)
            ·
              refine ⟨647638214202229690436567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1727035237872612507830845 647638214202229690436567)
              ·
                refine ⟨971457321303344535654851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647638214202229690436567 971457321303344535654851)
                ·
                  refine ⟨1457185981955016803482277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971457321303344535654851 1457185981955016803482277)
                  ·
                    refine ⟨273222371616565650652927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1457185981955016803482277 273222371616565650652927)
                    ·
                      rfl

theorem cell22_798148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_798148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798148 prefixEnd_798148 := by exact prefixLift 798148
  have htrace : WordTrace (prefixWord ++ tailWord_798148) baseStart_798148 baseEnd_798148 := by
    simpa [prefixWord, tailWord_798148, baseEnd_798148] using wordTrace_append hprefix tailTrace_798148
  have hstable : (prefixWord ++ tailWord_798148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798148).length < 2 ^ (prefixWord ++ tailWord_798148).sum := by decide
  have hdescent : baseEnd_798148 < baseStart_798148 := by decide
  rcases family_descends (prefixWord ++ tailWord_798148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798202 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_798202 : Nat := 118140960795 + 798202 * 2 ^ 59
def prefixEnd_798202 : Nat := 4983230072969 + 3 ^ 40 * 798202 * 2
def baseEnd_798202 : Nat := 91080285640042503267587

theorem tailTrace_798202 : CollatzResearch.WordTrace tailWord_798202 prefixEnd_798202 91080285640042503267587 := by
  unfold tailWord_798202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7278204663564487723389215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19408545769505300595704573 7278204663564487723389215)
  ·
    refine ⟨10917306995346731585083823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7278204663564487723389215 10917306995346731585083823)
    ·
      refine ⟨16375960493020097377625735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10917306995346731585083823 16375960493020097377625735)
      ·
        refine ⟨24563940739530146066438603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16375960493020097377625735 24563940739530146066438603)
        ·
          refine ⟨36845911109295219099657905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24563940739530146066438603 36845911109295219099657905)
          ·
            refine ⟨27634433331971414324743429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36845911109295219099657905 27634433331971414324743429)
            ·
              refine ⟨5181456249744640185889393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27634433331971414324743429 5181456249744640185889393)
              ·
                refine ⟨3886092187308480139417045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5181456249744640185889393 3886092187308480139417045)
                ·
                  refine ⟨91080285640042503267587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3886092187308480139417045 91080285640042503267587)
                  ·
                    rfl

theorem cell22_798202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_798202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798202 prefixEnd_798202 := by exact prefixLift 798202
  have htrace : WordTrace (prefixWord ++ tailWord_798202) baseStart_798202 baseEnd_798202 := by
    simpa [prefixWord, tailWord_798202, baseEnd_798202] using wordTrace_append hprefix tailTrace_798202
  have hstable : (prefixWord ++ tailWord_798202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798202).length < 2 ^ (prefixWord ++ tailWord_798202).sum := by decide
  have hdescent : baseEnd_798202 < baseStart_798202 := by decide
  rcases family_descends (prefixWord ++ tailWord_798202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798217 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_798217 : Nat := 118140960795 + 798217 * 2 ^ 59
def prefixEnd_798217 : Nat := 4983230072969 + 3 ^ 40 * 798217 * 2
def baseEnd_798217 : Nat := 273245991726672470677715

theorem tailTrace_798217 : CollatzResearch.WordTrace tailWord_798217 prefixEnd_798217 273245991726672470677715 := by
  unfold tailWord_798217
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113365749203608455352905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19408910499469072303568603 29113365749203608455352905)
  ·
    refine ⟨21835024311902706341514679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29113365749203608455352905 21835024311902706341514679)
    ·
      refine ⟨32752536467854059512272019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21835024311902706341514679 32752536467854059512272019)
      ·
        refine ⟨49128804701781089268408029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32752536467854059512272019 49128804701781089268408029)
        ·
          refine ⟨18423301763167908475653011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49128804701781089268408029 18423301763167908475653011)
          ·
            refine ⟨27634952644751862713479517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18423301763167908475653011 27634952644751862713479517)
            ·
              refine ⟨10363107241781948517554819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27634952644751862713479517 10363107241781948517554819)
              ·
                refine ⟨15544660862672922776332229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10363107241781948517554819 15544660862672922776332229)
                ·
                  refine ⟨2914623911751173020562293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15544660862672922776332229 2914623911751173020562293)
                  ·
                    refine ⟨273245991726672470677715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2914623911751173020562293 273245991726672470677715)
                    ·
                      rfl

theorem cell22_798217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_798217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798217 prefixEnd_798217 := by exact prefixLift 798217
  have htrace : WordTrace (prefixWord ++ tailWord_798217) baseStart_798217 baseEnd_798217 := by
    simpa [prefixWord, tailWord_798217, baseEnd_798217] using wordTrace_append hprefix tailTrace_798217
  have hstable : (prefixWord ++ tailWord_798217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798217).length < 2 ^ (prefixWord ++ tailWord_798217).sum := by decide
  have hdescent : baseEnd_798217 < baseStart_798217 := by decide
  rcases family_descends (prefixWord ++ tailWord_798217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798219 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 7]
def baseStart_798219 : Nat := 118140960795 + 798219 * 2 ^ 59
def prefixEnd_798219 : Nat := 4983230072969 + 3 ^ 40 * 798219 * 2
def baseEnd_798219 : Nat := 91082225455848377375903

theorem tailTrace_798219 : CollatzResearch.WordTrace tailWord_798219 prefixEnd_798219 91082225455848377375903 := by
  unfold tailWord_798219
  simp only [CollatzResearch.WordTrace]
  refine ⟨29113438695196362796925711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19408959130130908531283807 29113438695196362796925711)
  ·
    refine ⟨43670158042794544195388567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29113438695196362796925711 43670158042794544195388567)
    ·
      refine ⟨65505237064191816293082851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43670158042794544195388567 65505237064191816293082851)
      ·
        refine ⟨98257855596287724439624277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65505237064191816293082851 98257855596287724439624277)
        ·
          refine ⟨1151459245268996770776847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 98257855596287724439624277 1151459245268996770776847)
          ·
            refine ⟨1727188867903495156165271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151459245268996770776847 1727188867903495156165271)
            ·
              refine ⟨2590783301855242734247907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727188867903495156165271 2590783301855242734247907)
              ·
                refine ⟨3886174952782864101371861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590783301855242734247907 3886174952782864101371861)
                ·
                  refine ⟨91082225455848377375903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3886174952782864101371861 91082225455848377375903)
                  ·
                    rfl

theorem cell22_798219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 7].length) (baseStart_798219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798219 prefixEnd_798219 := by exact prefixLift 798219
  have htrace : WordTrace (prefixWord ++ tailWord_798219) baseStart_798219 baseEnd_798219 := by
    simpa [prefixWord, tailWord_798219, baseEnd_798219] using wordTrace_append hprefix tailTrace_798219
  have hstable : (prefixWord ++ tailWord_798219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798219).length < 2 ^ (prefixWord ++ tailWord_798219).sum := by decide
  have hdescent : baseEnd_798219 < baseStart_798219 := by decide
  rcases family_descends (prefixWord ++ tailWord_798219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798236 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 5]
def baseStart_798236 : Nat := 118140960795 + 798236 * 2 ^ 59
def prefixEnd_798236 : Nat := 4983230072969 + 3 ^ 40 * 798236 * 2
def baseEnd_798236 : Nat := 91084165271654251484219

theorem tailTrace_798236 : CollatzResearch.WordTrace tailWord_798236 prefixEnd_798236 91084165271654251484219 := by
  unfold tailWord_798236
  simp only [CollatzResearch.WordTrace]
  refine ⟨14557029368067387350147281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19409372490756516466863041 14557029368067387350147281)
  ·
    refine ⟨10917772026050540512610461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14557029368067387350147281 10917772026050540512610461)
    ·
      refine ⟨4094164509768952692228923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10917772026050540512610461 4094164509768952692228923)
      ·
        refine ⟨6141246764653429038343385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4094164509768952692228923 6141246764653429038343385)
        ·
          refine ⟨4605935073490071778757539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6141246764653429038343385 4605935073490071778757539)
          ·
            refine ⟨6908902610235107668136309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605935073490071778757539 6908902610235107668136309)
            ·
              refine ⟨647709619709541343887779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6908902610235107668136309 647709619709541343887779)
              ·
                refine ⟨971564429564312015831669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647709619709541343887779 971564429564312015831669)
                ·
                  refine ⟨91084165271654251484219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 971564429564312015831669 91084165271654251484219)
                  ·
                    rfl

theorem cell22_798236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_798236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798236 prefixEnd_798236 := by exact prefixLift 798236
  have htrace : WordTrace (prefixWord ++ tailWord_798236) baseStart_798236 baseEnd_798236 := by
    simpa [prefixWord, tailWord_798236, baseEnd_798236] using wordTrace_append hprefix tailTrace_798236
  have hstable : (prefixWord ++ tailWord_798236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798236).length < 2 ^ (prefixWord ++ tailWord_798236).sum := by decide
  have hdescent : baseEnd_798236 < baseStart_798236 := by decide
  rcases family_descends (prefixWord ++ tailWord_798236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798309 : List Nat := [1, 3, 1, 3, 3, 1, 2, 8]
def baseStart_798309 : Nat := 118140960795 + 798309 * 2 ^ 59
def prefixEnd_798309 : Nat := 4983230072969 + 3 ^ 40 * 798309 * 2
def baseEnd_798309 : Nat := 30364165022979433041937

theorem tailTrace_798309 : CollatzResearch.WordTrace tailWord_798309 prefixEnd_798309 30364165022979433041937 := by
  unfold tailWord_798309
  simp only [CollatzResearch.WordTrace]
  refine ⟨29116721264870308167701981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19411147509913538778467987 29116721264870308167701981)
  ·
    refine ⟨10918770474326365562888243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29116721264870308167701981 10918770474326365562888243)
    ·
      refine ⟨16378155711489548344332365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10918770474326365562888243 16378155711489548344332365)
      ·
        refine ⟨6141808391808580629124637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16378155711489548344332365 6141808391808580629124637)
        ·
          refine ⟨2303178146928217735921739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6141808391808580629124637 2303178146928217735921739)
          ·
            refine ⟨3454767220392326603882609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303178146928217735921739 3454767220392326603882609)
            ·
              refine ⟨2591075415294244952911957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3454767220392326603882609 2591075415294244952911957)
              ·
                refine ⟨30364165022979433041937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2591075415294244952911957 30364165022979433041937)
                ·
                  rfl

theorem cell22_798309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 8].length) (baseStart_798309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798309 prefixEnd_798309 := by exact prefixLift 798309
  have htrace : WordTrace (prefixWord ++ tailWord_798309) baseStart_798309 baseEnd_798309 := by
    simpa [prefixWord, tailWord_798309, baseEnd_798309] using wordTrace_append hprefix tailTrace_798309
  have hstable : (prefixWord ++ tailWord_798309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798309).length < 2 ^ (prefixWord ++ tailWord_798309).sum := by decide
  have hdescent : baseEnd_798309 < baseStart_798309 := by decide
  rcases family_descends (prefixWord ++ tailWord_798309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798341 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_798341 : Nat := 118140960795 + 798341 * 2 ^ 59
def prefixEnd_798341 : Nat := 4983230072969 + 3 ^ 40 * 798341 * 2
def baseEnd_798341 : Nat := 273288439460777480577335

theorem tailTrace_798341 : CollatzResearch.WordTrace tailWord_798341 prefixEnd_798341 273288439460777480577335 := by
  unfold tailWord_798341
  simp only [CollatzResearch.WordTrace]
  refine ⟨29117888400754377632866877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19411925600502918421911251 29117888400754377632866877)
  ·
    refine ⟨10919208150282891612325079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29117888400754377632866877 10919208150282891612325079)
    ·
      refine ⟨16378812225424337418487619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10919208150282891612325079 16378812225424337418487619)
      ·
        refine ⟨24568218338136506127731429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16378812225424337418487619 24568218338136506127731429)
        ·
          refine ⟨4606540938400594898949643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24568218338136506127731429 4606540938400594898949643)
          ·
            refine ⟨6909811407600892348424465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4606540938400594898949643 6909811407600892348424465)
            ·
              refine ⟨5182358555700669261318349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6909811407600892348424465 5182358555700669261318349)
              ·
                refine ⟨1943384458387750972994381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5182358555700669261318349 1943384458387750972994381)
                ·
                  refine ⟨728769171895406614872893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1943384458387750972994381 728769171895406614872893)
                  ·
                    refine ⟨273288439460777480577335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728769171895406614872893 273288439460777480577335)
                    ·
                      rfl

theorem cell22_798341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_798341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798341 prefixEnd_798341 := by exact prefixLift 798341
  have htrace : WordTrace (prefixWord ++ tailWord_798341) baseStart_798341 baseEnd_798341 := by
    simpa [prefixWord, tailWord_798341, baseEnd_798341] using wordTrace_append hprefix tailTrace_798341
  have hstable : (prefixWord ++ tailWord_798341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798341).length < 2 ^ (prefixWord ++ tailWord_798341).sum := by decide
  have hdescent : baseEnd_798341 < baseStart_798341 := by decide
  rcases family_descends (prefixWord ++ tailWord_798341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798418 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_798418 : Nat := 118140960795 + 798418 * 2 ^ 59
def prefixEnd_798418 : Nat := 4983230072969 + 3 ^ 40 * 798418 * 2
def baseEnd_798418 : Nat := 273314798134374946402099

theorem tailTrace_798418 : CollatzResearch.WordTrace tailWord_798418 prefixEnd_798418 273314798134374946402099 := by
  unfold tailWord_798418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280174205368854945854977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19413797880983613188946605 7280174205368854945854977)
  ·
    refine ⟨5460130654026641209391233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7280174205368854945854977 5460130654026641209391233)
    ·
      refine ⟨4095097990519980907043425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5460130654026641209391233 4095097990519980907043425)
      ·
        refine ⟨3071323492889985680282569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4095097990519980907043425 3071323492889985680282569)
        ·
          refine ⟨2303492619667489260211927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071323492889985680282569 2303492619667489260211927)
          ·
            refine ⟨3455238929501233890317891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303492619667489260211927 3455238929501233890317891)
            ·
              refine ⟨5182858394251850835476837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455238929501233890317891 5182858394251850835476837)
              ·
                refine ⟨971785948922222031651907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5182858394251850835476837 971785948922222031651907)
                ·
                  refine ⟨1457678923383333047477861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971785948922222031651907 1457678923383333047477861)
                  ·
                    refine ⟨273314798134374946402099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1457678923383333047477861 273314798134374946402099)
                    ·
                      rfl

theorem cell22_798418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_798418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798418 prefixEnd_798418 := by exact prefixLift 798418
  have htrace : WordTrace (prefixWord ++ tailWord_798418) baseStart_798418 baseEnd_798418 := by
    simpa [prefixWord, tailWord_798418, baseEnd_798418] using wordTrace_append hprefix tailTrace_798418
  have hstable : (prefixWord ++ tailWord_798418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798418).length < 2 ^ (prefixWord ++ tailWord_798418).sum := by decide
  have hdescent : baseEnd_798418 < baseStart_798418 := by decide
  rcases family_descends (prefixWord ++ tailWord_798418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798431 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 6, 3]
def baseStart_798431 : Nat := 118140960795 + 798431 * 2 ^ 59
def prefixEnd_798431 : Nat := 4983230072969 + 3 ^ 40 * 798431 * 2
def baseEnd_798431 : Nat := 273319248300047245827059

theorem tailTrace_798431 : CollatzResearch.WordTrace tailWord_798431 prefixEnd_798431 273319248300047245827059 := by
  unfold tailWord_798431
  simp only [CollatzResearch.WordTrace]
  refine ⟨29121170970428323003643147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19414113980285548669095431 29121170970428323003643147)
  ·
    refine ⟨43681756455642484505464721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29121170970428323003643147 43681756455642484505464721)
    ·
      refine ⟨32761317341731863379098541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43681756455642484505464721 32761317341731863379098541)
      ·
        refine ⟨12285494003149448767161953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32761317341731863379098541 12285494003149448767161953)
        ·
          refine ⟨9214120502362086575371465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12285494003149448767161953 9214120502362086575371465)
          ·
            refine ⟨6910590376771564931528599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9214120502362086575371465 6910590376771564931528599)
            ·
              refine ⟨10365885565157347397292899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6910590376771564931528599 10365885565157347397292899)
              ·
                refine ⟨15548828347736021095939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10365885565157347397292899 15548828347736021095939349)
                ·
                  refine ⟨728851328800125988872157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15548828347736021095939349 728851328800125988872157)
                  ·
                    refine ⟨273319248300047245827059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728851328800125988872157 273319248300047245827059)
                    ·
                      rfl

theorem cell22_798431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 6, 3].length) (baseStart_798431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798431 prefixEnd_798431 := by exact prefixLift 798431
  have htrace : WordTrace (prefixWord ++ tailWord_798431) baseStart_798431 baseEnd_798431 := by
    simpa [prefixWord, tailWord_798431, baseEnd_798431] using wordTrace_append hprefix tailTrace_798431
  have hstable : (prefixWord ++ tailWord_798431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798431).length < 2 ^ (prefixWord ++ tailWord_798431).sum := by decide
  have hdescent : baseEnd_798431 < baseStart_798431 := by decide
  rcases family_descends (prefixWord ++ tailWord_798431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798444 : List Nat := [2, 2, 1, 1, 2, 2, 12]
def baseStart_798444 : Nat := 118140960795 + 798444 * 2 ^ 59
def prefixEnd_798444 : Nat := 4983230072969 + 3 ^ 40 * 798444 * 2
def baseEnd_798444 : Nat := 10123099943174797972297

theorem tailTrace_798444 : CollatzResearch.WordTrace tailWord_798444 prefixEnd_798444 10123099943174797972297 := by
  unfold tailWord_798444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14560822559690613111933193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19414430079587484149244257 14560822559690613111933193)
  ·
    refine ⟨10920616919767959833949895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14560822559690613111933193 10920616919767959833949895)
    ·
      refine ⟨16380925379651939750924843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10920616919767959833949895 16380925379651939750924843)
      ·
        refine ⟨24571388069477909626387265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16380925379651939750924843 24571388069477909626387265)
        ·
          refine ⟨18428541052108432219790449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24571388069477909626387265 18428541052108432219790449)
          ·
            refine ⟨13821405789081324164842837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18428541052108432219790449 13821405789081324164842837)
            ·
              refine ⟨10123099943174797972297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13821405789081324164842837 10123099943174797972297)
              ·
                rfl

theorem cell22_798444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 12].length) (baseStart_798444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798444 prefixEnd_798444 := by exact prefixLift 798444
  have htrace : WordTrace (prefixWord ++ tailWord_798444) baseStart_798444 baseEnd_798444 := by
    simpa [prefixWord, tailWord_798444, baseEnd_798444] using wordTrace_append hprefix tailTrace_798444
  have hstable : (prefixWord ++ tailWord_798444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798444).length < 2 ^ (prefixWord ++ tailWord_798444).sum := by decide
  have hdescent : baseEnd_798444 < baseStart_798444 := by decide
  rcases family_descends (prefixWord ++ tailWord_798444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798450 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_798450 : Nat := 118140960795 + 798450 * 2 ^ 59
def prefixEnd_798450 : Nat := 4983230072969 + 3 ^ 40 * 798450 * 2
def baseEnd_798450 : Nat := 91108584129445843200667

theorem tailTrace_798450 : CollatzResearch.WordTrace tailWord_798450 prefixEnd_798450 91108584129445843200667 := by
  unfold tailWord_798450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280465989339872312146201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19414575971572992832389869 7280465989339872312146201)
  ·
    refine ⟨5460349492004904234109651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7280465989339872312146201 5460349492004904234109651)
    ·
      refine ⟨8190524238007356351164477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460349492004904234109651 8190524238007356351164477)
      ·
        refine ⟨3071446589252758631686679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8190524238007356351164477 3071446589252758631686679)
        ·
          refine ⟨4607169883879137947530019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071446589252758631686679 4607169883879137947530019)
          ·
            refine ⟨6910754825818706921295029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607169883879137947530019 6910754825818706921295029)
            ·
              refine ⟨647883264920503773871409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6910754825818706921295029 647883264920503773871409)
              ·
                refine ⟨485912448690377830403557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647883264920503773871409 485912448690377830403557)
                ·
                  refine ⟨91108584129445843200667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485912448690377830403557 91108584129445843200667)
                  ·
                    rfl

theorem cell22_798450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_798450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798450 prefixEnd_798450 := by exact prefixLift 798450
  have htrace : WordTrace (prefixWord ++ tailWord_798450) baseStart_798450 baseEnd_798450 := by
    simpa [prefixWord, tailWord_798450, baseEnd_798450] using wordTrace_append hprefix tailTrace_798450
  have hstable : (prefixWord ++ tailWord_798450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798450).length < 2 ^ (prefixWord ++ tailWord_798450).sum := by decide
  have hdescent : baseEnd_798450 < baseStart_798450 := by decide
  rcases family_descends (prefixWord ++ tailWord_798450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798459 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_798459 : Nat := 118140960795 + 798459 * 2 ^ 59
def prefixEnd_798459 : Nat := 4983230072969 + 3 ^ 40 * 798459 * 2
def baseEnd_798459 : Nat := 273328833272264506126973

theorem tailTrace_798459 : CollatzResearch.WordTrace tailWord_798459 prefixEnd_798459 273328833272264506126973 := by
  unfold tailWord_798459
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122192214326883785662431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19414794809551255857108287 29122192214326883785662431)
  ·
    refine ⟨43683288321490325678493647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29122192214326883785662431 43683288321490325678493647)
    ·
      refine ⟨65524932482235488517740471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43683288321490325678493647 65524932482235488517740471)
      ·
        refine ⟨98287398723353232776610707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65524932482235488517740471 98287398723353232776610707)
        ·
          refine ⟨147431098085029849164916061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98287398723353232776610707 147431098085029849164916061)
          ·
            refine ⟨55286661781886193436843523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147431098085029849164916061 55286661781886193436843523)
            ·
              refine ⟨82929992672829290155265285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55286661781886193436843523 82929992672829290155265285)
              ·
                refine ⟨15549373626155491904112241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82929992672829290155265285 15549373626155491904112241)
                ·
                  refine ⟨11662030219616618928084181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15549373626155491904112241 11662030219616618928084181)
                  ·
                    refine ⟨273328833272264506126973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11662030219616618928084181 273328833272264506126973)
                    ·
                      rfl

theorem cell22_798459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_798459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798459 prefixEnd_798459 := by exact prefixLift 798459
  have htrace : WordTrace (prefixWord ++ tailWord_798459) baseStart_798459 baseEnd_798459 := by
    simpa [prefixWord, tailWord_798459, baseEnd_798459] using wordTrace_append hprefix tailTrace_798459
  have hstable : (prefixWord ++ tailWord_798459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798459).length < 2 ^ (prefixWord ++ tailWord_798459).sum := by decide
  have hdescent : baseEnd_798459 < baseStart_798459 := by decide
  rcases family_descends (prefixWord ++ tailWord_798459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798465 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 2, 3]
def baseStart_798465 : Nat := 118140960795 + 798465 * 2 ^ 59
def prefixEnd_798465 : Nat := 4983230072969 + 3 ^ 40 * 798465 * 2
def baseEnd_798465 : Nat := 273330887194882490476955

theorem tailTrace_798465 : CollatzResearch.WordTrace tailWord_798465 prefixEnd_798465 273330887194882490476955 := by
  unfold tailWord_798465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122411052305146810380849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19414940701536764540253899 29122411052305146810380849)
  ·
    refine ⟨21841808289228860107785637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29122411052305146810380849 21841808289228860107785637)
    ·
      refine ⟨4095339054230411270209807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21841808289228860107785637 4095339054230411270209807)
      ·
        refine ⟨6143008581345616905314711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095339054230411270209807 6143008581345616905314711)
        ·
          refine ⟨9214512872018425357972067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143008581345616905314711 9214512872018425357972067)
          ·
            refine ⟨13821769308027638036958101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9214512872018425357972067 13821769308027638036958101)
            ·
              refine ⟨647895436313795532982411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13821769308027638036958101 647895436313795532982411)
              ·
                refine ⟨971843154470693299473617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647895436313795532982411 971843154470693299473617)
                ·
                  refine ⟨728882365853019974605213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 971843154470693299473617 728882365853019974605213)
                  ·
                    refine ⟨273330887194882490476955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 728882365853019974605213 273330887194882490476955)
                    ·
                      rfl

theorem cell22_798465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_798465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798465 prefixEnd_798465 := by exact prefixLift 798465
  have htrace : WordTrace (prefixWord ++ tailWord_798465) baseStart_798465 baseEnd_798465 := by
    simpa [prefixWord, tailWord_798465, baseEnd_798465] using wordTrace_append hprefix tailTrace_798465
  have hstable : (prefixWord ++ tailWord_798465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798465).length < 2 ^ (prefixWord ++ tailWord_798465).sum := by decide
  have hdescent : baseEnd_798465 < baseStart_798465 := by decide
  rcases family_descends (prefixWord ++ tailWord_798465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798553 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_798553 : Nat := 118140960795 + 798553 * 2 ^ 59
def prefixEnd_798553 : Nat := 4983230072969 + 3 ^ 40 * 798553 * 2
def baseEnd_798553 : Nat := 273361011393279594276685

theorem tailTrace_798553 : CollatzResearch.WordTrace tailWord_798553 prefixEnd_798553 273361011393279594276685 := by
  unfold tailWord_798553
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125620675986337839584313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19417080450657558559722875 29125620675986337839584313)
  ·
    refine ⟨21844215506989753379688235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29125620675986337839584313 21844215506989753379688235)
    ·
      refine ⟨32766323260484630069532353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21844215506989753379688235 32766323260484630069532353)
      ·
        refine ⟨24574742445363472552149265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32766323260484630069532353 24574742445363472552149265)
        ·
          refine ⟨18431056834022604414111949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24574742445363472552149265 18431056834022604414111949)
          ·
            refine ⟨6911646312758476655291981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18431056834022604414111949 6911646312758476655291981)
            ·
              refine ⟨2591867367284428745734493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6911646312758476655291981 2591867367284428745734493)
              ·
                refine ⟨971950262731660779650435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2591867367284428745734493 971950262731660779650435)
                ·
                  refine ⟨1457925394097491169475653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 971950262731660779650435 1457925394097491169475653)
                  ·
                    refine ⟨273361011393279594276685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1457925394097491169475653 273361011393279594276685)
                    ·
                      rfl

theorem cell22_798553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_798553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798553 prefixEnd_798553 := by exact prefixLift 798553
  have htrace : WordTrace (prefixWord ++ tailWord_798553) baseStart_798553 baseEnd_798553 := by
    simpa [prefixWord, tailWord_798553, baseEnd_798553] using wordTrace_append hprefix tailTrace_798553
  have hstable : (prefixWord ++ tailWord_798553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798553).length < 2 ^ (prefixWord ++ tailWord_798553).sum := by decide
  have hdescent : baseEnd_798553 < baseStart_798553 := by decide
  rcases family_descends (prefixWord ++ tailWord_798553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798568 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_798568 : Nat := 118140960795 + 798568 * 2 ^ 59
def prefixEnd_798568 : Nat := 4983230072969 + 3 ^ 40 * 798568 * 2
def baseEnd_798568 : Nat := 91122048733274851717213

theorem tailTrace_798568 : CollatzResearch.WordTrace tailWord_798568 prefixEnd_798568 91122048733274851717213 := by
  unfold tailWord_798568
  simp only [CollatzResearch.WordTrace]
  refine ⟨14563083885465997700690179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19417445180621330267586905 14563083885465997700690179)
  ·
    refine ⟨21844625828198996551035269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14563083885465997700690179 21844625828198996551035269)
    ·
      refine ⟨4095867342787311853319113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21844625828198996551035269 4095867342787311853319113)
      ·
        refine ⟨3071900507090483889989335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4095867342787311853319113 3071900507090483889989335)
        ·
          refine ⟨4607850760635725834984003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071900507090483889989335 4607850760635725834984003)
          ·
            refine ⟨6911776140953588752476005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607850760635725834984003 6911776140953588752476005)
            ·
              refine ⟨1295958026428797891089251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6911776140953588752476005 1295958026428797891089251)
              ·
                refine ⟨1943937039643196836633877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295958026428797891089251 1943937039643196836633877)
                ·
                  refine ⟨91122048733274851717213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1943937039643196836633877 91122048733274851717213)
                  ·
                    rfl

theorem cell22_798568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_798568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798568 prefixEnd_798568 := by exact prefixLift 798568
  have htrace : WordTrace (prefixWord ++ tailWord_798568) baseStart_798568 baseEnd_798568 := by
    simpa [prefixWord, tailWord_798568, baseEnd_798568] using wordTrace_append hprefix tailTrace_798568
  have hstable : (prefixWord ++ tailWord_798568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798568).length < 2 ^ (prefixWord ++ tailWord_798568).sum := by decide
  have hdescent : baseEnd_798568 < baseStart_798568 := by decide
  rcases family_descends (prefixWord ++ tailWord_798568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
