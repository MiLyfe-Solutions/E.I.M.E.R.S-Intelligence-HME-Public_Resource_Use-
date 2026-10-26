import V185TrunkScan23Chunk0891

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5279824 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_5279824 : Nat := 118140960795 + 5279824 * 2 ^ 59
def prefixEnd_5279824 : Nat := 4983230072969 + 3 ^ 40 * 5279824 * 2
def baseEnd_5279824 : Nat := 903695827714751966006179

theorem tailTrace_5279824 : CollatzResearch.WordTrace tailWord_5279824 prefixEnd_5279824 903695827714751966006179 := by
  unfold tailWord_5279824
  simp only [CollatzResearch.WordTrace]
  refine ⟨96285500812053422497271263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128380667749404563329695017 96285500812053422497271263)
  ·
    refine ⟨144428251218080133745906895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96285500812053422497271263 144428251218080133745906895)
    ·
      refine ⟨216642376827120200618860343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144428251218080133745906895 216642376827120200618860343)
      ·
        refine ⟨324963565240680300928290515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216642376827120200618860343 324963565240680300928290515)
        ·
          refine ⟨487445347861020451392435773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324963565240680300928290515 487445347861020451392435773)
          ·
            refine ⟨182792005447882669272163415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487445347861020451392435773 182792005447882669272163415)
            ·
              refine ⟨274188008171824003908245123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182792005447882669272163415 274188008171824003908245123)
              ·
                refine ⟨411282012257736005862367685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274188008171824003908245123 411282012257736005862367685)
                ·
                  refine ⟨77115377298325501099193941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411282012257736005862367685 77115377298325501099193941)
                  ·
                    refine ⟨903695827714751966006179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77115377298325501099193941 903695827714751966006179)
                    ·
                      rfl

theorem cell23_5279824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_5279824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279824 prefixEnd_5279824 := by exact prefixLift 5279824
  have htrace : WordTrace (prefixWord ++ tailWord_5279824) baseStart_5279824 baseEnd_5279824 := by
    simpa [prefixWord, tailWord_5279824, baseEnd_5279824] using wordTrace_append hprefix tailTrace_5279824
  have hstable : (prefixWord ++ tailWord_5279824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279824).length < 2 ^ (prefixWord ++ tailWord_5279824).sum := by decide
  have hdescent : baseEnd_5279824 < baseStart_5279824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279831 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_5279831 : Nat := 118140960795 + 5279831 * 2 ^ 59
def prefixEnd_5279831 : Nat := 4983230072969 + 3 ^ 40 * 5279831 * 2
def baseEnd_5279831 : Nat := 2711091077508837370631005

theorem tailTrace_5279831 : CollatzResearch.WordTrace tailWord_5279831 prefixEnd_5279831 2711091077508837370631005 := by
  unfold tailWord_5279831
  simp only [CollatzResearch.WordTrace]
  refine ⟨192571256935081485190047347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128380837956720990126698231 192571256935081485190047347)
  ·
    refine ⟨288856885402622227785071021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192571256935081485190047347 288856885402622227785071021)
    ·
      refine ⟨108321332025983335419401633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288856885402622227785071021 108321332025983335419401633)
      ·
        refine ⟨81240999019487501564551225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108321332025983335419401633 81240999019487501564551225)
        ·
          refine ⟨60930749264615626173413419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81240999019487501564551225 60930749264615626173413419)
          ·
            refine ⟨91396123896923439260120129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60930749264615626173413419 91396123896923439260120129)
            ·
              refine ⟨68547092922692579445090097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91396123896923439260120129 68547092922692579445090097)
              ·
                refine ⟨51410319692019434583817573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68547092922692579445090097 51410319692019434583817573)
                ·
                  refine ⟨9639434942253643984465795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51410319692019434583817573 9639434942253643984465795)
                  ·
                    refine ⟨14459152413380465976698693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9639434942253643984465795 14459152413380465976698693)
                    ·
                      refine ⟨2711091077508837370631005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14459152413380465976698693 2711091077508837370631005)
                      ·
                        rfl

theorem cell23_5279831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_5279831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279831 prefixEnd_5279831 := by exact prefixLift 5279831
  have htrace : WordTrace (prefixWord ++ tailWord_5279831) baseStart_5279831 baseEnd_5279831 := by
    simpa [prefixWord, tailWord_5279831, baseEnd_5279831] using wordTrace_append hprefix tailTrace_5279831
  have hstable : (prefixWord ++ tailWord_5279831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279831).length < 2 ^ (prefixWord ++ tailWord_5279831).sum := by decide
  have hdescent : baseEnd_5279831 < baseStart_5279831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279875 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 1, 4]
def baseStart_5279875 : Nat := 118140960795 + 5279875 * 2 ^ 59
def prefixEnd_5279875 : Nat := 4983230072969 + 3 ^ 40 * 5279875 * 2
def baseEnd_5279875 : Nat := 903704556885878399493601

theorem tailTrace_5279875 : CollatzResearch.WordTrace tailWord_5279875 prefixEnd_5279875 903704556885878399493601 := by
  unfold tailWord_5279875
  simp only [CollatzResearch.WordTrace]
  refine ⟨192572861746922080704649079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128381907831281387136432719 192572861746922080704649079)
  ·
    refine ⟨288859292620383121056973619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192572861746922080704649079 288859292620383121056973619)
    ·
      refine ⟨433288938930574681585460429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288859292620383121056973619 433288938930574681585460429)
      ·
        refine ⟨162483352098965505594547661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433288938930574681585460429 162483352098965505594547661)
        ·
          refine ⟨60931257037112064597955373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162483352098965505594547661 60931257037112064597955373)
          ·
            refine ⟨22849221388917024224233265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60931257037112064597955373 22849221388917024224233265)
            ·
              refine ⟨17136916041687768168174949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22849221388917024224233265 17136916041687768168174949)
              ·
                refine ⟨3213171757816456531532803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17136916041687768168174949 3213171757816456531532803)
                ·
                  refine ⟨4819757636724684797299205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213171757816456531532803 4819757636724684797299205)
                  ·
                    refine ⟨903704556885878399493601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4819757636724684797299205 903704556885878399493601)
                    ·
                      rfl

theorem cell23_5279875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 4].length) (baseStart_5279875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279875 prefixEnd_5279875 := by exact prefixLift 5279875
  have htrace : WordTrace (prefixWord ++ tailWord_5279875) baseStart_5279875 baseEnd_5279875 := by
    simpa [prefixWord, tailWord_5279875, baseEnd_5279875] using wordTrace_append hprefix tailTrace_5279875
  have hstable : (prefixWord ++ tailWord_5279875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279875).length < 2 ^ (prefixWord ++ tailWord_5279875).sum := by decide
  have hdescent : baseEnd_5279875 < baseStart_5279875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279888 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 6]
def baseStart_5279888 : Nat := 118140960795 + 5279888 * 2 ^ 59
def prefixEnd_5279888 : Nat := 4983230072969 + 3 ^ 40 * 5279888 * 2
def baseEnd_5279888 : Nat := 301235593989571516402027

theorem tailTrace_5279888 : CollatzResearch.WordTrace tailWord_5279888 prefixEnd_5279888 301235593989571516402027 := by
  unfold tailWord_5279888
  simp only [CollatzResearch.WordTrace]
  refine ⟨96286667947937491962436159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128382223930583322616581545 96286667947937491962436159)
  ·
    refine ⟨144430001921906237943654239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96286667947937491962436159 144430001921906237943654239)
    ·
      refine ⟨216645002882859356915481359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144430001921906237943654239 216645002882859356915481359)
      ·
        refine ⟨324967504324289035373222039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216645002882859356915481359 324967504324289035373222039)
        ·
          refine ⟨487451256486433553059833059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324967504324289035373222039 487451256486433553059833059)
          ·
            refine ⟨731176884729650329589749589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487451256486433553059833059 731176884729650329589749589)
            ·
              refine ⟨4284239558962794899939939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 731176884729650329589749589 4284239558962794899939939)
              ·
                refine ⟨6426359338444192349909909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284239558962794899939939 6426359338444192349909909)
                ·
                  refine ⟨301235593989571516402027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6426359338444192349909909 301235593989571516402027)
                  ·
                    rfl

theorem cell23_5279888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 6].length) (baseStart_5279888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279888 prefixEnd_5279888 := by exact prefixLift 5279888
  have htrace : WordTrace (prefixWord ++ tailWord_5279888) baseStart_5279888 baseEnd_5279888 := by
    simpa [prefixWord, tailWord_5279888, baseEnd_5279888] using wordTrace_append hprefix tailTrace_5279888
  have hstable : (prefixWord ++ tailWord_5279888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279888).length < 2 ^ (prefixWord ++ tailWord_5279888).sum := by decide
  have hdescent : baseEnd_5279888 < baseStart_5279888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279951 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_5279951 : Nat := 118140960795 + 5279951 * 2 ^ 59
def prefixEnd_5279951 : Nat := 4983230072969 + 3 ^ 40 * 5279951 * 2
def baseEnd_5279951 : Nat := 2711152695187376901130453

theorem tailTrace_5279951 : CollatzResearch.WordTrace tailWord_5279951 prefixEnd_5279951 2711152695187376901130453 := by
  unfold tailWord_5279951
  simp only [CollatzResearch.WordTrace]
  refine ⟨192575633694646745684415707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128383755796431163789610471 192575633694646745684415707)
  ·
    refine ⟨288863450541970118526623561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192575633694646745684415707 288863450541970118526623561)
    ·
      refine ⟨216647587906477588894967671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288863450541970118526623561 216647587906477588894967671)
      ·
        refine ⟨324971381859716383342451507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216647587906477588894967671 324971381859716383342451507)
        ·
          refine ⟨487457072789574575013677261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324971381859716383342451507 487457072789574575013677261)
          ·
            refine ⟨182796402296090465630128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487457072789574575013677261 182796402296090465630128973)
            ·
              refine ⟨68548650861033924611298365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182796402296090465630128973 68548650861033924611298365)
              ·
                refine ⟨25705744072887721729236887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68548650861033924611298365 25705744072887721729236887)
                ·
                  refine ⟨38558616109331582593855331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25705744072887721729236887 38558616109331582593855331)
                  ·
                    refine ⟨57837924163997373890782997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38558616109331582593855331 57837924163997373890782997)
                    ·
                      refine ⟨2711152695187376901130453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57837924163997373890782997 2711152695187376901130453)
                      ·
                        rfl

theorem cell23_5279951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_5279951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279951 prefixEnd_5279951 := by exact prefixLift 5279951
  have htrace : WordTrace (prefixWord ++ tailWord_5279951) baseStart_5279951 baseEnd_5279951 := by
    simpa [prefixWord, tailWord_5279951, baseEnd_5279951] using wordTrace_append hprefix tailTrace_5279951
  have hstable : (prefixWord ++ tailWord_5279951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279951).length < 2 ^ (prefixWord ++ tailWord_5279951).sum := by decide
  have hdescent : baseEnd_5279951 < baseStart_5279951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279961 : List Nat := [1, 2, 1, 2, 3, 1, 4, 9]
def baseStart_5279961 : Nat := 118140960795 + 5279961 * 2 ^ 59
def prefixEnd_5279961 : Nat := 4983230072969 + 3 ^ 40 * 5279961 * 2
def baseEnd_5279961 : Nat := 100413252962737846740941

theorem tailTrace_5279961 : CollatzResearch.WordTrace tailWord_5279961 prefixEnd_5279961 100413252962737846740941 := by
  unfold tailWord_5279961
  simp only [CollatzResearch.WordTrace]
  refine ⟨192575998424610517392279737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128383998949740344928186491 192575998424610517392279737)
  ·
    refine ⟨144431998818457888044209803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192575998424610517392279737 144431998818457888044209803)
    ·
      refine ⟨216647998227686832066314705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144431998818457888044209803 216647998227686832066314705)
      ·
        refine ⟨162485998670765124049736029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216647998227686832066314705 162485998670765124049736029)
        ·
          refine ⟨60932249501536921518651011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162485998670765124049736029 60932249501536921518651011)
          ·
            refine ⟨91398374252305382277976517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60932249501536921518651011 91398374252305382277976517)
            ·
              refine ⟨17137195172307259177120597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91398374252305382277976517 17137195172307259177120597)
              ·
                refine ⟨100413252962737846740941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17137195172307259177120597 100413252962737846740941)
                ·
                  rfl

theorem cell23_5279961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 9].length) (baseStart_5279961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279961 prefixEnd_5279961 := by exact prefixLift 5279961
  have htrace : WordTrace (prefixWord ++ tailWord_5279961) baseStart_5279961 baseEnd_5279961 := by
    simpa [prefixWord, tailWord_5279961, baseEnd_5279961] using wordTrace_append hprefix tailTrace_5279961
  have hstable : (prefixWord ++ tailWord_5279961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279961).length < 2 ^ (prefixWord ++ tailWord_5279961).sum := by decide
  have hdescent : baseEnd_5279961 < baseStart_5279961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279965 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_5279965 : Nat := 118140960795 + 5279965 * 2 ^ 59
def prefixEnd_5279965 : Nat := 4983230072969 + 3 ^ 40 * 5279965 * 2
def baseEnd_5279965 : Nat := 903719961305513282118463

theorem tailTrace_5279965 : CollatzResearch.WordTrace tailWord_5279965 prefixEnd_5279965 903719961305513282118463 := by
  unfold tailWord_5279965
  simp only [CollatzResearch.WordTrace]
  refine ⟨192576144316596026075425349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128384096211064017383616899 192576144316596026075425349)
  ·
    refine ⟨36108027059361754889142253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192576144316596026075425349 36108027059361754889142253)
    ·
      refine ⟨13540510147260658083428345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36108027059361754889142253 13540510147260658083428345)
      ·
        refine ⟨10155382610445493562571259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13540510147260658083428345 10155382610445493562571259)
        ·
          refine ⟨15233073915668240343856889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10155382610445493562571259 15233073915668240343856889)
          ·
            refine ⟨11424805436751180257892667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15233073915668240343856889 11424805436751180257892667)
            ·
              refine ⟨17137208155126770386839001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11424805436751180257892667 17137208155126770386839001)
              ·
                refine ⟨12852906116345077790129251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17137208155126770386839001 12852906116345077790129251)
                ·
                  refine ⟨19279359174517616685193877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12852906116345077790129251 19279359174517616685193877)
                  ·
                    refine ⟨903719961305513282118463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19279359174517616685193877 903719961305513282118463)
                    ·
                      rfl

theorem cell23_5279965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_5279965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279965 prefixEnd_5279965 := by exact prefixLift 5279965
  have htrace : WordTrace (prefixWord ++ tailWord_5279965) baseStart_5279965 baseEnd_5279965 := by
    simpa [prefixWord, tailWord_5279965, baseEnd_5279965] using wordTrace_append hprefix tailTrace_5279965
  have hstable : (prefixWord ++ tailWord_5279965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279965).length < 2 ^ (prefixWord ++ tailWord_5279965).sum := by decide
  have hdescent : baseEnd_5279965 < baseStart_5279965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279968 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_5279968 : Nat := 118140960795 + 5279968 * 2 ^ 59
def prefixEnd_5279968 : Nat := 4983230072969 + 3 ^ 40 * 5279968 * 2
def baseEnd_5279968 : Nat := 2711161424358503334617875

theorem tailTrace_5279968 : CollatzResearch.WordTrace tailWord_5279968 prefixEnd_5279968 2711161424358503334617875 := by
  unfold tailWord_5279968
  simp only [CollatzResearch.WordTrace]
  refine ⟨96288126867792578793892279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128384169157056771725189705 96288126867792578793892279)
  ·
    refine ⟨144432190301688868190838419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96288126867792578793892279 144432190301688868190838419)
    ·
      refine ⟨216648285452533302286257629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144432190301688868190838419 216648285452533302286257629)
      ·
        refine ⟨81243107044699988357346611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216648285452533302286257629 81243107044699988357346611)
        ·
          refine ⟨121864660567049982536019917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81243107044699988357346611 121864660567049982536019917)
          ·
            refine ⟨45699247712643743451007469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121864660567049982536019917 45699247712643743451007469)
            ·
              refine ⟨17137217892241403794127801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45699247712643743451007469 17137217892241403794127801)
              ·
                refine ⟨12852913419181052845595851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17137217892241403794127801 12852913419181052845595851)
                ·
                  refine ⟨19279370128771579268393777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12852913419181052845595851 19279370128771579268393777)
                  ·
                    refine ⟨14459527596578684451295333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19279370128771579268393777 14459527596578684451295333)
                    ·
                      refine ⟨2711161424358503334617875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14459527596578684451295333 2711161424358503334617875)
                      ·
                        rfl

theorem cell23_5279968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_5279968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279968 prefixEnd_5279968 := by exact prefixLift 5279968
  have htrace : WordTrace (prefixWord ++ tailWord_5279968) baseStart_5279968 baseEnd_5279968 := by
    simpa [prefixWord, tailWord_5279968, baseEnd_5279968] using wordTrace_append hprefix tailTrace_5279968
  have hstable : (prefixWord ++ tailWord_5279968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279968).length < 2 ^ (prefixWord ++ tailWord_5279968).sum := by decide
  have hdescent : baseEnd_5279968 < baseStart_5279968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5279975 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5279975 : Nat := 118140960795 + 5279975 * 2 ^ 59
def prefixEnd_5279975 : Nat := 4983230072969 + 3 ^ 40 * 5279975 * 2
def baseEnd_5279975 : Nat := 2711165018723084807230343

theorem tailTrace_5279975 : CollatzResearch.WordTrace tailWord_5279975 prefixEnd_5279975 2711165018723084807230343 := by
  unfold tailWord_5279975
  simp only [CollatzResearch.WordTrace]
  refine ⟨192576509046559797783289379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128384339364373198522192919 192576509046559797783289379)
  ·
    refine ⟨288864763569839696674934069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192576509046559797783289379 288864763569839696674934069)
    ·
      refine ⟨27081071584672471563275069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288864763569839696674934069 27081071584672471563275069)
      ·
        refine ⟨10155401844252176836228151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27081071584672471563275069 10155401844252176836228151)
        ·
          refine ⟨15233102766378265254342227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10155401844252176836228151 15233102766378265254342227)
          ·
            refine ⟨22849654149567397881513341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15233102766378265254342227 22849654149567397881513341)
            ·
              refine ⟨8568620306087774205567503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22849654149567397881513341 8568620306087774205567503)
              ·
                refine ⟨12852930459131661308351255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568620306087774205567503 12852930459131661308351255)
                ·
                  refine ⟨19279395688697491962526883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12852930459131661308351255 19279395688697491962526883)
                  ·
                    refine ⟨28919093533046237943790325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19279395688697491962526883 28919093533046237943790325)
                    ·
                      refine ⟨2711165018723084807230343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28919093533046237943790325 2711165018723084807230343)
                      ·
                        rfl

theorem cell23_5279975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5279975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5279975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5279975 prefixEnd_5279975 := by exact prefixLift 5279975
  have htrace : WordTrace (prefixWord ++ tailWord_5279975) baseStart_5279975 baseEnd_5279975 := by
    simpa [prefixWord, tailWord_5279975, baseEnd_5279975] using wordTrace_append hprefix tailTrace_5279975
  have hstable : (prefixWord ++ tailWord_5279975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5279975).length < 2 ^ (prefixWord ++ tailWord_5279975).sum := by decide
  have hdescent : baseEnd_5279975 < baseStart_5279975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5279975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280002 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5280002 : Nat := 118140960795 + 5280002 * 2 ^ 59
def prefixEnd_5280002 : Nat := 4983230072969 + 3 ^ 40 * 5280002 * 2
def baseEnd_5280002 : Nat := 2711178882700756201592719

theorem tailTrace_5280002 : CollatzResearch.WordTrace tailWord_5280002 prefixEnd_5280002 2711178882700756201592719 := by
  unfold tailWord_5280002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48144373454365495348630565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128384995878307987596348173 48144373454365495348630565)
  ·
    refine ⟨9027070022693530377868231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48144373454365495348630565 9027070022693530377868231)
    ·
      refine ⟨13540605034040295566802347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9027070022693530377868231 13540605034040295566802347)
      ·
        refine ⟨20310907551060443350203521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13540605034040295566802347 20310907551060443350203521)
        ·
          refine ⟨15233180663295332512652641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20310907551060443350203521 15233180663295332512652641)
          ·
            refine ⟨11424885497471499384489481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15233180663295332512652641 11424885497471499384489481)
            ·
              refine ⟨8568664123103624538367111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11424885497471499384489481 8568664123103624538367111)
              ·
                refine ⟨12852996184655436807550667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568664123103624538367111 12852996184655436807550667)
                ·
                  refine ⟨19279494276983155211326001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12852996184655436807550667 19279494276983155211326001)
                  ·
                    refine ⟨14459620707737366408494501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19279494276983155211326001 14459620707737366408494501)
                    ·
                      refine ⟨2711178882700756201592719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14459620707737366408494501 2711178882700756201592719)
                      ·
                        rfl

theorem cell23_5280002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5280002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280002 prefixEnd_5280002 := by exact prefixLift 5280002
  have htrace : WordTrace (prefixWord ++ tailWord_5280002) baseStart_5280002 baseEnd_5280002 := by
    simpa [prefixWord, tailWord_5280002, baseEnd_5280002] using wordTrace_append hprefix tailTrace_5280002
  have hstable : (prefixWord ++ tailWord_5280002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280002).length < 2 ^ (prefixWord ++ tailWord_5280002).sum := by decide
  have hdescent : baseEnd_5280002 < baseStart_5280002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280026 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3]
def baseStart_5280026 : Nat := 118140960795 + 5280026 * 2 ^ 59
def prefixEnd_5280026 : Nat := 4983230072969 + 3 ^ 40 * 5280026 * 2
def baseEnd_5280026 : Nat := 2711191206236464107692609

theorem tailTrace_5280026 : CollatzResearch.WordTrace tailWord_5280026 prefixEnd_5280026 2711191206236464107692609 := by
  unfold tailWord_5280026
  simp only [CollatzResearch.WordTrace]
  refine ⟨48144592292343758373348983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128385579446250022328930621 48144592292343758373348983)
  ·
    refine ⟨72216888438515637560023475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48144592292343758373348983 72216888438515637560023475)
    ·
      refine ⟨108325332657773456340035213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72216888438515637560023475 108325332657773456340035213)
      ·
        refine ⟨40621999746665046127513205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108325332657773456340035213 40621999746665046127513205)
        ·
          refine ⟨3808312476249848074454363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40621999746665046127513205 3808312476249848074454363)
          ·
            refine ⟨5712468714374772111681545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808312476249848074454363 5712468714374772111681545)
            ·
              refine ⟨4284351535781079083761159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5712468714374772111681545 4284351535781079083761159)
              ·
                refine ⟨6426527303671618625641739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284351535781079083761159 6426527303671618625641739)
                ·
                  refine ⟨9639790955507427938462609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426527303671618625641739 9639790955507427938462609)
                  ·
                    refine ⟨7229843216630570953846957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9639790955507427938462609 7229843216630570953846957)
                    ·
                      refine ⟨2711191206236464107692609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7229843216630570953846957 2711191206236464107692609)
                      ·
                        rfl

theorem cell23_5280026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_5280026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280026 prefixEnd_5280026 := by exact prefixLift 5280026
  have htrace : WordTrace (prefixWord ++ tailWord_5280026) baseStart_5280026 baseEnd_5280026 := by
    simpa [prefixWord, tailWord_5280026, baseEnd_5280026] using wordTrace_append hprefix tailTrace_5280026
  have hstable : (prefixWord ++ tailWord_5280026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280026).length < 2 ^ (prefixWord ++ tailWord_5280026).sum := by decide
  have hdescent : baseEnd_5280026 < baseStart_5280026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280048 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_5280048 : Nat := 118140960795 + 5280048 * 2 ^ 59
def prefixEnd_5280048 : Nat := 4983230072969 + 3 ^ 40 * 5280048 * 2
def baseEnd_5280048 : Nat := 2711202502810863021617507

theorem tailTrace_5280048 : CollatzResearch.WordTrace tailWord_5280048 prefixEnd_5280048 2711202502810863021617507 := by
  unfold tailWord_5280048
  simp only [CollatzResearch.WordTrace]
  refine ⟨96289585787647665625348399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128386114383530220833797865 96289585787647665625348399)
  ·
    refine ⟨144434378681471498438022599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96289585787647665625348399 144434378681471498438022599)
    ·
      refine ⟨216651568022207247657033899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144434378681471498438022599 216651568022207247657033899)
      ·
        refine ⟨324977352033310871485550849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216651568022207247657033899 324977352033310871485550849)
        ·
          refine ⟨243733014024983153614163137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324977352033310871485550849 243733014024983153614163137)
          ·
            refine ⟨182799760518737365210622353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243733014024983153614163137 182799760518737365210622353)
            ·
              refine ⟨137099820389053023907966765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182799760518737365210622353 137099820389053023907966765)
              ·
                refine ⟨51412432645894883965487537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137099820389053023907966765 51412432645894883965487537)
                ·
                  refine ⟨38559324484421162974115653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51412432645894883965487537 38559324484421162974115653)
                  ·
                    refine ⟨7229873340828968057646685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38559324484421162974115653 7229873340828968057646685)
                    ·
                      refine ⟨2711202502810863021617507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7229873340828968057646685 2711202502810863021617507)
                      ·
                        rfl

theorem cell23_5280048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_5280048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280048 prefixEnd_5280048 := by exact prefixLift 5280048
  have htrace : WordTrace (prefixWord ++ tailWord_5280048) baseStart_5280048 baseEnd_5280048 := by
    simpa [prefixWord, tailWord_5280048, baseEnd_5280048] using wordTrace_append hprefix tailTrace_5280048
  have hstable : (prefixWord ++ tailWord_5280048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280048).length < 2 ^ (prefixWord ++ tailWord_5280048).sum := by decide
  have hdescent : baseEnd_5280048 < baseStart_5280048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280105 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 2, 5, 2]
def baseStart_5280105 : Nat := 118140960795 + 5280105 * 2 ^ 59
def prefixEnd_5280105 : Nat := 4983230072969 + 3 ^ 40 * 5280105 * 2
def baseEnd_5280105 : Nat := 2711231771208169298604745

theorem tailTrace_5280105 : CollatzResearch.WordTrace tailWord_5280105 prefixEnd_5280105 2711231771208169298604745 := by
  unfold tailWord_5280105
  simp only [CollatzResearch.WordTrace]
  refine ⟨192581250536088829985521769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128387500357392553323681179 192581250536088829985521769)
  ·
    refine ⟨144435937902066622489141327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192581250536088829985521769 144435937902066622489141327)
    ·
      refine ⟨216653906853099933733711991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144435937902066622489141327 216653906853099933733711991)
      ·
        refine ⟨324980860279649900600567987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216653906853099933733711991 324980860279649900600567987)
        ·
          refine ⟨487471290419474850900851981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324980860279649900600567987 487471290419474850900851981)
          ·
            refine ⟨182801733907303069087819493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487471290419474850900851981 182801733907303069087819493)
            ·
              refine ⟨34275325107619325453966155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182801733907303069087819493 34275325107619325453966155)
              ·
                refine ⟨51412987661428988180949233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34275325107619325453966155 51412987661428988180949233)
                ·
                  refine ⟨38559740746071741135711925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51412987661428988180949233 38559740746071741135711925)
                  ·
                    refine ⟨3614975694944225731472993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38559740746071741135711925 3614975694944225731472993)
                    ·
                      refine ⟨2711231771208169298604745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3614975694944225731472993 2711231771208169298604745)
                      ·
                        rfl

theorem cell23_5280105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 5, 2].length) (baseStart_5280105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280105 prefixEnd_5280105 := by exact prefixLift 5280105
  have htrace : WordTrace (prefixWord ++ tailWord_5280105) baseStart_5280105 baseEnd_5280105 := by
    simpa [prefixWord, tailWord_5280105, baseEnd_5280105] using wordTrace_append hprefix tailTrace_5280105
  have hstable : (prefixWord ++ tailWord_5280105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280105).length < 2 ^ (prefixWord ++ tailWord_5280105).sum := by decide
  have hdescent : baseEnd_5280105 < baseStart_5280105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280152 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5280152 : Nat := 118140960795 + 5280152 * 2 ^ 59
def prefixEnd_5280152 : Nat := 4983230072969 + 3 ^ 40 * 5280152 * 2
def baseEnd_5280152 : Nat := 2711255904798930614717029

theorem tailTrace_5280152 : CollatzResearch.WordTrace tailWord_5280152 prefixEnd_5280152 2711255904798930614717029 := by
  unfold tailWord_5280152
  simp only [CollatzResearch.WordTrace]
  refine ⟨96291482383459278506241355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128388643177945704674988473 96291482383459278506241355)
  ·
    refine ⟨144437223575188917759362033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96291482383459278506241355 144437223575188917759362033)
    ·
      refine ⟨108327917681391688319521525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144437223575188917759362033 108327917681391688319521525)
      ·
        refine ⟨10155742282630470779955143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108327917681391688319521525 10155742282630470779955143)
        ·
          refine ⟨15233613423945706169932715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10155742282630470779955143 15233613423945706169932715)
          ·
            refine ⟨22850420135918559254899073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15233613423945706169932715 22850420135918559254899073)
            ·
              refine ⟨17137815101938919441174305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22850420135918559254899073 17137815101938919441174305)
              ·
                refine ⟨12853361326454189580880729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17137815101938919441174305 12853361326454189580880729)
                ·
                  refine ⟨9640020994840642185660547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12853361326454189580880729 9640020994840642185660547)
                  ·
                    refine ⟨14460031492260963278490821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9640020994840642185660547 14460031492260963278490821)
                    ·
                      refine ⟨2711255904798930614717029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14460031492260963278490821 2711255904798930614717029)
                      ·
                        rfl

theorem cell23_5280152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5280152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280152 prefixEnd_5280152 := by exact prefixLift 5280152
  have htrace : WordTrace (prefixWord ++ tailWord_5280152) baseStart_5280152 baseEnd_5280152 := by
    simpa [prefixWord, tailWord_5280152, baseEnd_5280152] using wordTrace_append hprefix tailTrace_5280152
  have hstable : (prefixWord ++ tailWord_5280152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280152).length < 2 ^ (prefixWord ++ tailWord_5280152).sum := by decide
  have hdescent : baseEnd_5280152 < baseStart_5280152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280162 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5280162 : Nat := 118140960795 + 5280162 * 2 ^ 59
def prefixEnd_5280162 : Nat := 4983230072969 + 3 ^ 40 * 5280162 * 2
def baseEnd_5280162 : Nat := 903753679868491858530661

theorem tailTrace_5280162 : CollatzResearch.WordTrace tailWord_5280162 prefixEnd_5280162 903753679868491858530661 := by
  unfold tailWord_5280162
  simp only [CollatzResearch.WordTrace]
  refine ⟨48145832374220582180086685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128388886331254885813564493 48145832374220582180086685)
  ·
    refine ⟨18054687140332718317532507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48145832374220582180086685 18054687140332718317532507)
    ·
      refine ⟨27082030710499077476298761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18054687140332718317532507 27082030710499077476298761)
      ·
        refine ⟨20311523032874308107224071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27082030710499077476298761 20311523032874308107224071)
        ·
          refine ⟨30467284549311462160836107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20311523032874308107224071 30467284549311462160836107)
          ·
            refine ⟨45700926823967193241254161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30467284549311462160836107 45700926823967193241254161)
            ·
              refine ⟨34275695117975394930940621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45700926823967193241254161 34275695117975394930940621)
              ·
                refine ⟨12853385669240773099102733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34275695117975394930940621 12853385669240773099102733)
                ·
                  refine ⟨4820019625965289912163525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12853385669240773099102733 4820019625965289912163525)
                  ·
                    refine ⟨903753679868491858530661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820019625965289912163525 903753679868491858530661)
                    ·
                      rfl

theorem cell23_5280162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5280162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280162 prefixEnd_5280162 := by exact prefixLift 5280162
  have htrace : WordTrace (prefixWord ++ tailWord_5280162) baseStart_5280162 baseEnd_5280162 := by
    simpa [prefixWord, tailWord_5280162, baseEnd_5280162] using wordTrace_append hprefix tailTrace_5280162
  have hstable : (prefixWord ++ tailWord_5280162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280162).length < 2 ^ (prefixWord ++ tailWord_5280162).sum := by decide
  have hdescent : baseEnd_5280162 < baseStart_5280162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280189 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_5280189 : Nat := 118140960795 + 5280189 * 2 ^ 59
def prefixEnd_5280189 : Nat := 4983230072969 + 3 ^ 40 * 5280189 * 2
def baseEnd_5280189 : Nat := 2711274903583146969954359

theorem tailTrace_5280189 : CollatzResearch.WordTrace tailWord_5280189 prefixEnd_5280189 2711274903583146969954359 := by
  unfold tailWord_5280189
  simp only [CollatzResearch.WordTrace]
  refine ⟨192584314267784512331579621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128389542845189674887719747 192584314267784512331579621)
  ·
    refine ⟨36109558925209596062171179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192584314267784512331579621 36109558925209596062171179)
    ·
      refine ⟨54164338387814394093256769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36109558925209596062171179 54164338387814394093256769)
      ·
        refine ⟨40623253790860795569942577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54164338387814394093256769 40623253790860795569942577)
        ·
          refine ⟨30467440343145596677456933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40623253790860795569942577 30467440343145596677456933)
          ·
            refine ⟨5712645064339799377023175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30467440343145596677456933 5712645064339799377023175)
            ·
              refine ⟨8568967596509699065534763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712645064339799377023175 8568967596509699065534763)
              ·
                refine ⟨12853451394764548598302145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568967596509699065534763 12853451394764548598302145)
                ·
                  refine ⟨9640088546073411448726609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12853451394764548598302145 9640088546073411448726609)
                  ·
                    refine ⟨7230066409555058586544957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9640088546073411448726609 7230066409555058586544957)
                    ·
                      refine ⟨2711274903583146969954359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7230066409555058586544957 2711274903583146969954359)
                      ·
                        rfl

theorem cell23_5280189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_5280189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280189 prefixEnd_5280189 := by exact prefixLift 5280189
  have htrace : WordTrace (prefixWord ++ tailWord_5280189) baseStart_5280189 baseEnd_5280189 := by
    simpa [prefixWord, tailWord_5280189, baseEnd_5280189] using wordTrace_append hprefix tailTrace_5280189
  have hstable : (prefixWord ++ tailWord_5280189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280189).length < 2 ^ (prefixWord ++ tailWord_5280189).sum := by decide
  have hdescent : baseEnd_5280189 < baseStart_5280189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280202 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_5280202 : Nat := 118140960795 + 5280202 * 2 ^ 59
def prefixEnd_5280202 : Nat := 4983230072969 + 3 ^ 40 * 5280202 * 2
def baseEnd_5280202 : Nat := 2711281578831655419091799

theorem tailTrace_5280202 : CollatzResearch.WordTrace tailWord_5280202 prefixEnd_5280202 2711281578831655419091799 := by
  unfold tailWord_5280202
  simp only [CollatzResearch.WordTrace]
  refine ⟨48146197104184353887950715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128389858944491610367868573 48146197104184353887950715)
  ·
    refine ⟨72219295656276530831926073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48146197104184353887950715 72219295656276530831926073)
    ·
      refine ⟨54164471742207398123944555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72219295656276530831926073 54164471742207398123944555)
      ·
        refine ⟨81246707613311097185916833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54164471742207398123944555 81246707613311097185916833)
        ·
          refine ⟨60935030709983322889437625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81246707613311097185916833 60935030709983322889437625)
          ·
            refine ⟨45701273032487492167078219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60935030709983322889437625 45701273032487492167078219)
            ·
              refine ⟨68551909548731238250617329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45701273032487492167078219 68551909548731238250617329)
              ·
                refine ⟨51413932161548428687962997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68551909548731238250617329 51413932161548428687962997)
                ·
                  refine ⟨4820056140145165189496531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51413932161548428687962997 4820056140145165189496531)
                  ·
                    refine ⟨7230084210217747784244797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4820056140145165189496531 7230084210217747784244797)
                    ·
                      refine ⟨2711281578831655419091799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7230084210217747784244797 2711281578831655419091799)
                      ·
                        rfl

theorem cell23_5280202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_5280202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280202 prefixEnd_5280202 := by exact prefixLift 5280202
  have htrace : WordTrace (prefixWord ++ tailWord_5280202) baseStart_5280202 baseEnd_5280202 := by
    simpa [prefixWord, tailWord_5280202, baseEnd_5280202] using wordTrace_append hprefix tailTrace_5280202
  have hstable : (prefixWord ++ tailWord_5280202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280202).length < 2 ^ (prefixWord ++ tailWord_5280202).sum := by decide
  have hdescent : baseEnd_5280202 < baseStart_5280202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280255 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 4]
def baseStart_5280255 : Nat := 118140960795 + 5280255 * 2 ^ 59
def prefixEnd_5280255 : Nat := 4983230072969 + 3 ^ 40 * 5280255 * 2
def baseEnd_5280255 : Nat := 2711308793306343711729055

theorem tailTrace_5280255 : CollatzResearch.WordTrace tailWord_5280255 prefixEnd_5280255 2711308793306343711729055 := by
  unfold tailWord_5280255
  simp only [CollatzResearch.WordTrace]
  refine ⟨192586721485545405603482219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128391147657030270402321479 192586721485545405603482219)
  ·
    refine ⟨288880082228318108405223329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192586721485545405603482219 288880082228318108405223329)
    ·
      refine ⟨216660061671238581303917497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288880082228318108405223329 216660061671238581303917497)
      ·
        refine ⟨162495046253428935977938123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216660061671238581303917497 162495046253428935977938123)
        ·
          refine ⟨243742569380143403966907185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162495046253428935977938123 243742569380143403966907185)
          ·
            refine ⟨182806927035107552975180389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243742569380143403966907185 182806927035107552975180389)
            ·
              refine ⟨34276298819082666182846323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182806927035107552975180389 34276298819082666182846323)
              ·
                refine ⟨51414448228623999274269485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34276298819082666182846323 51414448228623999274269485)
                ·
                  refine ⟨19280418085733999727851057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51414448228623999274269485 19280418085733999727851057)
                  ·
                    refine ⟨14460313564300499795888293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19280418085733999727851057 14460313564300499795888293)
                    ·
                      refine ⟨2711308793306343711729055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14460313564300499795888293 2711308793306343711729055)
                      ·
                        rfl

theorem cell23_5280255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_5280255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280255 prefixEnd_5280255 := by exact prefixLift 5280255
  have htrace : WordTrace (prefixWord ++ tailWord_5280255) baseStart_5280255 baseEnd_5280255 := by
    simpa [prefixWord, tailWord_5280255, baseEnd_5280255] using wordTrace_append hprefix tailTrace_5280255
  have hstable : (prefixWord ++ tailWord_5280255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280255).length < 2 ^ (prefixWord ++ tailWord_5280255).sum := by decide
  have hdescent : baseEnd_5280255 < baseStart_5280255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280296 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5280296 : Nat := 118140960795 + 5280296 * 2 ^ 59
def prefixEnd_5280296 : Nat := 4983230072969 + 3 ^ 40 * 5280296 * 2
def baseEnd_5280296 : Nat := 2711329846013178051316367

theorem tailTrace_5280296 : CollatzResearch.WordTrace tailWord_5280296 prefixEnd_5280296 2711329846013178051316367 := by
  unfold tailWord_5280296
  simp only [CollatzResearch.WordTrace]
  refine ⟨96294108439198434802862371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128392144585597913070483161 96294108439198434802862371)
  ·
    refine ⟨144441162658797652204293557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96294108439198434802862371 144441162658797652204293557)
    ·
      refine ⟨13541358999262279894152521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 144441162658797652204293557 13541358999262279894152521)
      ·
        refine ⟨10156019249446709920614391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13541358999262279894152521 10156019249446709920614391)
        ·
          refine ⟨15234028874170064880921587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10156019249446709920614391 15234028874170064880921587)
          ·
            refine ⟨22851043311255097321382381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15234028874170064880921587 22851043311255097321382381)
            ·
              refine ⟨8569141241720661495518393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22851043311255097321382381 8569141241720661495518393)
              ·
                refine ⟨6426855931290496121638795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8569141241720661495518393 6426855931290496121638795)
                ·
                  refine ⟨9640283896935744182458193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426855931290496121638795 9640283896935744182458193)
                  ·
                    refine ⟨7230212922701808136843645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9640283896935744182458193 7230212922701808136843645)
                    ·
                      refine ⟨2711329846013178051316367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7230212922701808136843645 2711329846013178051316367)
                      ·
                        rfl

theorem cell23_5280296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5280296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280296 prefixEnd_5280296 := by exact prefixLift 5280296
  have htrace : WordTrace (prefixWord ++ tailWord_5280296) baseStart_5280296 baseEnd_5280296 := by
    simpa [prefixWord, tailWord_5280296, baseEnd_5280296] using wordTrace_append hprefix tailTrace_5280296
  have hstable : (prefixWord ++ tailWord_5280296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280296).length < 2 ^ (prefixWord ++ tailWord_5280296).sum := by decide
  have hdescent : baseEnd_5280296 < baseStart_5280296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280305 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_5280305 : Nat := 118140960795 + 5280305 * 2 ^ 59
def prefixEnd_5280305 : Nat := 4983230072969 + 3 ^ 40 * 5280305 * 2
def baseEnd_5280305 : Nat := 2711334467339068516103825

theorem tailTrace_5280305 : CollatzResearch.WordTrace tailWord_5280305 prefixEnd_5280305 2711334467339068516103825 := by
  unfold tailWord_5280305
  simp only [CollatzResearch.WordTrace]
  refine ⟨192588545135364264142802369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128392363423576176095201579 192588545135364264142802369)
  ·
    refine ⟨144441408851523198107101777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192588545135364264142802369 144441408851523198107101777)
    ·
      refine ⟨108331056638642398580326333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144441408851523198107101777 108331056638642398580326333)
      ·
        refine ⟨40624146239490899467622375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108331056638642398580326333 40624146239490899467622375)
        ·
          refine ⟨60936219359236349201433563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40624146239490899467622375 60936219359236349201433563)
          ·
            refine ⟨91404329038854523802150345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60936219359236349201433563 91404329038854523802150345)
            ·
              refine ⟨68553246779140892851612759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91404329038854523802150345 68553246779140892851612759)
              ·
                refine ⟨102829870168711339277419139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68553246779140892851612759 102829870168711339277419139)
                ·
                  refine ⟨154244805253067008916128709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102829870168711339277419139 154244805253067008916128709)
                  ·
                    refine ⟨28920900984950064171774133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154244805253067008916128709 28920900984950064171774133)
                    ·
                      refine ⟨2711334467339068516103825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28920900984950064171774133 2711334467339068516103825)
                      ·
                        rfl

theorem cell23_5280305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_5280305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280305 prefixEnd_5280305 := by exact prefixLift 5280305
  have htrace : WordTrace (prefixWord ++ tailWord_5280305) baseStart_5280305 baseEnd_5280305 := by
    simpa [prefixWord, tailWord_5280305, baseEnd_5280305] using wordTrace_append hprefix tailTrace_5280305
  have hstable : (prefixWord ++ tailWord_5280305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280305).length < 2 ^ (prefixWord ++ tailWord_5280305).sum := by decide
  have hdescent : baseEnd_5280305 < baseStart_5280305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280335 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_5280335 : Nat := 118140960795 + 5280335 * 2 ^ 59
def prefixEnd_5280335 : Nat := 4983230072969 + 3 ^ 40 * 5280335 * 2
def baseEnd_5280335 : Nat := 2711349871758703398728687

theorem tailTrace_5280335 : CollatzResearch.WordTrace tailWord_5280335 prefixEnd_5280335 2711349871758703398728687 := by
  unfold tailWord_5280335
  simp only [CollatzResearch.WordTrace]
  refine ⟨192589639325255579266394459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128393092883503719510929639 192589639325255579266394459)
  ·
    refine ⟨288884458987883368899591689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192589639325255579266394459 288884458987883368899591689)
    ·
      refine ⟨216663344240912526674693767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288884458987883368899591689 216663344240912526674693767)
      ·
        refine ⟨324995016361368790012040651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216663344240912526674693767 324995016361368790012040651)
        ·
          refine ⟨487492524542053185018060977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324995016361368790012040651 487492524542053185018060977)
          ·
            refine ⟨365619393406539888763545733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487492524542053185018060977 365619393406539888763545733)
            ·
              refine ⟨68553636263726229143164825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 365619393406539888763545733 68553636263726229143164825)
              ·
                refine ⟨51415227197794671857373619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68553636263726229143164825 51415227197794671857373619)
                ·
                  refine ⟨77122840796692007786060429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51415227197794671857373619 77122840796692007786060429)
                  ·
                    refine ⟨28921065298759502919772661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77122840796692007786060429 28921065298759502919772661)
                    ·
                      refine ⟨2711349871758703398728687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28921065298759502919772661 2711349871758703398728687)
                      ·
                        rfl

theorem cell23_5280335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_5280335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280335 prefixEnd_5280335 := by exact prefixLift 5280335
  have htrace : WordTrace (prefixWord ++ tailWord_5280335) baseStart_5280335 baseEnd_5280335 := by
    simpa [prefixWord, tailWord_5280335, baseEnd_5280335] using wordTrace_append hprefix tailTrace_5280335
  have hstable : (prefixWord ++ tailWord_5280335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280335).length < 2 ^ (prefixWord ++ tailWord_5280335).sum := by decide
  have hdescent : baseEnd_5280335 < baseStart_5280335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280362 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5280362 : Nat := 118140960795 + 5280362 * 2 ^ 59
def prefixEnd_5280362 : Nat := 4983230072969 + 3 ^ 40 * 5280362 * 2
def baseEnd_5280362 : Nat := 2711363735736374793091063

theorem tailTrace_5280362 : CollatzResearch.WordTrace tailWord_5280362 prefixEnd_5280362 2711363735736374793091063 := by
  unfold tailWord_5280362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48147656024039440719406835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128393749397438508585084893 48147656024039440719406835)
  ·
    refine ⟨72221484036059161079110253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48147656024039440719406835 72221484036059161079110253)
    ·
      refine ⟨27083056513522185404666345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72221484036059161079110253 27083056513522185404666345)
      ·
        refine ⟨20312292385141639053499759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27083056513522185404666345 20312292385141639053499759)
        ·
          refine ⟨30468438577712458580249639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20312292385141639053499759 30468438577712458580249639)
          ·
            refine ⟨45702657866568687870374459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30468438577712458580249639 45702657866568687870374459)
            ·
              refine ⟨68553986799853031805561689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45702657866568687870374459 68553986799853031805561689)
              ·
                refine ⟨51415490099889773854171267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68553986799853031805561689 51415490099889773854171267)
                ·
                  refine ⟨77123235149834660781256901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51415490099889773854171267 77123235149834660781256901)
                  ·
                    refine ⟨14460606590593998896485669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77123235149834660781256901 14460606590593998896485669)
                    ·
                      refine ⟨2711363735736374793091063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14460606590593998896485669 2711363735736374793091063)
                      ·
                        rfl

theorem cell23_5280362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5280362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280362 prefixEnd_5280362 := by exact prefixLift 5280362
  have htrace : WordTrace (prefixWord ++ tailWord_5280362) baseStart_5280362 baseEnd_5280362 := by
    simpa [prefixWord, tailWord_5280362, baseEnd_5280362] using wordTrace_append hprefix tailTrace_5280362
  have hstable : (prefixWord ++ tailWord_5280362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280362).length < 2 ^ (prefixWord ++ tailWord_5280362).sum := by decide
  have hdescent : baseEnd_5280362 < baseStart_5280362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280366 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_5280366 : Nat := 118140960795 + 5280366 * 2 ^ 59
def prefixEnd_5280366 : Nat := 4983230072969 + 3 ^ 40 * 5280366 * 2
def baseEnd_5280366 : Nat := 2711365789658992777441045

theorem tailTrace_5280366 : CollatzResearch.WordTrace tailWord_5280366 prefixEnd_5280366 2711365789658992777441045 := by
  unfold tailWord_5280366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24073846248517908945096619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128393846658762181040515301 24073846248517908945096619)
  ·
    refine ⟨36110769372776863417644929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24073846248517908945096619 36110769372776863417644929)
    ·
      refine ⟨27083077029582647563233697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36110769372776863417644929 27083077029582647563233697)
      ·
        refine ⟨20312307772186985672425273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27083077029582647563233697 20312307772186985672425273)
        ·
          refine ⟨15234230829140239254318955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20312307772186985672425273 15234230829140239254318955)
          ·
            refine ⟨22851346243710358881478433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15234230829140239254318955 22851346243710358881478433)
            ·
              refine ⟨17138509682782769161108825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22851346243710358881478433 17138509682782769161108825)
              ·
                refine ⟨12853882262087076870831619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17138509682782769161108825 12853882262087076870831619)
                ·
                  refine ⟨19280823393130615306247429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12853882262087076870831619 19280823393130615306247429)
                  ·
                    refine ⟨3615154386211990369921393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19280823393130615306247429 3615154386211990369921393)
                    ·
                      refine ⟨2711365789658992777441045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615154386211990369921393 2711365789658992777441045)
                      ·
                        rfl

theorem cell23_5280366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_5280366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280366 prefixEnd_5280366 := by exact prefixLift 5280366
  have htrace : WordTrace (prefixWord ++ tailWord_5280366) baseStart_5280366 baseEnd_5280366 := by
    simpa [prefixWord, tailWord_5280366, baseEnd_5280366] using wordTrace_append hprefix tailTrace_5280366
  have hstable : (prefixWord ++ tailWord_5280366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280366).length < 2 ^ (prefixWord ++ tailWord_5280366).sum := by decide
  have hdescent : baseEnd_5280366 < baseStart_5280366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280370 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_5280370 : Nat := 118140960795 + 5280370 * 2 ^ 59
def prefixEnd_5280370 : Nat := 4983230072969 + 3 ^ 40 * 5280370 * 2
def baseEnd_5280370 : Nat := 2711367843581610761791027

theorem tailTrace_5280370 : CollatzResearch.WordTrace tailWord_5280370 prefixEnd_5280370 2711367843581610761791027 := by
  unfold tailWord_5280370
  simp only [CollatzResearch.WordTrace]
  refine ⟨48147728970032195060979641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128393943920085853495945709 48147728970032195060979641)
  ·
    refine ⟨36110796727524146295734731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48147728970032195060979641 36110796727524146295734731)
    ·
      refine ⟨54166195091286219443602097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36110796727524146295734731 54166195091286219443602097)
      ·
        refine ⟨40624646318464664582701573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54166195091286219443602097 40624646318464664582701573)
        ·
          refine ⟨7617121184712124609256545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40624646318464664582701573 7617121184712124609256545)
          ·
            refine ⟨5712840888534093456942409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7617121184712124609256545 5712840888534093456942409)
            ·
              refine ⟨4284630666400570092706807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5712840888534093456942409 4284630666400570092706807)
              ·
                refine ⟨6426945999600855139060211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284630666400570092706807 6426945999600855139060211)
                ·
                  refine ⟨9640418999401282708590317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6426945999600855139060211 9640418999401282708590317)
                  ·
                    refine ⟨3615157124775481015721369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9640418999401282708590317 3615157124775481015721369)
                    ·
                      refine ⟨2711367843581610761791027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615157124775481015721369 2711367843581610761791027)
                      ·
                        rfl

theorem cell23_5280370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_5280370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280370 prefixEnd_5280370 := by exact prefixLift 5280370
  have htrace : WordTrace (prefixWord ++ tailWord_5280370) baseStart_5280370 baseEnd_5280370 := by
    simpa [prefixWord, tailWord_5280370, baseEnd_5280370] using wordTrace_append hprefix tailTrace_5280370
  have hstable : (prefixWord ++ tailWord_5280370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280370).length < 2 ^ (prefixWord ++ tailWord_5280370).sum := by decide
  have hdescent : baseEnd_5280370 < baseStart_5280370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280389 : List Nat := [1, 3, 1, 1, 4, 2, 2, 4, 5]
def baseStart_5280389 : Nat := 118140960795 + 5280389 * 2 ^ 59
def prefixEnd_5280389 : Nat := 4983230072969 + 3 ^ 40 * 5280389 * 2
def baseEnd_5280389 : Nat := 301264177746005131939271

theorem tailTrace_5280389 : CollatzResearch.WordTrace tailWord_5280389 prefixEnd_5280389 301264177746005131939271 := by
  unfold tailWord_5280389
  simp only [CollatzResearch.WordTrace]
  refine ⟨192591608867059946488860221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128394405911373297659240147 192591608867059946488860221)
  ·
    refine ⟨72221853325147479933322583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192591608867059946488860221 72221853325147479933322583)
    ·
      refine ⟨108332779987721219899983875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72221853325147479933322583 108332779987721219899983875)
      ·
        refine ⟨162499169981581829849975813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108332779987721219899983875 162499169981581829849975813)
        ·
          refine ⟨30468594371546593096870465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162499169981581829849975813 30468594371546593096870465)
          ·
            refine ⟨22851445778659944822652849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30468594371546593096870465 22851445778659944822652849)
            ·
              refine ⟨17138584333994958616989637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22851445778659944822652849 17138584333994958616989637)
              ·
                refine ⟨3213484562624054740685557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17138584333994958616989637 3213484562624054740685557)
                ·
                  refine ⟨301264177746005131939271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3213484562624054740685557 301264177746005131939271)
                  ·
                    rfl

theorem cell23_5280389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_5280389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280389 prefixEnd_5280389 := by exact prefixLift 5280389
  have htrace : WordTrace (prefixWord ++ tailWord_5280389) baseStart_5280389 baseEnd_5280389 := by
    simpa [prefixWord, tailWord_5280389, baseEnd_5280389] using wordTrace_append hprefix tailTrace_5280389
  have hstable : (prefixWord ++ tailWord_5280389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280389).length < 2 ^ (prefixWord ++ tailWord_5280389).sum := by decide
  have hdescent : baseEnd_5280389 < baseStart_5280389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280499 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 3, 5, 2]
def baseStart_5280499 : Nat := 118140960795 + 5280499 * 2 ^ 59
def prefixEnd_5280499 : Nat := 4983230072969 + 3 ^ 40 * 5280499 * 2
def baseEnd_5280499 : Nat := 2711434082586040757077933

theorem tailTrace_5280499 : CollatzResearch.WordTrace tailWord_5280499 prefixEnd_5280499 2711434082586040757077933 := by
  unfold tailWord_5280499
  simp only [CollatzResearch.WordTrace]
  refine ⟨192595620896661435275364551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128397080597774290183576367 192595620896661435275364551)
  ·
    refine ⟨288893431344992152913046827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192595620896661435275364551 288893431344992152913046827)
    ·
      refine ⟨433340147017488229369570241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288893431344992152913046827 433340147017488229369570241)
      ·
        refine ⟨325005110263116172027177681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433340147017488229369570241 325005110263116172027177681)
        ·
          refine ⟨243753832697337129020383261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325005110263116172027177681 243753832697337129020383261)
          ·
            refine ⟨91407687261501423382643723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243753832697337129020383261 91407687261501423382643723)
            ·
              refine ⟨137111530892252135073965585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91407687261501423382643723 137111530892252135073965585)
              ·
                refine ⟨102833648169189101305474189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137111530892252135073965585 102833648169189101305474189)
                ·
                  refine ⟨38562618063445912989552821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102833648169189101305474189 38562618063445912989552821)
                  ·
                    refine ⟨3615245443448054342770577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38562618063445912989552821 3615245443448054342770577)
                    ·
                      refine ⟨2711434082586040757077933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615245443448054342770577 2711434082586040757077933)
                      ·
                        rfl

theorem cell23_5280499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5, 2].length) (baseStart_5280499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280499 prefixEnd_5280499 := by exact prefixLift 5280499
  have htrace : WordTrace (prefixWord ++ tailWord_5280499) baseStart_5280499 baseEnd_5280499 := by
    simpa [prefixWord, tailWord_5280499, baseEnd_5280499] using wordTrace_append hprefix tailTrace_5280499
  have hstable : (prefixWord ++ tailWord_5280499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280499).length < 2 ^ (prefixWord ++ tailWord_5280499).sum := by decide
  have hdescent : baseEnd_5280499 < baseStart_5280499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280512 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_5280512 : Nat := 118140960795 + 5280512 * 2 ^ 59
def prefixEnd_5280512 : Nat := 4983230072969 + 3 ^ 40 * 5280512 * 2
def baseEnd_5280512 : Nat := 2711440757834549206215373

theorem tailTrace_5280512 : CollatzResearch.WordTrace tailWord_5280512 prefixEnd_5280512 2711440757834549206215373 := by
  unfold tailWord_5280512
  simp only [CollatzResearch.WordTrace]
  refine ⟨96298047522807169247793895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128397396697076225663725193 96298047522807169247793895)
  ·
    refine ⟨144447071284210753871690843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96298047522807169247793895 144447071284210753871690843)
    ·
      refine ⟨216670606926316130807536265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144447071284210753871690843 216670606926316130807536265)
      ·
        refine ⟨162502955194737098105652199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216670606926316130807536265 162502955194737098105652199)
        ·
          refine ⟨243754432792105647158478299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162502955194737098105652199 243754432792105647158478299)
          ·
            refine ⟨365631649188158470737717449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243754432792105647158478299 365631649188158470737717449)
            ·
              refine ⟨274223736891118853053288087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365631649188158470737717449 274223736891118853053288087)
              ·
                refine ⟨411335605336678279579932131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274223736891118853053288087 411335605336678279579932131)
                ·
                  refine ⟨617003408005017419369898197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411335605336678279579932131 617003408005017419369898197)
                  ·
                    refine ⟨14461017375117595766481989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 617003408005017419369898197 14461017375117595766481989)
                    ·
                      refine ⟨2711440757834549206215373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14461017375117595766481989 2711440757834549206215373)
                      ·
                        rfl

theorem cell23_5280512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_5280512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280512 prefixEnd_5280512 := by exact prefixLift 5280512
  have htrace : WordTrace (prefixWord ++ tailWord_5280512) baseStart_5280512 baseEnd_5280512 := by
    simpa [prefixWord, tailWord_5280512, baseEnd_5280512] using wordTrace_append hprefix tailTrace_5280512
  have hstable : (prefixWord ++ tailWord_5280512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280512).length < 2 ^ (prefixWord ++ tailWord_5280512).sum := by decide
  have hdescent : baseEnd_5280512 < baseStart_5280512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280516 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_5280516 : Nat := 118140960795 + 5280516 * 2 ^ 59
def prefixEnd_5280516 : Nat := 4983230072969 + 3 ^ 40 * 5280516 * 2
def baseEnd_5280516 : Nat := 2711442811757167190565355

theorem tailTrace_5280516 : CollatzResearch.WordTrace tailWord_5280516 prefixEnd_5280516 2711442811757167190565355 := by
  unfold tailWord_5280516
  simp only [CollatzResearch.WordTrace]
  refine ⟨96298120468799923589366701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128397493958399898119155601 96298120468799923589366701)
  ·
    refine ⟨36111795175799971346012513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96298120468799923589366701 36111795175799971346012513)
    ·
      refine ⟨27083846381849978509509385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36111795175799971346012513 27083846381849978509509385)
      ·
        refine ⟨20312884786387483882132039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27083846381849978509509385 20312884786387483882132039)
        ·
          refine ⟨30469327179581225823198059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20312884786387483882132039 30469327179581225823198059)
          ·
            refine ⟨45703990769371838734797089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30469327179581225823198059 45703990769371838734797089)
            ·
              refine ⟨34277993077028879051097817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45703990769371838734797089 34277993077028879051097817)
              ·
                refine ⟨25708494807771659288323363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34277993077028879051097817 25708494807771659288323363)
                ·
                  refine ⟨38562742211657488932485045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25708494807771659288323363 38562742211657488932485045)
                  ·
                    refine ⟨3615257082342889587420473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38562742211657488932485045 3615257082342889587420473)
                    ·
                      refine ⟨2711442811757167190565355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615257082342889587420473 2711442811757167190565355)
                      ·
                        rfl

theorem cell23_5280516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_5280516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280516 prefixEnd_5280516 := by exact prefixLift 5280516
  have htrace : WordTrace (prefixWord ++ tailWord_5280516) baseStart_5280516 baseEnd_5280516 := by
    simpa [prefixWord, tailWord_5280516, baseEnd_5280516] using wordTrace_append hprefix tailTrace_5280516
  have hstable : (prefixWord ++ tailWord_5280516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280516).length < 2 ^ (prefixWord ++ tailWord_5280516).sum := by decide
  have hdescent : baseEnd_5280516 < baseStart_5280516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280529 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_5280529 : Nat := 118140960795 + 5280529 * 2 ^ 59
def prefixEnd_5280529 : Nat := 4983230072969 + 3 ^ 40 * 5280529 * 2
def baseEnd_5280529 : Nat := 2711449487005675639702795

theorem tailTrace_5280529 : CollatzResearch.WordTrace tailWord_5280529 prefixEnd_5280529 2711449487005675639702795 := by
  unfold tailWord_5280529
  simp only [CollatzResearch.WordTrace]
  refine ⟨192596715086552750398956641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128397810057701833599304427 192596715086552750398956641)
  ·
    refine ⟨144447536314914562799217481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192596715086552750398956641 144447536314914562799217481)
    ·
      refine ⟨108335652236185922099413111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144447536314914562799217481 108335652236185922099413111)
      ·
        refine ⟨162503478354278883149119667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108335652236185922099413111 162503478354278883149119667)
        ·
          refine ⟨243755217531418324723679501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162503478354278883149119667 243755217531418324723679501)
          ·
            refine ⟨91408206574281871771379813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243755217531418324723679501 91408206574281871771379813)
            ·
              refine ⟨17139038732677850957133715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91408206574281871771379813 17139038732677850957133715)
              ·
                refine ⟨25708558099016776435700573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17139038732677850957133715 25708558099016776435700573)
                ·
                  refine ⟨9640709287131291163387715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25708558099016776435700573 9640709287131291163387715)
                  ·
                    refine ⟨14461063930696936745081573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9640709287131291163387715 14461063930696936745081573)
                    ·
                      refine ⟨2711449487005675639702795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14461063930696936745081573 2711449487005675639702795)
                      ·
                        rfl

theorem cell23_5280529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_5280529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280529 prefixEnd_5280529 := by exact prefixLift 5280529
  have htrace : WordTrace (prefixWord ++ tailWord_5280529) baseStart_5280529 baseEnd_5280529 := by
    simpa [prefixWord, tailWord_5280529, baseEnd_5280529] using wordTrace_append hprefix tailTrace_5280529
  have hstable : (prefixWord ++ tailWord_5280529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280529).length < 2 ^ (prefixWord ++ tailWord_5280529).sum := by decide
  have hdescent : baseEnd_5280529 < baseStart_5280529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280540 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_5280540 : Nat := 118140960795 + 5280540 * 2 ^ 59
def prefixEnd_5280540 : Nat := 4983230072969 + 3 ^ 40 * 5280540 * 2
def baseEnd_5280540 : Nat := 2711455135292875096665245

theorem tailTrace_5280540 : CollatzResearch.WordTrace tailWord_5280540 prefixEnd_5280540 2711455135292875096665245 := by
  unfold tailWord_5280540
  simp only [CollatzResearch.WordTrace]
  refine ⟨96298558144756449638803537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128398077526341932851738049 96298558144756449638803537)
  ·
    refine ⟨72223918608567337229102653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96298558144756449638803537 72223918608567337229102653)
    ·
      refine ⟨27083969478212751460913495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72223918608567337229102653 27083969478212751460913495)
      ·
        refine ⟨40625954217319127191370243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27083969478212751460913495 40625954217319127191370243)
        ·
          refine ⟨60938931325978690787055365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40625954217319127191370243 60938931325978690787055365)
          ·
            refine ⟨11426049623621004522572881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60938931325978690787055365 11426049623621004522572881)
            ·
              refine ⟨8569537217715753391929661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11426049623621004522572881 8569537217715753391929661)
              ·
                refine ⟨3213576456643407521973623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8569537217715753391929661 3213576456643407521973623)
                ·
                  refine ⟨4820364684965111282960435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213576456643407521973623 4820364684965111282960435)
                  ·
                    refine ⟨7230547027447666924440653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4820364684965111282960435 7230547027447666924440653)
                    ·
                      refine ⟨2711455135292875096665245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7230547027447666924440653 2711455135292875096665245)
                      ·
                        rfl

theorem cell23_5280540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_5280540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280540 prefixEnd_5280540 := by exact prefixLift 5280540
  have htrace : WordTrace (prefixWord ++ tailWord_5280540) baseStart_5280540 baseEnd_5280540 := by
    simpa [prefixWord, tailWord_5280540, baseEnd_5280540] using wordTrace_append hprefix tailTrace_5280540
  have hstable : (prefixWord ++ tailWord_5280540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280540).length < 2 ^ (prefixWord ++ tailWord_5280540).sum := by decide
  have hdescent : baseEnd_5280540 < baseStart_5280540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280543 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 1, 5]
def baseStart_5280543 : Nat := 118140960795 + 5280543 * 2 ^ 59
def prefixEnd_5280543 : Nat := 4983230072969 + 3 ^ 40 * 5280543 * 2
def baseEnd_5280543 : Nat := 903818891911612861642577

theorem tailTrace_5280543 : CollatzResearch.WordTrace tailWord_5280543 prefixEnd_5280543 903818891911612861642577 := by
  unfold tailWord_5280543
  simp only [CollatzResearch.WordTrace]
  refine ⟨192597225708502030789966283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128398150472334687193310855 192597225708502030789966283)
  ·
    refine ⟨288895838562753046184949425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192597225708502030789966283 288895838562753046184949425)
    ·
      refine ⟨216671878922064784638712069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288895838562753046184949425 216671878922064784638712069)
      ·
        refine ⟨40625977297887147119758513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216671878922064784638712069 40625977297887147119758513)
        ·
          refine ⟨30469482973415360339818885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40625977297887147119758513 30469482973415360339818885)
          ·
            refine ⟨5713028057515380063716041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30469482973415360339818885 5713028057515380063716041)
            ·
              refine ⟨4284771043136535047787031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713028057515380063716041 4284771043136535047787031)
              ·
                refine ⟨6427156564704802571680547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284771043136535047787031 6427156564704802571680547)
                ·
                  refine ⟨9640734847057203857520821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6427156564704802571680547 9640734847057203857520821)
                  ·
                    refine ⟨903818891911612861642577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9640734847057203857520821 903818891911612861642577)
                    ·
                      rfl

theorem cell23_5280543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 5].length) (baseStart_5280543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280543 prefixEnd_5280543 := by exact prefixLift 5280543
  have htrace : WordTrace (prefixWord ++ tailWord_5280543) baseStart_5280543 baseEnd_5280543 := by
    simpa [prefixWord, tailWord_5280543, baseEnd_5280543] using wordTrace_append hprefix tailTrace_5280543
  have hstable : (prefixWord ++ tailWord_5280543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280543).length < 2 ^ (prefixWord ++ tailWord_5280543).sum := by decide
  have hdescent : baseEnd_5280543 < baseStart_5280543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280549 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_5280549 : Nat := 118140960795 + 5280549 * 2 ^ 59
def prefixEnd_5280549 : Nat := 4983230072969 + 3 ^ 40 * 5280549 * 2
def baseEnd_5280549 : Nat := 2711459756618765561452703

theorem tailTrace_5280549 : CollatzResearch.WordTrace tailWord_5280549 prefixEnd_5280549 2711459756618765561452703 := by
  unfold tailWord_5280549
  simp only [CollatzResearch.WordTrace]
  refine ⟨192597444546480293814684701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128398296364320195876456467 192597444546480293814684701)
  ·
    refine ⟨72224041704930110180506763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192597444546480293814684701 72224041704930110180506763)
    ·
      refine ⟨108336062557395165270760145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72224041704930110180506763 108336062557395165270760145)
      ·
        refine ⟨81252046918046373953070109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108336062557395165270760145 81252046918046373953070109)
        ·
          refine ⟨30469517594267390232401291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81252046918046373953070109 30469517594267390232401291)
          ·
            refine ⟨45704276391401085348601937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30469517594267390232401291 45704276391401085348601937)
            ·
              refine ⟨34278207293550814011451453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45704276391401085348601937 34278207293550814011451453)
              ·
                refine ⟨12854327735081555254294295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34278207293550814011451453 12854327735081555254294295)
                ·
                  refine ⟨19281491602622332881441443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12854327735081555254294295 19281491602622332881441443)
                  ·
                    refine ⟨28922237403933499322162165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19281491602622332881441443 28922237403933499322162165)
                    ·
                      refine ⟨2711459756618765561452703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28922237403933499322162165 2711459756618765561452703)
                      ·
                        rfl

theorem cell23_5280549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_5280549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280549 prefixEnd_5280549 := by exact prefixLift 5280549
  have htrace : WordTrace (prefixWord ++ tailWord_5280549) baseStart_5280549 baseEnd_5280549 := by
    simpa [prefixWord, tailWord_5280549, baseEnd_5280549] using wordTrace_append hprefix tailTrace_5280549
  have hstable : (prefixWord ++ tailWord_5280549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280549).length < 2 ^ (prefixWord ++ tailWord_5280549).sum := by decide
  have hdescent : baseEnd_5280549 < baseStart_5280549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280557 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5280557 : Nat := 118140960795 + 5280557 * 2 ^ 59
def prefixEnd_5280557 : Nat := 4983230072969 + 3 ^ 40 * 5280557 * 2
def baseEnd_5280557 : Nat := 2711463864464001530152667

theorem tailTrace_5280557 : CollatzResearch.WordTrace tailWord_5280557 prefixEnd_5280557 2711463864464001530152667 := by
  unfold tailWord_5280557
  simp only [CollatzResearch.WordTrace]
  refine ⟨192597736330451311180975925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128398490886967540787317283 192597736330451311180975925)
  ·
    refine ⟨18056037780979810423216493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192597736330451311180975925 18056037780979810423216493)
    ·
      refine ⟨6771014167867428908706185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18056037780979810423216493 6771014167867428908706185)
      ·
        refine ⟨5078260625900571681529639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6771014167867428908706185 5078260625900571681529639)
        ·
          refine ⟨7617390938850857522294459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5078260625900571681529639 7617390938850857522294459)
          ·
            refine ⟨11426086408276286283441689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7617390938850857522294459 11426086408276286283441689)
            ·
              refine ⟨8569564806207214712581267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11426086408276286283441689 8569564806207214712581267)
              ·
                refine ⟨12854347209310822068871901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8569564806207214712581267 12854347209310822068871901)
                ·
                  refine ⟨4820380203491558275826963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12854347209310822068871901 4820380203491558275826963)
                  ·
                    refine ⟨7230570305237337413740445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4820380203491558275826963 7230570305237337413740445)
                    ·
                      refine ⟨2711463864464001530152667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7230570305237337413740445 2711463864464001530152667)
                      ·
                        rfl

theorem cell23_5280557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5280557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280557 prefixEnd_5280557 := by exact prefixLift 5280557
  have htrace : WordTrace (prefixWord ++ tailWord_5280557) baseStart_5280557 baseEnd_5280557 := by
    simpa [prefixWord, tailWord_5280557, baseEnd_5280557] using wordTrace_append hprefix tailTrace_5280557
  have hstable : (prefixWord ++ tailWord_5280557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280557).length < 2 ^ (prefixWord ++ tailWord_5280557).sum := by decide
  have hdescent : baseEnd_5280557 < baseStart_5280557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280563 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 3, 2, 2]
def baseStart_5280563 : Nat := 118140960795 + 5280563 * 2 ^ 59
def prefixEnd_5280563 : Nat := 4983230072969 + 3 ^ 40 * 5280563 * 2
def baseEnd_5280563 : Nat := 2711466945347928506677639

theorem tailTrace_5280563 : CollatzResearch.WordTrace tailWord_5280563 prefixEnd_5280563 2711466945347928506677639 := by
  unfold tailWord_5280563
  simp only [CollatzResearch.WordTrace]
  refine ⟨192597955168429574205694343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128398636778953049470462895 192597955168429574205694343)
  ·
    refine ⟨288896932752644361308541515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192597955168429574205694343 288896932752644361308541515)
    ·
      refine ⟨433345399128966541962812273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288896932752644361308541515 433345399128966541962812273)
      ·
        refine ⟨325009049346724906472109205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433345399128966541962812273 325009049346724906472109205)
        ·
          refine ⟨15234799188127729990880119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 325009049346724906472109205 15234799188127729990880119)
          ·
            refine ⟨22852198782191594986320179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15234799188127729990880119 22852198782191594986320179)
            ·
              refine ⟨34278298173287392479480269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22852198782191594986320179 34278298173287392479480269)
              ·
                refine ⟨12854361814982772179805101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34278298173287392479480269 12854361814982772179805101)
                ·
                  refine ⟨4820385680618539567426913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12854361814982772179805101 4820385680618539567426913)
                  ·
                    refine ⟨3615289260463904675570185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4820385680618539567426913 3615289260463904675570185)
                    ·
                      refine ⟨2711466945347928506677639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615289260463904675570185 2711466945347928506677639)
                      ·
                        rfl

theorem cell23_5280563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 2, 2].length) (baseStart_5280563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280563 prefixEnd_5280563 := by exact prefixLift 5280563
  have htrace : WordTrace (prefixWord ++ tailWord_5280563) baseStart_5280563 baseEnd_5280563 := by
    simpa [prefixWord, tailWord_5280563, baseEnd_5280563] using wordTrace_append hprefix tailTrace_5280563
  have hstable : (prefixWord ++ tailWord_5280563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280563).length < 2 ^ (prefixWord ++ tailWord_5280563).sum := by decide
  have hdescent : baseEnd_5280563 < baseStart_5280563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280573 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_5280573 : Nat := 118140960795 + 5280573 * 2 ^ 59
def prefixEnd_5280573 : Nat := 4983230072969 + 3 ^ 40 * 5280573 * 2
def baseEnd_5280573 : Nat := 903824026718157822517531

theorem tailTrace_5280573 : CollatzResearch.WordTrace tailWord_5280573 prefixEnd_5280573 903824026718157822517531 := by
  unfold tailWord_5280573
  simp only [CollatzResearch.WordTrace]
  refine ⟨192598319898393345913558373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128398879932262230609038915 192598319898393345913558373)
  ·
    refine ⟨36112184980948752358792195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192598319898393345913558373 36112184980948752358792195)
    ·
      refine ⟨54168277471423128538188293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36112184980948752358792195 54168277471423128538188293)
      ·
        refine ⟨10156552025891836600910305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54168277471423128538188293 10156552025891836600910305)
        ·
          refine ⟨7617414019418877450682729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10156552025891836600910305 7617414019418877450682729)
          ·
            refine ⟨5713060514564158088012047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7617414019418877450682729 5713060514564158088012047)
            ·
              refine ⟨8569590771846237132018071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713060514564158088012047 8569590771846237132018071)
              ·
                refine ⟨12854386157769355698027107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8569590771846237132018071 12854386157769355698027107)
                ·
                  refine ⟨19281579236654033547040661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12854386157769355698027107 19281579236654033547040661)
                  ·
                    refine ⟨903824026718157822517531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19281579236654033547040661 903824026718157822517531)
                    ·
                      rfl

theorem cell23_5280573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_5280573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280573 prefixEnd_5280573 := by exact prefixLift 5280573
  have htrace : WordTrace (prefixWord ++ tailWord_5280573) baseStart_5280573 baseEnd_5280573 := by
    simpa [prefixWord, tailWord_5280573, baseEnd_5280573] using wordTrace_append hprefix tailTrace_5280573
  have hstable : (prefixWord ++ tailWord_5280573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280573).length < 2 ^ (prefixWord ++ tailWord_5280573).sum := by decide
  have hdescent : baseEnd_5280573 < baseStart_5280573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280636 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 5, 4, 2]
def baseStart_5280636 : Nat := 118140960795 + 5280636 * 2 ^ 59
def prefixEnd_5280636 : Nat := 4983230072969 + 3 ^ 40 * 5280636 * 2
def baseEnd_5280636 : Nat := 2711504429435706721064803

theorem tailTrace_5280636 : CollatzResearch.WordTrace tailWord_5280636 prefixEnd_5280636 2711504429435706721064803 := by
  unfold tailWord_5280636
  simp only [CollatzResearch.WordTrace]
  refine ⟨96300308848582553836550881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128400411798110071782067841 96300308848582553836550881)
  ·
    refine ⟨72225231636436915377413161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96300308848582553836550881 72225231636436915377413161)
    ·
      refine ⟨54168923727327686533059871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72225231636436915377413161 54168923727327686533059871)
      ·
        refine ⟨81253385590991529799589807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54168923727327686533059871 81253385590991529799589807)
        ·
          refine ⟨121880078386487294699384711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81253385590991529799589807 121880078386487294699384711)
          ·
            refine ⟨182820117579730942049077067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121880078386487294699384711 182820117579730942049077067)
            ·
              refine ⟨274230176369596413073615601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182820117579730942049077067 274230176369596413073615601)
              ·
                refine ⟨205672632277197309805211701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274230176369596413073615601 205672632277197309805211701)
                ·
                  refine ⟨19281809275987247794238597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205672632277197309805211701 19281809275987247794238597)
                  ·
                    refine ⟨3615339239247608961419737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19281809275987247794238597 3615339239247608961419737)
                    ·
                      refine ⟨2711504429435706721064803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615339239247608961419737 2711504429435706721064803)
                      ·
                        rfl

theorem cell23_5280636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_5280636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280636 prefixEnd_5280636 := by exact prefixLift 5280636
  have htrace : WordTrace (prefixWord ++ tailWord_5280636) baseStart_5280636 baseEnd_5280636 := by
    simpa [prefixWord, tailWord_5280636, baseEnd_5280636] using wordTrace_append hprefix tailTrace_5280636
  have hstable : (prefixWord ++ tailWord_5280636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280636).length < 2 ^ (prefixWord ++ tailWord_5280636).sum := by decide
  have hdescent : baseEnd_5280636 < baseStart_5280636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280639 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_5280639 : Nat := 118140960795 + 5280639 * 2 ^ 59
def prefixEnd_5280639 : Nat := 4983230072969 + 3 ^ 40 * 5280639 * 2
def baseEnd_5280639 : Nat := 2711505969877670209327289

theorem tailTrace_5280639 : CollatzResearch.WordTrace tailWord_5280639 prefixEnd_5280639 2711505969877670209327289 := by
  unfold tailWord_5280639
  simp only [CollatzResearch.WordTrace]
  refine ⟨192600727116154239185460971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128400484744102826123640647 192600727116154239185460971)
  ·
    refine ⟨288901090674231358778191457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192600727116154239185460971 288901090674231358778191457)
    ·
      refine ⟨216675818005673519083643593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288901090674231358778191457 216675818005673519083643593)
      ·
        refine ⟨162506863504255139312732695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216675818005673519083643593 162506863504255139312732695)
        ·
          refine ⟨243760295256382708969099043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162506863504255139312732695 243760295256382708969099043)
          ·
            refine ⟨365640442884574063453648565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243760295256382708969099043 365640442884574063453648565)
            ·
              refine ⟨34278791520428818448779553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365640442884574063453648565 34278791520428818448779553)
              ·
                refine ⟨25709093640321613836584665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34278791520428818448779553 25709093640321613836584665)
                ·
                  refine ⟨19281820230241210377438499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25709093640321613836584665 19281820230241210377438499)
                  ·
                    refine ⟨28922730345361815566157749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19281820230241210377438499 28922730345361815566157749)
                    ·
                      refine ⟨2711505969877670209327289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28922730345361815566157749 2711505969877670209327289)
                      ·
                        rfl

theorem cell23_5280639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_5280639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280639 prefixEnd_5280639 := by exact prefixLift 5280639
  have htrace : WordTrace (prefixWord ++ tailWord_5280639) baseStart_5280639 baseEnd_5280639 := by
    simpa [prefixWord, tailWord_5280639, baseEnd_5280639] using wordTrace_append hprefix tailTrace_5280639
  have hstable : (prefixWord ++ tailWord_5280639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280639).length < 2 ^ (prefixWord ++ tailWord_5280639).sum := by decide
  have hdescent : baseEnd_5280639 < baseStart_5280639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280753 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 3, 4]
def baseStart_5280753 : Nat := 118140960795 + 5280753 * 2 ^ 59
def prefixEnd_5280753 : Nat := 4983230072969 + 3 ^ 40 * 5280753 * 2
def baseEnd_5280753 : Nat := 903854835557427587767255

theorem tailTrace_5280753 : CollatzResearch.WordTrace tailWord_5280753 prefixEnd_5280753 903854835557427587767255 := by
  unfold tailWord_5280753
  simp only [CollatzResearch.WordTrace]
  refine ⟨192604885037741236655110913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128403256691827491103407275 192604885037741236655110913)
  ·
    refine ⟨144453663778305927491333185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192604885037741236655110913 144453663778305927491333185)
    ·
      refine ⟨108340247833729445618499889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144453663778305927491333185 108340247833729445618499889)
      ·
        refine ⟨81255185875297084213874917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108340247833729445618499889 81255185875297084213874917)
        ·
          refine ⟨15235347351618203290101547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81255185875297084213874917 15235347351618203290101547)
          ·
            refine ⟨22853021027427304935152321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15235347351618203290101547 22853021027427304935152321)
            ·
              refine ⟨17139765770570478701364241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22853021027427304935152321 17139765770570478701364241)
              ·
                refine ⟨12854824327927859026023181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17139765770570478701364241 12854824327927859026023181)
                ·
                  refine ⟨4820559122972947134758693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12854824327927859026023181 4820559122972947134758693)
                  ·
                    refine ⟨903854835557427587767255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820559122972947134758693 903854835557427587767255)
                    ·
                      rfl

theorem cell23_5280753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_5280753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280753 prefixEnd_5280753 := by exact prefixLift 5280753
  have htrace : WordTrace (prefixWord ++ tailWord_5280753) baseStart_5280753 baseEnd_5280753 := by
    simpa [prefixWord, tailWord_5280753, baseEnd_5280753] using wordTrace_append hprefix tailTrace_5280753
  have hstable : (prefixWord ++ tailWord_5280753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280753).length < 2 ^ (prefixWord ++ tailWord_5280753).sum := by decide
  have hdescent : baseEnd_5280753 < baseStart_5280753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280759 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_5280759 : Nat := 118140960795 + 5280759 * 2 ^ 59
def prefixEnd_5280759 : Nat := 4983230072969 + 3 ^ 40 * 5280759 * 2
def baseEnd_5280759 : Nat := 2711567587556209739826737

theorem tailTrace_5280759 : CollatzResearch.WordTrace tailWord_5280759 prefixEnd_5280759 2711567587556209739826737 := by
  unfold tailWord_5280759
  simp only [CollatzResearch.WordTrace]
  refine ⟨192605103875719499679829331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128403402583812999786552887 192605103875719499679829331)
  ·
    refine ⟨288907655813579249519743997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192605103875719499679829331 288907655813579249519743997)
    ·
      refine ⟨108340370930092218569903999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288907655813579249519743997 108340370930092218569903999)
      ·
        refine ⟨162510556395138327854855999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108340370930092218569903999 162510556395138327854855999)
        ·
          refine ⟨243765834592707491782283999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162510556395138327854855999 243765834592707491782283999)
          ·
            refine ⟨365648751889061237673425999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243765834592707491782283999 365648751889061237673425999)
            ·
              refine ⟨548473127833591856510138999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365648751889061237673425999 548473127833591856510138999)
              ·
                refine ⟨822709691750387784765208499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548473127833591856510138999 822709691750387784765208499)
                ·
                  refine ⟨1234064537625581677147812749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822709691750387784765208499 1234064537625581677147812749)
                  ·
                    refine ⟨462774201609593128930429781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1234064537625581677147812749 462774201609593128930429781)
                    ·
                      refine ⟨2711567587556209739826737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 462774201609593128930429781 2711567587556209739826737)
                      ·
                        rfl

theorem cell23_5280759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_5280759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280759 prefixEnd_5280759 := by exact prefixLift 5280759
  have htrace : WordTrace (prefixWord ++ tailWord_5280759) baseStart_5280759 baseEnd_5280759 := by
    simpa [prefixWord, tailWord_5280759, baseEnd_5280759] using wordTrace_append hprefix tailTrace_5280759
  have hstable : (prefixWord ++ tailWord_5280759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280759).length < 2 ^ (prefixWord ++ tailWord_5280759).sum := by decide
  have hdescent : baseEnd_5280759 < baseStart_5280759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280800 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 6]
def baseStart_5280800 : Nat := 118140960795 + 5280800 * 2 ^ 59
def prefixEnd_5280800 : Nat := 4983230072969 + 3 ^ 40 * 5280800 * 2
def baseEnd_5280800 : Nat := 301287626695893786601561

theorem tailTrace_5280800 : CollatzResearch.WordTrace tailWord_5280800 prefixEnd_5280800 301287626695893786601561 := by
  unfold tailWord_5280800
  simp only [CollatzResearch.WordTrace]
  refine ⟨96303299634285481841035927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128404399512380642454714569 96303299634285481841035927)
  ·
    refine ⟨144454949451428222761553891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96303299634285481841035927 144454949451428222761553891)
    ·
      refine ⟨216682424177142334142330837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144454949451428222761553891 216682424177142334142330837)
      ·
        refine ⟨5078494316651773456460879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 216682424177142334142330837 5078494316651773456460879)
        ·
          refine ⟨7617741474977660184691319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5078494316651773456460879 7617741474977660184691319)
          ·
            refine ⟨11426612212466490277036979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7617741474977660184691319 11426612212466490277036979)
            ·
              refine ⟨17139918318699735415555469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11426612212466490277036979 17139918318699735415555469)
              ·
                refine ⟨6427469369512400780833301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17139918318699735415555469 6427469369512400780833301)
                ·
                  refine ⟨301287626695893786601561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6427469369512400780833301 301287626695893786601561)
                  ·
                    rfl

theorem cell23_5280800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 6].length) (baseStart_5280800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280800 prefixEnd_5280800 := by exact prefixLift 5280800
  have htrace : WordTrace (prefixWord ++ tailWord_5280800) baseStart_5280800 baseEnd_5280800 := by
    simpa [prefixWord, tailWord_5280800, baseEnd_5280800] using wordTrace_append hprefix tailTrace_5280800
  have hstable : (prefixWord ++ tailWord_5280800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280800).length < 2 ^ (prefixWord ++ tailWord_5280800).sum := by decide
  have hdescent : baseEnd_5280800 < baseStart_5280800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280826 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 3, 6]
def baseStart_5280826 : Nat := 118140960795 + 5280826 * 2 ^ 59
def prefixEnd_5280826 : Nat := 4983230072969 + 3 ^ 40 * 5280826 * 2
def baseEnd_5280826 : Nat := 903867330253353659229643

theorem tailTrace_5280826 : CollatzResearch.WordTrace tailWord_5280826 prefixEnd_5280826 903867330253353659229643 := by
  unfold tailWord_5280826
  simp only [CollatzResearch.WordTrace]
  refine ⟨48151886891619192530629583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128405031710984513415012221 48151886891619192530629583)
  ·
    refine ⟨72227830337428788795944375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48151886891619192530629583 72227830337428788795944375)
    ·
      refine ⟨108341745506143183193916563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72227830337428788795944375 108341745506143183193916563)
      ·
        refine ⟨162512618259214774790874845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108341745506143183193916563 162512618259214774790874845)
        ·
          refine ⟨60942231847205540546578067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162512618259214774790874845 60942231847205540546578067)
          ·
            refine ⟨91413347770808310819867101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60942231847205540546578067 91413347770808310819867101)
            ·
              refine ⟨34280005414053116557450163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91413347770808310819867101 34280005414053116557450163)
              ·
                refine ⟨51420008121079674836175245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34280005414053116557450163 51420008121079674836175245)
                ·
                  refine ⟨19282503045404878063565717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51420008121079674836175245 19282503045404878063565717)
                  ·
                    refine ⟨903867330253353659229643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19282503045404878063565717 903867330253353659229643)
                    ·
                      rfl

theorem cell23_5280826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_5280826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280826 prefixEnd_5280826 := by exact prefixLift 5280826
  have htrace : WordTrace (prefixWord ++ tailWord_5280826) baseStart_5280826 baseEnd_5280826 := by
    simpa [prefixWord, tailWord_5280826, baseEnd_5280826] using wordTrace_append hprefix tailTrace_5280826
  have hstable : (prefixWord ++ tailWord_5280826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280826).length < 2 ^ (prefixWord ++ tailWord_5280826).sum := by decide
  have hdescent : baseEnd_5280826 < baseStart_5280826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280853 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_5280853 : Nat := 118140960795 + 5280853 * 2 ^ 59
def prefixEnd_5280853 : Nat := 4983230072969 + 3 ^ 40 * 5280853 * 2
def baseEnd_5280853 : Nat := 2711615854737732372051305

theorem tailTrace_5280853 : CollatzResearch.WordTrace tailWord_5280853 prefixEnd_5280853 2711615854737732372051305 := by
  unfold tailWord_5280853
  simp only [CollatzResearch.WordTrace]
  refine ⟨192608532337378953733751213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128405688224919302489167475 192608532337378953733751213)
  ·
    refine ⟨72228199626517107650156705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192608532337378953733751213 72228199626517107650156705)
    ·
      refine ⟨54171149719887830737617529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72228199626517107650156705 54171149719887830737617529)
      ·
        refine ⟨40628362289915873053213147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54171149719887830737617529 40628362289915873053213147)
        ·
          refine ⟨60942543434873809579819721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40628362289915873053213147 60942543434873809579819721)
          ·
            refine ⟨45706907576155357184864791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60942543434873809579819721 45706907576155357184864791)
            ·
              refine ⟨68560361364233035777297187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45706907576155357184864791 68560361364233035777297187)
              ·
                refine ⟨102840542046349553665945781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68560361364233035777297187 102840542046349553665945781)
                ·
                  refine ⟨9641300816845270656182417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102840542046349553665945781 9641300816845270656182417)
                  ·
                    refine ⟨7230975612633952992136813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9641300816845270656182417 7230975612633952992136813)
                    ·
                      refine ⟨2711615854737732372051305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7230975612633952992136813 2711615854737732372051305)
                      ·
                        rfl

theorem cell23_5280853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_5280853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280853 prefixEnd_5280853 := by exact prefixLift 5280853
  have htrace : WordTrace (prefixWord ++ tailWord_5280853) baseStart_5280853 baseEnd_5280853 := by
    simpa [prefixWord, tailWord_5280853, baseEnd_5280853] using wordTrace_append hprefix tailTrace_5280853
  have hstable : (prefixWord ++ tailWord_5280853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280853).length < 2 ^ (prefixWord ++ tailWord_5280853).sum := by decide
  have hdescent : baseEnd_5280853 < baseStart_5280853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280860 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_5280860 : Nat := 118140960795 + 5280860 * 2 ^ 59
def prefixEnd_5280860 : Nat := 4983230072969 + 3 ^ 40 * 5280860 * 2
def baseEnd_5280860 : Nat := 903873149700771281554591

theorem tailTrace_5280860 : CollatzResearch.WordTrace tailWord_5280860 prefixEnd_5280860 903873149700771281554591 := by
  unfold tailWord_5280860
  simp only [CollatzResearch.WordTrace]
  refine ⟨96304393824176796964628017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128405858432235729286170689 96304393824176796964628017)
  ·
    refine ⟨72228295368132597723471013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96304393824176796964628017 72228295368132597723471013)
    ·
      refine ⟨13542805381524862073150815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72228295368132597723471013 13542805381524862073150815)
      ·
        refine ⟨20314208072287293109726223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13542805381524862073150815 20314208072287293109726223)
        ·
          refine ⟨30471312108430939664589335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20314208072287293109726223 30471312108430939664589335)
          ·
            refine ⟨45706968162646409496884003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30471312108430939664589335 45706968162646409496884003)
            ·
              refine ⟨68560452243969614245326005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45706968162646409496884003 68560452243969614245326005)
              ·
                refine ⟨6427542397872151335499313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68560452243969614245326005 6427542397872151335499313)
                ·
                  refine ⟨4820656798404113501624485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6427542397872151335499313 4820656798404113501624485)
                  ·
                    refine ⟨903873149700771281554591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820656798404113501624485 903873149700771281554591)
                    ·
                      rfl

theorem cell23_5280860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_5280860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280860 prefixEnd_5280860 := by exact prefixLift 5280860
  have htrace : WordTrace (prefixWord ++ tailWord_5280860) baseStart_5280860 baseEnd_5280860 := by
    simpa [prefixWord, tailWord_5280860, baseEnd_5280860] using wordTrace_append hprefix tailTrace_5280860
  have hstable : (prefixWord ++ tailWord_5280860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280860).length < 2 ^ (prefixWord ++ tailWord_5280860).sum := by decide
  have hdescent : baseEnd_5280860 < baseStart_5280860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280863 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 4]
def baseStart_5280863 : Nat := 118140960795 + 5280863 * 2 ^ 59
def prefixEnd_5280863 : Nat := 4983230072969 + 3 ^ 40 * 5280863 * 2
def baseEnd_5280863 : Nat := 2711620989544277332926259

theorem tailTrace_5280863 : CollatzResearch.WordTrace tailWord_5280863 prefixEnd_5280863 2711620989544277332926259 := by
  unfold tailWord_5280863
  simp only [CollatzResearch.WordTrace]
  refine ⟨192608897067342725441615243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128405931378228483627743495 192608897067342725441615243)
  ·
    refine ⟨288913345601014088162422865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192608897067342725441615243 288913345601014088162422865)
    ·
      refine ⟨216685009200760566121817149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288913345601014088162422865 216685009200760566121817149)
      ·
        refine ⟨81256878450285212295681431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216685009200760566121817149 81256878450285212295681431)
        ·
          refine ⟨121885317675427818443522147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81256878450285212295681431 121885317675427818443522147)
          ·
            refine ⟨182827976513141727665283221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121885317675427818443522147 182827976513141727665283221)
            ·
              refine ⟨8570061399053518484310151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182827976513141727665283221 8570061399053518484310151)
              ·
                refine ⟨12855092098580277726465227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8570061399053518484310151 12855092098580277726465227)
                ·
                  refine ⟨19282638147870416589697841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12855092098580277726465227 19282638147870416589697841)
                  ·
                    refine ⟨14461978610902812442273381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19282638147870416589697841 14461978610902812442273381)
                    ·
                      refine ⟨2711620989544277332926259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14461978610902812442273381 2711620989544277332926259)
                      ·
                        rfl

theorem cell23_5280863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_5280863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280863 prefixEnd_5280863 := by exact prefixLift 5280863
  have htrace : WordTrace (prefixWord ++ tailWord_5280863) baseStart_5280863 baseEnd_5280863 := by
    simpa [prefixWord, tailWord_5280863, baseEnd_5280863] using wordTrace_append hprefix tailTrace_5280863
  have hstable : (prefixWord ++ tailWord_5280863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280863).length < 2 ^ (prefixWord ++ tailWord_5280863).sum := by decide
  have hdescent : baseEnd_5280863 < baseStart_5280863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280873 : List Nat := [1, 2, 1, 1, 1, 7, 3, 7]
def baseStart_5280873 : Nat := 118140960795 + 5280873 * 2 ^ 59
def prefixEnd_5280873 : Nat := 4983230072969 + 3 ^ 40 * 5280873 * 2
def baseEnd_5280873 : Nat := 100430597198178603474119

theorem tailTrace_5280873 : CollatzResearch.WordTrace tailWord_5280873 prefixEnd_5280873 100430597198178603474119 := by
  unfold tailWord_5280873
  simp only [CollatzResearch.WordTrace]
  refine ⟨192609261797306497149479273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128406174531537664766319515 192609261797306497149479273)
  ·
    refine ⟨144456946347979872862109455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192609261797306497149479273 144456946347979872862109455)
    ·
      refine ⟨216685419521969809293164183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144456946347979872862109455 216685419521969809293164183)
      ·
        refine ⟨325028129282954713939746275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216685419521969809293164183 325028129282954713939746275)
        ·
          refine ⟨487542193924432070909619413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325028129282954713939746275 487542193924432070909619413)
          ·
            refine ⟨11426770170103876661944205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 487542193924432070909619413 11426770170103876661944205)
            ·
              refine ⟨4285038813788953748229077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11426770170103876661944205 4285038813788953748229077)
              ·
                refine ⟨100430597198178603474119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4285038813788953748229077 100430597198178603474119)
                ·
                  rfl

theorem cell23_5280873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 7].length) (baseStart_5280873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280873 prefixEnd_5280873 := by exact prefixLift 5280873
  have htrace : WordTrace (prefixWord ++ tailWord_5280873) baseStart_5280873 baseEnd_5280873 := by
    simpa [prefixWord, tailWord_5280873, baseEnd_5280873] using wordTrace_append hprefix tailTrace_5280873
  have hstable : (prefixWord ++ tailWord_5280873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280873).length < 2 ^ (prefixWord ++ tailWord_5280873).sum := by decide
  have hdescent : baseEnd_5280873 < baseStart_5280873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5280957 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_5280957 : Nat := 118140960795 + 5280957 * 2 ^ 59
def prefixEnd_5280957 : Nat := 4983230072969 + 3 ^ 40 * 5280957 * 2
def baseEnd_5280957 : Nat := 2711669256725799965150827

theorem tailTrace_5280957 : CollatzResearch.WordTrace tailWord_5280957 prefixEnd_5280957 2711669256725799965150827 := by
  unfold tailWord_5280957
  simp only [CollatzResearch.WordTrace]
  refine ⟨192612325529002179495537125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128408217019334786330358083 192612325529002179495537125)
  ·
    refine ⟨36114811036687908655413211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192612325529002179495537125 36114811036687908655413211)
    ·
      refine ⟨54172216555031862983119817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36114811036687908655413211 54172216555031862983119817)
      ·
        refine ⟨40629162416273897237339863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54172216555031862983119817 40629162416273897237339863)
        ·
          refine ⟨60943743624410845856009795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40629162416273897237339863 60943743624410845856009795)
          ·
            refine ⟨91415615436616268784014693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60943743624410845856009795 91415615436616268784014693)
            ·
              refine ⟨17140427894365550397002755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91415615436616268784014693 17140427894365550397002755)
              ·
                refine ⟨25710641841548325595504133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17140427894365550397002755 25710641841548325595504133)
                ·
                  refine ⟨4820745345290311049157025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25710641841548325595504133 4820745345290311049157025)
                  ·
                    refine ⟨3615559008967733286867769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4820745345290311049157025 3615559008967733286867769)
                    ·
                      refine ⟨2711669256725799965150827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615559008967733286867769 2711669256725799965150827)
                      ·
                        rfl

theorem cell23_5280957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_5280957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5280957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5280957 prefixEnd_5280957 := by exact prefixLift 5280957
  have htrace : WordTrace (prefixWord ++ tailWord_5280957) baseStart_5280957 baseEnd_5280957 := by
    simpa [prefixWord, tailWord_5280957, baseEnd_5280957] using wordTrace_append hprefix tailTrace_5280957
  have hstable : (prefixWord ++ tailWord_5280957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5280957).length < 2 ^ (prefixWord ++ tailWord_5280957).sum := by decide
  have hdescent : baseEnd_5280957 < baseStart_5280957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5280957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281003 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5]
def baseStart_5281003 : Nat := 118140960795 + 5281003 * 2 ^ 59
def prefixEnd_5281003 : Nat := 4983230072969 + 3 ^ 40 * 5281003 * 2
def baseEnd_5281003 : Nat := 2711692876835906785175615

theorem tailTrace_5281003 : CollatzResearch.WordTrace tailWord_5281003 prefixEnd_5281003 2711692876835906785175615 := by
  unfold tailWord_5281003
  simp only [CollatzResearch.WordTrace]
  refine ⟨192614003286835529351711663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128409335524557019567807775 192614003286835529351711663)
  ·
    refine ⟨288921004930253294027567495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192614003286835529351711663 288921004930253294027567495)
    ·
      refine ⟨433381507395379941041351243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288921004930253294027567495 433381507395379941041351243)
      ·
        refine ⟨650072261093069911562026865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433381507395379941041351243 650072261093069911562026865)
        ·
          refine ⟨487554195819802433671520149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650072261093069911562026865 487554195819802433671520149)
          ·
            refine ⟨22854102929053239078352507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 487554195819802433671520149 22854102929053239078352507)
            ·
              refine ⟨34281154393579858617528761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22854102929053239078352507 34281154393579858617528761)
              ·
                refine ⟨25710865795184893963146571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34281154393579858617528761 25710865795184893963146571)
                ·
                  refine ⟨38566298692777340944719857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25710865795184893963146571 38566298692777340944719857)
                  ·
                    refine ⟨28924724019583005708539893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38566298692777340944719857 28924724019583005708539893)
                    ·
                      refine ⟨2711692876835906785175615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28924724019583005708539893 2711692876835906785175615)
                      ·
                        rfl

theorem cell23_5281003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_5281003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281003 prefixEnd_5281003 := by exact prefixLift 5281003
  have htrace : WordTrace (prefixWord ++ tailWord_5281003) baseStart_5281003 baseEnd_5281003 := by
    simpa [prefixWord, tailWord_5281003, baseEnd_5281003] using wordTrace_append hprefix tailTrace_5281003
  have hstable : (prefixWord ++ tailWord_5281003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281003).length < 2 ^ (prefixWord ++ tailWord_5281003).sum := by decide
  have hdescent : baseEnd_5281003 < baseStart_5281003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281074 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_5281074 : Nat := 118140960795 + 5281074 * 2 ^ 59
def prefixEnd_5281074 : Nat := 4983230072969 + 3 ^ 40 * 5281074 * 2
def baseEnd_5281074 : Nat := 903909777987458669129263

theorem tailTrace_5281074 : CollatzResearch.WordTrace tailWord_5281074 prefixEnd_5281074 903909777987458669129263 := by
  unfold tailWord_5281074
  simp only [CollatzResearch.WordTrace]
  refine ⟨48154148217394577119386569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128411061913052205651697517 48154148217394577119386569)
  ·
    refine ⟨36115611163045932839539927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48154148217394577119386569 36115611163045932839539927)
    ·
      refine ⟨54173416744568899259309891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36115611163045932839539927 54173416744568899259309891)
      ·
        refine ⟨81260125116853348888964837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54173416744568899259309891 81260125116853348888964837)
        ·
          refine ⟨15236273459410002916680907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81260125116853348888964837 15236273459410002916680907)
          ·
            refine ⟨22854410189115004375021361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15236273459410002916680907 22854410189115004375021361)
            ·
              refine ⟨17140807641836253281266021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22854410189115004375021361 17140807641836253281266021)
              ·
                refine ⟨3213901432844297490237379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17140807641836253281266021 3213901432844297490237379)
                ·
                  refine ⟨4820852149266446235356069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213901432844297490237379 4820852149266446235356069)
                  ·
                    refine ⟨903909777987458669129263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820852149266446235356069 903909777987458669129263)
                    ·
                      rfl

theorem cell23_5281074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_5281074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281074 prefixEnd_5281074 := by exact prefixLift 5281074
  have htrace : WordTrace (prefixWord ++ tailWord_5281074) baseStart_5281074 baseEnd_5281074 := by
    simpa [prefixWord, tailWord_5281074, baseEnd_5281074] using wordTrace_append hprefix tailTrace_5281074
  have hstable : (prefixWord ++ tailWord_5281074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281074).length < 2 ^ (prefixWord ++ tailWord_5281074).sum := by decide
  have hdescent : baseEnd_5281074 < baseStart_5281074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281087 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 6]
def baseStart_5281087 : Nat := 118140960795 + 5281087 * 2 ^ 59
def prefixEnd_5281087 : Nat := 4983230072969 + 3 ^ 40 * 5281087 * 2
def baseEnd_5281087 : Nat := 301304001023431606280581

theorem tailTrace_5281087 : CollatzResearch.WordTrace tailWord_5281087 prefixEnd_5281087 301304001023431606280581 := by
  unfold tailWord_5281087
  simp only [CollatzResearch.WordTrace]
  refine ⟨192617067018531211697769515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128411378012354141131846343 192617067018531211697769515)
  ·
    refine ⟨288925600527796817546654273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192617067018531211697769515 288925600527796817546654273)
    ·
      refine ⟨216694200395847613159990705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288925600527796817546654273 216694200395847613159990705)
      ·
        refine ⟨162520650296885709869993029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216694200395847613159990705 162520650296885709869993029)
        ·
          refine ⟨30472621930666070600623693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162520650296885709869993029 30472621930666070600623693)
          ·
            refine ⟨11427233223999776475233885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30472621930666070600623693 11427233223999776475233885)
            ·
              refine ⟨4285212458999916178212707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11427233223999776475233885 4285212458999916178212707)
              ·
                refine ⟨6427818688499874267319061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4285212458999916178212707 6427818688499874267319061)
                ·
                  refine ⟨301304001023431606280581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6427818688499874267319061 301304001023431606280581)
                  ·
                    rfl

theorem cell23_5281087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 6].length) (baseStart_5281087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281087 prefixEnd_5281087 := by exact prefixLift 5281087
  have htrace : WordTrace (prefixWord ++ tailWord_5281087) baseStart_5281087 baseEnd_5281087 := by
    simpa [prefixWord, tailWord_5281087, baseEnd_5281087] using wordTrace_append hprefix tailTrace_5281087
  have hstable : (prefixWord ++ tailWord_5281087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281087).length < 2 ^ (prefixWord ++ tailWord_5281087).sum := by decide
  have hdescent : baseEnd_5281087 < baseStart_5281087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281093 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_5281093 : Nat := 118140960795 + 5281093 * 2 ^ 59
def prefixEnd_5281093 : Nat := 4983230072969 + 3 ^ 40 * 5281093 * 2
def baseEnd_5281093 : Nat := 2711739090094811433050201

theorem tailTrace_5281093 : CollatzResearch.WordTrace tailWord_5281093 prefixEnd_5281093 2711739090094811433050201 := by
  unfold tailWord_5281093
  simp only [CollatzResearch.WordTrace]
  refine ⟨192617285856509474722487933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128411523904339649814991955 192617285856509474722487933)
  ·
    refine ⟨72231482196191053020932975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192617285856509474722487933 72231482196191053020932975)
    ·
      refine ⟨108347223294286579531399463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72231482196191053020932975 108347223294286579531399463)
      ·
        refine ⟨162520834941429869297099195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108347223294286579531399463 162520834941429869297099195)
        ·
          refine ⟨243781252412144803945648793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162520834941429869297099195 243781252412144803945648793)
          ·
            refine ⟨182835939309108602959236595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243781252412144803945648793 182835939309108602959236595)
            ·
              refine ⟨274253908963662904438854893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182835939309108602959236595 274253908963662904438854893)
              ·
                refine ⟨102845215861373589164570585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274253908963662904438854893 102845215861373589164570585)
                ·
                  refine ⟨77133911896030191873427939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102845215861373589164570585 77133911896030191873427939)
                  ·
                    refine ⟨115700867844045287810141909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77133911896030191873427939 115700867844045287810141909)
                    ·
                      refine ⟨2711739090094811433050201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115700867844045287810141909 2711739090094811433050201)
                      ·
                        rfl

theorem cell23_5281093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_5281093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281093 prefixEnd_5281093 := by exact prefixLift 5281093
  have htrace : WordTrace (prefixWord ++ tailWord_5281093) baseStart_5281093 baseEnd_5281093 := by
    simpa [prefixWord, tailWord_5281093, baseEnd_5281093] using wordTrace_append hprefix tailTrace_5281093
  have hstable : (prefixWord ++ tailWord_5281093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281093).length < 2 ^ (prefixWord ++ tailWord_5281093).sum := by decide
  have hdescent : baseEnd_5281093 < baseStart_5281093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281097 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 3]
def baseStart_5281097 : Nat := 118140960795 + 5281097 * 2 ^ 59
def prefixEnd_5281097 : Nat := 4983230072969 + 3 ^ 40 * 5281097 * 2
def baseEnd_5281097 : Nat := 2711741144017429417400183

theorem tailTrace_5281097 : CollatzResearch.WordTrace tailWord_5281097 prefixEnd_5281097 2711741144017429417400183 := by
  unfold tailWord_5281097
  simp only [CollatzResearch.WordTrace]
  refine ⟨192617431748494983405633545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128411621165663322270422363 192617431748494983405633545)
  ·
    refine ⟨144463073811371237554225159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192617431748494983405633545 144463073811371237554225159)
    ·
      refine ⟨216694610717056856331337739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144463073811371237554225159 216694610717056856331337739)
      ·
        refine ⟨325041916075585284497006609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216694610717056856331337739 325041916075585284497006609)
        ·
          refine ⟨243781437056688963372754957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325041916075585284497006609 243781437056688963372754957)
          ·
            refine ⟨91418038896258361264783109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243781437056688963372754957 91418038896258361264783109)
            ·
              refine ⟨17140882293048442737146833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91418038896258361264783109 17140882293048442737146833)
              ·
                refine ⟨12855661719786332052860125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17140882293048442737146833 12855661719786332052860125)
                ·
                  refine ⟨4820873144919874519822547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12855661719786332052860125 4820873144919874519822547)
                  ·
                    refine ⟨7231309717379811779733821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4820873144919874519822547 7231309717379811779733821)
                    ·
                      refine ⟨2711741144017429417400183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7231309717379811779733821 2711741144017429417400183)
                      ·
                        rfl

theorem cell23_5281097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_5281097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281097 prefixEnd_5281097 := by exact prefixLift 5281097
  have htrace : WordTrace (prefixWord ++ tailWord_5281097) baseStart_5281097 baseEnd_5281097 := by
    simpa [prefixWord, tailWord_5281097, baseEnd_5281097] using wordTrace_append hprefix tailTrace_5281097
  have hstable : (prefixWord ++ tailWord_5281097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281097).length < 2 ^ (prefixWord ++ tailWord_5281097).sum := by decide
  have hdescent : baseEnd_5281097 < baseStart_5281097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281107 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 2, 3, 2]
def baseStart_5281107 : Nat := 118140960795 + 5281107 * 2 ^ 59
def prefixEnd_5281107 : Nat := 4983230072969 + 3 ^ 40 * 5281107 * 2
def baseEnd_5281107 : Nat := 2711746278823974378275137

theorem tailTrace_5281107 : CollatzResearch.WordTrace tailWord_5281107 prefixEnd_5281107 2711746278823974378275137 := by
  unfold tailWord_5281107
  simp only [CollatzResearch.WordTrace]
  refine ⟨192617796478458755113497575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128411864318972503408998383 192617796478458755113497575)
  ·
    refine ⟨288926694717688132670246363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192617796478458755113497575 288926694717688132670246363)
    ·
      refine ⟨433390042076532199005369545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288926694717688132670246363 433390042076532199005369545)
      ·
        refine ⟨325042531557399149254027159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433390042076532199005369545 325042531557399149254027159)
        ·
          refine ⟨487563797336098723881040739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325042531557399149254027159 487563797336098723881040739)
          ·
            refine ⟨731345696004148085821561109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487563797336098723881040739 731345696004148085821561109)
            ·
              refine ⟨34281829500194441522885677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 731345696004148085821561109 34281829500194441522885677)
              ·
                refine ⟨12855686062572915571082129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34281829500194441522885677 12855686062572915571082129)
                ·
                  refine ⟨9641764546929686678311597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12855686062572915571082129 9641764546929686678311597)
                  ·
                    refine ⟨3615661705098632504366849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9641764546929686678311597 3615661705098632504366849)
                    ·
                      refine ⟨2711746278823974378275137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615661705098632504366849 2711746278823974378275137)
                      ·
                        rfl

theorem cell23_5281107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3, 2].length) (baseStart_5281107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281107 prefixEnd_5281107 := by exact prefixLift 5281107
  have htrace : WordTrace (prefixWord ++ tailWord_5281107) baseStart_5281107 baseEnd_5281107 := by
    simpa [prefixWord, tailWord_5281107, baseEnd_5281107] using wordTrace_append hprefix tailTrace_5281107
  have hstable : (prefixWord ++ tailWord_5281107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281107).length < 2 ^ (prefixWord ++ tailWord_5281107).sum := by decide
  have hdescent : baseEnd_5281107 < baseStart_5281107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281124 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_5281124 : Nat := 118140960795 + 5281124 * 2 ^ 59
def prefixEnd_5281124 : Nat := 4983230072969 + 3 ^ 40 * 5281124 * 2
def baseEnd_5281124 : Nat := 2711755007995100811762559

theorem tailTrace_5281124 : CollatzResearch.WordTrace tailWord_5281124 prefixEnd_5281124 2711755007995100811762559 := by
  unfold tailWord_5281124
  simp only [CollatzResearch.WordTrace]
  refine ⟨96309208259698583508433213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128412277679598111344577617 96309208259698583508433213)
  ·
    refine ⟨36115953097386968815662455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96309208259698583508433213 36115953097386968815662455)
    ·
      refine ⟨54173929646080453223493683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36115953097386968815662455 54173929646080453223493683)
      ·
        refine ⟨81260894469120679835240525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54173929646080453223493683 81260894469120679835240525)
        ·
          refine ⟨30472835425920254938215197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81260894469120679835240525 30472835425920254938215197)
          ·
            refine ⟨11427313284720095601830699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30472835425920254938215197 11427313284720095601830699)
            ·
              refine ⟨17140969927080143402746049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11427313284720095601830699 17140969927080143402746049)
              ·
                refine ⟨12855727445310107552059537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17140969927080143402746049 12855727445310107552059537)
                ·
                  refine ⟨9641795583982580664044653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12855727445310107552059537 9641795583982580664044653)
                  ·
                    refine ⟨3615673343993467749016745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9641795583982580664044653 3615673343993467749016745)
                    ·
                      refine ⟨2711755007995100811762559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615673343993467749016745 2711755007995100811762559)
                      ·
                        rfl

theorem cell23_5281124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_5281124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281124 prefixEnd_5281124 := by exact prefixLift 5281124
  have htrace : WordTrace (prefixWord ++ tailWord_5281124) baseStart_5281124 baseEnd_5281124 := by
    simpa [prefixWord, tailWord_5281124, baseEnd_5281124] using wordTrace_append hprefix tailTrace_5281124
  have hstable : (prefixWord ++ tailWord_5281124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281124).length < 2 ^ (prefixWord ++ tailWord_5281124).sum := by decide
  have hdescent : baseEnd_5281124 < baseStart_5281124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281147 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 2, 4]
def baseStart_5281147 : Nat := 118140960795 + 5281147 * 2 ^ 59
def prefixEnd_5281147 : Nat := 4983230072969 + 3 ^ 40 * 5281147 * 2
def baseEnd_5281147 : Nat := 903922272683384740591651

theorem tailTrace_5281147 : CollatzResearch.WordTrace tailWord_5281147 prefixEnd_5281147 903922272683384740591651 := by
  unfold tailWord_5281147
  simp only [CollatzResearch.WordTrace]
  refine ⟨192619255398313841944953695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128412836932209227963302463 192619255398313841944953695)
  ·
    refine ⟨288928883097470762917430543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192619255398313841944953695 288928883097470762917430543)
    ·
      refine ⟨433393324646206144376145815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288928883097470762917430543 433393324646206144376145815)
      ·
        refine ⟨650089986969309216564218723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433393324646206144376145815 650089986969309216564218723)
        ·
          refine ⟨975134980453963824846328085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650089986969309216564218723 975134980453963824846328085)
          ·
            refine ⟨45709452208779554289671629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 975134980453963824846328085 45709452208779554289671629)
            ·
              refine ⟨17141044578292332858626861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45709452208779554289671629 17141044578292332858626861)
              ·
                refine ⟨6427891716859624821985073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17141044578292332858626861 6427891716859624821985073)
                ·
                  refine ⟨4820918787644718616488805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6427891716859624821985073 4820918787644718616488805)
                  ·
                    refine ⟨903922272683384740591651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4820918787644718616488805 903922272683384740591651)
                    ·
                      rfl

theorem cell23_5281147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 4].length) (baseStart_5281147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281147 prefixEnd_5281147 := by exact prefixLift 5281147
  have htrace : WordTrace (prefixWord ++ tailWord_5281147) baseStart_5281147 baseEnd_5281147 := by
    simpa [prefixWord, tailWord_5281147, baseEnd_5281147] using wordTrace_append hprefix tailTrace_5281147
  have hstable : (prefixWord ++ tailWord_5281147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281147).length < 2 ^ (prefixWord ++ tailWord_5281147).sum := by decide
  have hdescent : baseEnd_5281147 < baseStart_5281147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281160 : List Nat := [2, 1, 3, 3, 1, 2, 2, 9]
def baseStart_5281160 : Nat := 118140960795 + 5281160 * 2 ^ 59
def prefixEnd_5281160 : Nat := 4983230072969 + 3 ^ 40 * 5281160 * 2
def baseEnd_5281160 : Nat := 100436055307357876700459

theorem tailTrace_5281160 : CollatzResearch.WordTrace tailWord_5281160 prefixEnd_5281160 100436055307357876700459 := by
  unfold tailWord_5281160
  simp only [CollatzResearch.WordTrace]
  refine ⟨96309864773633372582588467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128413153031511163443451289 96309864773633372582588467)
  ·
    refine ⟨144464797160450058873882701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96309864773633372582588467 144464797160450058873882701)
    ·
      refine ⟨54174298935168772077706013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144464797160450058873882701 54174298935168772077706013)
      ·
        refine ⟨20315362100688289529139755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54174298935168772077706013 20315362100688289529139755)
        ·
          refine ⟨30473043151032434293709633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20315362100688289529139755 30473043151032434293709633)
          ·
            refine ⟨22854782363274325720282225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30473043151032434293709633 22854782363274325720282225)
            ·
              refine ⟨17141086772455744290211669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22854782363274325720282225 17141086772455744290211669)
              ·
                refine ⟨100436055307357876700459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17141086772455744290211669 100436055307357876700459)
                ·
                  rfl

theorem cell23_5281160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 9].length) (baseStart_5281160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281160 prefixEnd_5281160 := by exact prefixLift 5281160
  have htrace : WordTrace (prefixWord ++ tailWord_5281160) baseStart_5281160 baseEnd_5281160 := by
    simpa [prefixWord, tailWord_5281160, baseEnd_5281160] using wordTrace_append hprefix tailTrace_5281160
  have hstable : (prefixWord ++ tailWord_5281160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281160).length < 2 ^ (prefixWord ++ tailWord_5281160).sum := by decide
  have hdescent : baseEnd_5281160 < baseStart_5281160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281182 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_5281182 : Nat := 118140960795 + 5281182 * 2 ^ 59
def prefixEnd_5281182 : Nat := 4983230072969 + 3 ^ 40 * 5281182 * 2
def baseEnd_5281182 : Nat := 2711784789873061584837293

theorem tailTrace_5281182 : CollatzResearch.WordTrace tailWord_5281182 prefixEnd_5281182 2711784789873061584837293 := by
  unfold tailWord_5281182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077566494148380365309725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128413687968791361948318533 24077566494148380365309725)
  ·
    refine ⟨9029087435305642636991147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24077566494148380365309725 9029087435305642636991147)
    ·
      refine ⟨13543631152958463955486721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9029087435305642636991147 13543631152958463955486721)
      ·
        refine ⟨10157723364718847966615041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13543631152958463955486721 10157723364718847966615041)
        ·
          refine ⟨7618292523539135974961281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10157723364718847966615041 7618292523539135974961281)
          ·
            refine ⟨5713719392654351981220961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7618292523539135974961281 5713719392654351981220961)
            ·
              refine ⟨4285289544490763985915721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5713719392654351981220961 4285289544490763985915721)
              ·
                refine ⟨3213967158368072989436791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285289544490763985915721 3213967158368072989436791)
                ·
                  refine ⟨4820950737552109484155187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213967158368072989436791 4820950737552109484155187)
                  ·
                    refine ⟨7231426106328164226232781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4820950737552109484155187 7231426106328164226232781)
                    ·
                      refine ⟨2711784789873061584837293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7231426106328164226232781 2711784789873061584837293)
                      ·
                        rfl

theorem cell23_5281182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_5281182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281182 prefixEnd_5281182 := by exact prefixLift 5281182
  have htrace : WordTrace (prefixWord ++ tailWord_5281182) baseStart_5281182 baseEnd_5281182 := by
    simpa [prefixWord, tailWord_5281182, baseEnd_5281182] using wordTrace_append hprefix tailTrace_5281182
  have hstable : (prefixWord ++ tailWord_5281182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281182).length < 2 ^ (prefixWord ++ tailWord_5281182).sum := by decide
  have hdescent : baseEnd_5281182 < baseStart_5281182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281231 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 1, 3, 2]
def baseStart_5281231 : Nat := 118140960795 + 5281231 * 2 ^ 59
def prefixEnd_5281231 : Nat := 4983230072969 + 3 ^ 40 * 5281231 * 2
def baseEnd_5281231 : Nat := 2711809950425131893124567

theorem tailTrace_5281231 : CollatzResearch.WordTrace tailWord_5281231 prefixEnd_5281231 2711809950425131893124567 := by
  unfold tailWord_5281231
  simp only [CollatzResearch.WordTrace]
  refine ⟨192622319130009524291011547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128414879420006349527341031 192622319130009524291011547)
  ·
    refine ⟨288933478695014286436517321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192622319130009524291011547 288933478695014286436517321)
    ·
      refine ⟨216700109021260714827387991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288933478695014286436517321 216700109021260714827387991)
      ·
        refine ⟨325050163531891072241081987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216700109021260714827387991 325050163531891072241081987)
        ·
          refine ⟨487575245297836608361622981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325050163531891072241081987 487575245297836608361622981)
          ·
            refine ⟨91420358493344364067804309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 487575245297836608361622981 91420358493344364067804309)
            ·
              refine ⟨4285329304375517065678327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91420358493344364067804309 4285329304375517065678327)
              ·
                refine ⟨6427993956563275598517491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4285329304375517065678327 6427993956563275598517491)
                ·
                  refine ⟨9641990934844913397776237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6427993956563275598517491 9641990934844913397776237)
                  ·
                    refine ⟨3615746600566842524166089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9641990934844913397776237 3615746600566842524166089)
                    ·
                      refine ⟨2711809950425131893124567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615746600566842524166089 2711809950425131893124567)
                      ·
                        rfl

theorem cell23_5281231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 3, 2].length) (baseStart_5281231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281231 prefixEnd_5281231 := by exact prefixLift 5281231
  have htrace : WordTrace (prefixWord ++ tailWord_5281231) baseStart_5281231 baseEnd_5281231 := by
    simpa [prefixWord, tailWord_5281231, baseEnd_5281231] using wordTrace_append hprefix tailTrace_5281231
  have hstable : (prefixWord ++ tailWord_5281231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281231).length < 2 ^ (prefixWord ++ tailWord_5281231).sum := by decide
  have hdescent : baseEnd_5281231 < baseStart_5281231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281238 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_5281238 : Nat := 118140960795 + 5281238 * 2 ^ 59
def prefixEnd_5281238 : Nat := 4983230072969 + 3 ^ 40 * 5281238 * 2
def baseEnd_5281238 : Nat := 2711813544789713365737035

theorem tailTrace_5281238 : CollatzResearch.WordTrace tailWord_5281238 prefixEnd_5281238 2711813544789713365737035 := by
  unfold tailWord_5281238
  simp only [CollatzResearch.WordTrace]
  refine ⟨12038910902561510280407273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128415049627322776324344245 12038910902561510280407273)
  ·
    refine ⟨9029183176921132710305455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12038910902561510280407273 9029183176921132710305455)
    ·
      refine ⟨13543774765381699065458183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9029183176921132710305455 13543774765381699065458183)
      ·
        refine ⟨20315662148072548598187275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13543774765381699065458183 20315662148072548598187275)
        ·
          refine ⟨30473493222108822897280913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20315662148072548598187275 30473493222108822897280913)
          ·
            refine ⟨22855119916581617172960685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30473493222108822897280913 22855119916581617172960685)
            ·
              refine ⟨8570669968718106439860257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22855119916581617172960685 8570669968718106439860257)
              ·
                refine ⟨6428002476538579829895193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8570669968718106439860257 6428002476538579829895193)
                ·
                  refine ⟨4821001857403934872421395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6428002476538579829895193 4821001857403934872421395)
                  ·
                    refine ⟨7231502786105902308632093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4821001857403934872421395 7231502786105902308632093)
                    ·
                      refine ⟨2711813544789713365737035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7231502786105902308632093 2711813544789713365737035)
                      ·
                        rfl

theorem cell23_5281238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_5281238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281238 prefixEnd_5281238 := by exact prefixLift 5281238
  have htrace : WordTrace (prefixWord ++ tailWord_5281238) baseStart_5281238 baseEnd_5281238 := by
    simpa [prefixWord, tailWord_5281238, baseEnd_5281238] using wordTrace_append hprefix tailTrace_5281238
  have hstable : (prefixWord ++ tailWord_5281238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281238).length < 2 ^ (prefixWord ++ tailWord_5281238).sum := by decide
  have hdescent : baseEnd_5281238 < baseStart_5281238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281297 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_5281297 : Nat := 118140960795 + 5281297 * 2 ^ 59
def prefixEnd_5281297 : Nat := 4983230072969 + 3 ^ 40 * 5281297 * 2
def baseEnd_5281297 : Nat := 903947946716109544966421

theorem tailTrace_5281297 : CollatzResearch.WordTrace tailWord_5281297 prefixEnd_5281297 903947946716109544966421 := by
  unfold tailWord_5281297
  simp only [CollatzResearch.WordTrace]
  refine ⟨192624726347770417562914145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128416484231846945041942763 192624726347770417562914145)
  ·
    refine ⟨144468544760827813172185609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192624726347770417562914145 144468544760827813172185609)
    ·
      refine ⟨108351408570620859879139207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144468544760827813172185609 108351408570620859879139207)
      ·
        refine ⟨162527112855931289818708811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108351408570620859879139207 162527112855931289818708811)
        ·
          refine ⟨243790669283896934728063217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162527112855931289818708811 243790669283896934728063217)
          ·
            refine ⟨182843001962922701046047413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243790669283896934728063217 182843001962922701046047413)
            ·
              refine ⟨17141531434024003223066945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 182843001962922701046047413 17141531434024003223066945)
              ·
                refine ⟨12856148575518002417300209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17141531434024003223066945 12856148575518002417300209)
                ·
                  refine ⟨9642111431638501812975157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12856148575518002417300209 9642111431638501812975157)
                  ·
                    refine ⟨903947946716109544966421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9642111431638501812975157 903947946716109544966421)
                    ·
                      rfl

theorem cell23_5281297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_5281297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281297 prefixEnd_5281297 := by exact prefixLift 5281297
  have htrace : WordTrace (prefixWord ++ tailWord_5281297) baseStart_5281297 baseEnd_5281297 := by
    simpa [prefixWord, tailWord_5281297, baseEnd_5281297] using wordTrace_append hprefix tailTrace_5281297
  have hstable : (prefixWord ++ tailWord_5281297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281297).length < 2 ^ (prefixWord ++ tailWord_5281297).sum := by decide
  have hdescent : baseEnd_5281297 < baseStart_5281297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281301 : List Nat := [1, 3, 2, 1, 3, 3, 3, 2, 5]
def baseStart_5281301 : Nat := 118140960795 + 5281301 * 2 ^ 59
def prefixEnd_5281301 : Nat := 4983230072969 + 3 ^ 40 * 5281301 * 2
def baseEnd_5281301 : Nat := 301316210452327402138805

theorem tailTrace_5281301 : CollatzResearch.WordTrace tailWord_5281301 prefixEnd_5281301 301316210452327402138805 := by
  unfold tailWord_5281301
  simp only [CollatzResearch.WordTrace]
  refine ⟨192624872239755926246059757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128416581493170617497373171 192624872239755926246059757)
  ·
    refine ⟨72234327089908472342272409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192624872239755926246059757 72234327089908472342272409)
    ·
      refine ⟨54175745317431354256704307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72234327089908472342272409 54175745317431354256704307)
      ·
        refine ⟨81263617976147031385056461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54175745317431354256704307 81263617976147031385056461)
        ·
          refine ⟨30473856741055136769396173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81263617976147031385056461 30473856741055136769396173)
          ·
            refine ⟨11427696277895676288523565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30473856741055136769396173 11427696277895676288523565)
            ·
              refine ⟨4285386104210878608196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11427696277895676288523565 4285386104210878608196337)
              ·
                refine ⟨3214039578158158956147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4285386104210878608196337 3214039578158158956147253)
                ·
                  refine ⟨301316210452327402138805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3214039578158158956147253 301316210452327402138805)
                  ·
                    rfl

theorem cell23_5281301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_5281301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281301 prefixEnd_5281301 := by exact prefixLift 5281301
  have htrace : WordTrace (prefixWord ++ tailWord_5281301) baseStart_5281301 baseEnd_5281301 := by
    simpa [prefixWord, tailWord_5281301, baseEnd_5281301] using wordTrace_append hprefix tailTrace_5281301
  have hstable : (prefixWord ++ tailWord_5281301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281301).length < 2 ^ (prefixWord ++ tailWord_5281301).sum := by decide
  have hdescent : baseEnd_5281301 < baseStart_5281301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281317 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_5281317 : Nat := 118140960795 + 5281317 * 2 ^ 59
def prefixEnd_5281317 : Nat := 4983230072969 + 3 ^ 40 * 5281317 * 2
def baseEnd_5281317 : Nat := 2711854109761418556649171

theorem tailTrace_5281317 : CollatzResearch.WordTrace tailWord_5281317 prefixEnd_5281317 2711854109761418556649171 := by
  unfold tailWord_5281317
  simp only [CollatzResearch.WordTrace]
  refine ⟨192625455807697960978642205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128416970538465307319094803 192625455807697960978642205)
  ·
    refine ⟨72234545927886735366990827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192625455807697960978642205 72234545927886735366990827)
    ·
      refine ⟨108351818891830103050486241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72234545927886735366990827 108351818891830103050486241)
      ·
        refine ⟨81263864168872577287864681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108351818891830103050486241 81263864168872577287864681)
        ·
          refine ⟨60947898126654432965898511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81263864168872577287864681 60947898126654432965898511)
          ·
            refine ⟨91421847189981649448847767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60947898126654432965898511 91421847189981649448847767)
            ·
              refine ⟨137132770784972474173271651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91421847189981649448847767 137132770784972474173271651)
              ·
                refine ⟨205699156177458711259907477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137132770784972474173271651 205699156177458711259907477)
                ·
                  refine ⟨9642147945818377090308163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205699156177458711259907477 9642147945818377090308163)
                  ·
                    refine ⟨14463221918727565635462245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9642147945818377090308163 14463221918727565635462245)
                    ·
                      refine ⟨2711854109761418556649171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14463221918727565635462245 2711854109761418556649171)
                      ·
                        rfl

theorem cell23_5281317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_5281317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281317 prefixEnd_5281317 := by exact prefixLift 5281317
  have htrace : WordTrace (prefixWord ++ tailWord_5281317) baseStart_5281317 baseEnd_5281317 := by
    simpa [prefixWord, tailWord_5281317, baseEnd_5281317] using wordTrace_append hprefix tailTrace_5281317
  have hstable : (prefixWord ++ tailWord_5281317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281317).length < 2 ^ (prefixWord ++ tailWord_5281317).sum := by decide
  have hdescent : baseEnd_5281317 < baseStart_5281317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281354 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_5281354 : Nat := 118140960795 + 5281354 * 2 ^ 59
def prefixEnd_5281354 : Nat := 4983230072969 + 3 ^ 40 * 5281354 * 2
def baseEnd_5281354 : Nat := 2711873108545634911886501

theorem tailTrace_5281354 : CollatzResearch.WordTrace tailWord_5281354 prefixEnd_5281354 2711873108545634911886501 := by
  unfold tailWord_5281354
  simp only [CollatzResearch.WordTrace]
  refine ⟨48156701327140979074434779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128417870205709277531826077 48156701327140979074434779)
  ·
    refine ⟨72235051990711468611652169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48156701327140979074434779 72235051990711468611652169)
    ·
      refine ⟨54176288993033601458739127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72235051990711468611652169 54176288993033601458739127)
      ·
        refine ⟨81264433489550402188108691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54176288993033601458739127 81264433489550402188108691)
        ·
          refine ⟨121896650234325603282163037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81264433489550402188108691 121896650234325603282163037)
          ·
            refine ⟨45711243837872101230811139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121896650234325603282163037 45711243837872101230811139)
            ·
              refine ⟨68566865756808151846216709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45711243837872101230811139 68566865756808151846216709)
              ·
                refine ⟨12856287329401528471165633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68566865756808151846216709 12856287329401528471165633)
                ·
                  refine ⟨9642215497051146353374225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12856287329401528471165633 9642215497051146353374225)
                  ·
                    refine ⟨7231661622788359765030669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9642215497051146353374225 7231661622788359765030669)
                    ·
                      refine ⟨2711873108545634911886501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7231661622788359765030669 2711873108545634911886501)
                      ·
                        rfl

theorem cell23_5281354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_5281354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281354 prefixEnd_5281354 := by exact prefixLift 5281354
  have htrace : WordTrace (prefixWord ++ tailWord_5281354) baseStart_5281354 baseEnd_5281354 := by
    simpa [prefixWord, tailWord_5281354, baseEnd_5281354] using wordTrace_append hprefix tailTrace_5281354
  have hstable : (prefixWord ++ tailWord_5281354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281354).length < 2 ^ (prefixWord ++ tailWord_5281354).sum := by decide
  have hdescent : baseEnd_5281354 < baseStart_5281354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281361 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 1, 4]
def baseStart_5281361 : Nat := 118140960795 + 5281361 * 2 ^ 59
def prefixEnd_5281361 : Nat := 4983230072969 + 3 ^ 40 * 5281361 * 2
def baseEnd_5281361 : Nat := 903958900970072128166323

theorem tailTrace_5281361 : CollatzResearch.WordTrace tailWord_5281361 prefixEnd_5281361 903958900970072128166323 := by
  unfold tailWord_5281361
  simp only [CollatzResearch.WordTrace]
  refine ⟨192627060619538556493243937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128418040413025704328829291 192627060619538556493243937)
  ·
    refine ⟨144470295464653917369932953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192627060619538556493243937 144470295464653917369932953)
    ·
      refine ⟨108352721598490438027449715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144470295464653917369932953 108352721598490438027449715)
      ·
        refine ⟨162529082397735657041174573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108352721598490438027449715 162529082397735657041174573)
        ·
          refine ⟨60948405899150871390440465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162529082397735657041174573 60948405899150871390440465)
          ·
            refine ⟨45711304424363153542830349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60948405899150871390440465 45711304424363153542830349)
            ·
              refine ⟨17141739159136182578561381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45711304424363153542830349 17141739159136182578561381)
              ·
                refine ⟨3214076092338034233480259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17141739159136182578561381 3214076092338034233480259)
                ·
                  refine ⟨4821114138507051350220389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214076092338034233480259 4821114138507051350220389)
                  ·
                    refine ⟨903958900970072128166323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821114138507051350220389 903958900970072128166323)
                    ·
                      rfl

theorem cell23_5281361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_5281361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281361 prefixEnd_5281361 := by exact prefixLift 5281361
  have htrace : WordTrace (prefixWord ++ tailWord_5281361) baseStart_5281361 baseEnd_5281361 := by
    simpa [prefixWord, tailWord_5281361, baseEnd_5281361] using wordTrace_append hprefix tailTrace_5281361
  have hstable : (prefixWord ++ tailWord_5281361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281361).length < 2 ^ (prefixWord ++ tailWord_5281361).sum := by decide
  have hdescent : baseEnd_5281361 < baseStart_5281361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281417 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_5281417 : Nat := 118140960795 + 5281417 * 2 ^ 59
def prefixEnd_5281417 : Nat := 4983230072969 + 3 ^ 40 * 5281417 * 2
def baseEnd_5281417 : Nat := 903968485942289388466237

theorem tailTrace_5281417 : CollatzResearch.WordTrace tailWord_5281417 prefixEnd_5281417 903968485942289388466237 := by
  unfold tailWord_5281417
  simp only [CollatzResearch.WordTrace]
  refine ⟨192629103107335678057282505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128419402071557118704855003 192629103107335678057282505)
  ·
    refine ⟨144471827330501758542961879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192629103107335678057282505 144471827330501758542961879)
    ·
      refine ⟨216707740995752637814442819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144471827330501758542961879 216707740995752637814442819)
      ·
        refine ⟨325061611493628956721664229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216707740995752637814442819 325061611493628956721664229)
        ·
          refine ⟨60949052155055429385312043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325061611493628956721664229 60949052155055429385312043)
          ·
            refine ⟨91423578232583144077968065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60949052155055429385312043 91423578232583144077968065)
            ·
              refine ⟨68567683674437358058476049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91423578232583144077968065 68567683674437358058476049)
              ·
                refine ⟨51425762755828018543857037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68567683674437358058476049 51425762755828018543857037)
                ·
                  refine ⟨19284661033435506953946389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51425762755828018543857037 19284661033435506953946389)
                  ·
                    refine ⟨903968485942289388466237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19284661033435506953946389 903968485942289388466237)
                    ·
                      rfl

theorem cell23_5281417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_5281417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281417 prefixEnd_5281417 := by exact prefixLift 5281417
  have htrace : WordTrace (prefixWord ++ tailWord_5281417) baseStart_5281417 baseEnd_5281417 := by
    simpa [prefixWord, tailWord_5281417, baseEnd_5281417] using wordTrace_append hprefix tailTrace_5281417
  have hstable : (prefixWord ++ tailWord_5281417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281417).length < 2 ^ (prefixWord ++ tailWord_5281417).sum := by decide
  have hdescent : baseEnd_5281417 < baseStart_5281417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281418 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_5281418 : Nat := 118140960795 + 5281418 * 2 ^ 59
def prefixEnd_5281418 : Nat := 4983230072969 + 3 ^ 40 * 5281418 * 2
def baseEnd_5281418 : Nat := 2711905971307522661486207

theorem tailTrace_5281418 : CollatzResearch.WordTrace tailWord_5281418 prefixEnd_5281418 2711905971307522661486207 := by
  unfold tailWord_5281418
  simp only [CollatzResearch.WordTrace]
  refine ⟨48157284895083013807017227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128419426386888036818712605 48157284895083013807017227)
  ·
    refine ⟨72235927342624520710525841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48157284895083013807017227 72235927342624520710525841)
    ·
      refine ⟨54176945506968390532894381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72235927342624520710525841 54176945506968390532894381)
      ·
        refine ⟨20316354565113146449835393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54176945506968390532894381 20316354565113146449835393)
        ·
          refine ⟨15237265923834859837376545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20316354565113146449835393 15237265923834859837376545)
          ·
            refine ⟨11427949442876144878032409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15237265923834859837376545 11427949442876144878032409)
            ·
              refine ⟨8570962082157108658524307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11427949442876144878032409 8570962082157108658524307)
              ·
                refine ⟨12856443123235662987786461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8570962082157108658524307 12856443123235662987786461)
                ·
                  refine ⟨4821166171213373620419923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12856443123235662987786461 4821166171213373620419923)
                  ·
                    refine ⟨7231749256820060430629885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4821166171213373620419923 7231749256820060430629885)
                    ·
                      refine ⟨2711905971307522661486207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7231749256820060430629885 2711905971307522661486207)
                      ·
                        rfl

theorem cell23_5281418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_5281418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281418 prefixEnd_5281418 := by exact prefixLift 5281418
  have htrace : WordTrace (prefixWord ++ tailWord_5281418) baseStart_5281418 baseEnd_5281418 := by
    simpa [prefixWord, tailWord_5281418, baseEnd_5281418] using wordTrace_append hprefix tailTrace_5281418
  have hstable : (prefixWord ++ tailWord_5281418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281418).length < 2 ^ (prefixWord ++ tailWord_5281418).sum := by decide
  have hdescent : baseEnd_5281418 < baseStart_5281418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281438 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5281438 : Nat := 118140960795 + 5281438 * 2 ^ 59
def prefixEnd_5281438 : Nat := 4983230072969 + 3 ^ 40 * 5281438 * 2
def baseEnd_5281438 : Nat := 903972080306870861078705

theorem tailTrace_5281438 : CollatzResearch.WordTrace tailWord_5281438 prefixEnd_5281438 903972080306870861078705 := by
  unfold tailWord_5281438
  simp only [CollatzResearch.WordTrace]
  refine ⟨24078733630032449830474621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128419912693506399095864645 24078733630032449830474621)
  ·
    refine ⟨9029525111262168686427983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24078733630032449830474621 9029525111262168686427983)
    ·
      refine ⟨13544287666893253029641975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9029525111262168686427983 13544287666893253029641975)
      ·
        refine ⟨20316431500339879544462963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13544287666893253029641975 20316431500339879544462963)
        ·
          refine ⟨30474647250509819316694445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20316431500339879544462963 30474647250509819316694445)
          ·
            refine ⟨11427992718941182243760417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30474647250509819316694445 11427992718941182243760417)
            ·
              refine ⟨8570994539205886682820313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11427992718941182243760417 8570994539205886682820313)
              ·
                refine ⟨6428245904404415012115235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8570994539205886682820313 6428245904404415012115235)
                ·
                  refine ⟨9642368856606622518172853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6428245904404415012115235 9642368856606622518172853)
                  ·
                    refine ⟨903972080306870861078705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9642368856606622518172853 903972080306870861078705)
                    ·
                      rfl

theorem cell23_5281438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5281438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281438 prefixEnd_5281438 := by exact prefixLift 5281438
  have htrace : WordTrace (prefixWord ++ tailWord_5281438) baseStart_5281438 baseEnd_5281438 := by
    simpa [prefixWord, tailWord_5281438, baseEnd_5281438] using wordTrace_append hprefix tailTrace_5281438
  have hstable : (prefixWord ++ tailWord_5281438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281438).length < 2 ^ (prefixWord ++ tailWord_5281438).sum := by decide
  have hdescent : baseEnd_5281438 < baseStart_5281438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281441 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_5281441 : Nat := 118140960795 + 5281441 * 2 ^ 59
def prefixEnd_5281441 : Nat := 4983230072969 + 3 ^ 40 * 5281441 * 2
def baseEnd_5281441 : Nat := 2711917781362576071498601

theorem tailTrace_5281441 : CollatzResearch.WordTrace tailWord_5281441 prefixEnd_5281441 2711917781362576071498601 := by
  unfold tailWord_5281441
  simp only [CollatzResearch.WordTrace]
  refine ⟨192629978459248730156156177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128419985639499153437437451 192629978459248730156156177)
  ·
    refine ⟨144472483844436547617117133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192629978459248730156156177 144472483844436547617117133)
    ·
      refine ⟨54177181441663705356418925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144472483844436547617117133 54177181441663705356418925)
      ·
        refine ⟨20316443040623889508657097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54177181441663705356418925 20316443040623889508657097)
        ·
          refine ⟨15237332280467917131492823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20316443040623889508657097 15237332280467917131492823)
          ·
            refine ⟨22855998420701875697239235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15237332280467917131492823 22855998420701875697239235)
            ·
              refine ⟨34283997631052813545858853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22855998420701875697239235 34283997631052813545858853)
              ·
                refine ⟨6428249555822402539848535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34283997631052813545858853 6428249555822402539848535)
                ·
                  refine ⟨9642374333733603809772803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6428249555822402539848535 9642374333733603809772803)
                  ·
                    refine ⟨14463561500600405714659205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9642374333733603809772803 14463561500600405714659205)
                    ·
                      refine ⟨2711917781362576071498601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14463561500600405714659205 2711917781362576071498601)
                      ·
                        rfl

theorem cell23_5281441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_5281441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281441 prefixEnd_5281441 := by exact prefixLift 5281441
  have htrace : WordTrace (prefixWord ++ tailWord_5281441) baseStart_5281441 baseEnd_5281441 := by
    simpa [prefixWord, tailWord_5281441, baseEnd_5281441] using wordTrace_append hprefix tailTrace_5281441
  have hstable : (prefixWord ++ tailWord_5281441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281441).length < 2 ^ (prefixWord ++ tailWord_5281441).sum := by decide
  have hdescent : baseEnd_5281441 < baseStart_5281441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281477 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_5281477 : Nat := 118140960795 + 5281477 * 2 ^ 59
def prefixEnd_5281477 : Nat := 4983230072969 + 3 ^ 40 * 5281477 * 2
def baseEnd_5281477 : Nat := 903978755555379310216145

theorem tailTrace_5281477 : CollatzResearch.WordTrace tailWord_5281477 prefixEnd_5281477 903978755555379310216145 := by
  unfold tailWord_5281477
  simp only [CollatzResearch.WordTrace]
  refine ⟨192631291487118308304466685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128420860991412205536311123 192631291487118308304466685)
  ·
    refine ⟨72236734307669365614175007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192631291487118308304466685 72236734307669365614175007)
    ·
      refine ⟨108355101461504048421262511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72236734307669365614175007 108355101461504048421262511)
      ·
        refine ⟨162532652192256072631893767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108355101461504048421262511 162532652192256072631893767)
        ·
          refine ⟨243798978288384108947840651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162532652192256072631893767 243798978288384108947840651)
          ·
            refine ⟨365698467432576163421760977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243798978288384108947840651 365698467432576163421760977)
            ·
              refine ⟨274273850574432122566320733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365698467432576163421760977 274273850574432122566320733)
              ·
                refine ⟨102852693965412045962370275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274273850574432122566320733 102852693965412045962370275)
                ·
                  refine ⟨154279040948118068943555413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102852693965412045962370275 154279040948118068943555413)
                  ·
                    refine ⟨903978755555379310216145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 154279040948118068943555413 903978755555379310216145)
                    ·
                      rfl

theorem cell23_5281477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_5281477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281477 prefixEnd_5281477 := by exact prefixLift 5281477
  have htrace : WordTrace (prefixWord ++ tailWord_5281477) baseStart_5281477 baseEnd_5281477 := by
    simpa [prefixWord, tailWord_5281477, baseEnd_5281477] using wordTrace_append hprefix tailTrace_5281477
  have hstable : (prefixWord ++ tailWord_5281477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281477).length < 2 ^ (prefixWord ++ tailWord_5281477).sum := by decide
  have hdescent : baseEnd_5281477 < baseStart_5281477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281485 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5281485 : Nat := 118140960795 + 5281485 * 2 ^ 59
def prefixEnd_5281485 : Nat := 4983230072969 + 3 ^ 40 * 5281485 * 2
def baseEnd_5281485 : Nat := 903980124837124633116133

theorem tailTrace_5281485 : CollatzResearch.WordTrace tailWord_5281485 prefixEnd_5281485 903980124837124633116133 := by
  unfold tailWord_5281485
  simp only [CollatzResearch.WordTrace]
  refine ⟨192631583271089325670757909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128421055514059550447171939 192631583271089325670757909)
  ·
    refine ⟨9029605465832312140816777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 192631583271089325670757909 9029605465832312140816777)
    ·
      refine ⟨6772204099374234105612583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9029605465832312140816777 6772204099374234105612583)
      ·
        refine ⟨10158306149061351158418875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772204099374234105612583 10158306149061351158418875)
        ·
          refine ⟨15237459223592026737628313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10158306149061351158418875 15237459223592026737628313)
          ·
            refine ⟨11428094417694020053221235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15237459223592026737628313 11428094417694020053221235)
            ·
              refine ⟨17142141626541030079831853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11428094417694020053221235 17142141626541030079831853)
              ·
                refine ⟨6428303109952886279936945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17142141626541030079831853 6428303109952886279936945)
                ·
                  refine ⟨4821227332464664709952709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6428303109952886279936945 4821227332464664709952709)
                  ·
                    refine ⟨903980124837124633116133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821227332464664709952709 903980124837124633116133)
                    ·
                      rfl

theorem cell23_5281485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5281485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281485 prefixEnd_5281485 := by exact prefixLift 5281485
  have htrace : WordTrace (prefixWord ++ tailWord_5281485) baseStart_5281485 baseEnd_5281485 := by
    simpa [prefixWord, tailWord_5281485, baseEnd_5281485] using wordTrace_append hprefix tailTrace_5281485
  have hstable : (prefixWord ++ tailWord_5281485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281485).length < 2 ^ (prefixWord ++ tailWord_5281485).sum := by decide
  have hdescent : baseEnd_5281485 < baseStart_5281485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281571 : List Nat := [1, 1, 1, 4, 2, 1, 3, 5, 5]
def baseStart_5281571 : Nat := 118140960795 + 5281571 * 2 ^ 59
def prefixEnd_5281571 : Nat := 4983230072969 + 3 ^ 40 * 5281571 * 2
def baseEnd_5281571 : Nat := 301331614871962284763667

theorem tailTrace_5281571 : CollatzResearch.WordTrace tailWord_5281571 prefixEnd_5281571 301331614871962284763667 := by
  unfold tailWord_5281571
  simp only [CollatzResearch.WordTrace]
  refine ⟨192634719948777762358388567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128423146632518508238925711 192634719948777762358388567)
  ·
    refine ⟨288952079923166643537582851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192634719948777762358388567 288952079923166643537582851)
    ·
      refine ⟨433428119884749965306374277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288952079923166643537582851 433428119884749965306374277)
      ·
        refine ⟨81267772478390618494945177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 433428119884749965306374277 81267772478390618494945177)
        ·
          refine ⟨60950829358792963871208883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81267772478390618494945177 60950829358792963871208883)
          ·
            refine ⟨91426244038189445806813325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60950829358792963871208883 91426244038189445806813325)
            ·
              refine ⟨34284841514321042177554997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91426244038189445806813325 34284841514321042177554997)
              ·
                refine ⟨3214203891967597704145781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34284841514321042177554997 3214203891967597704145781)
                ·
                  refine ⟨301331614871962284763667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3214203891967597704145781 301331614871962284763667)
                  ·
                    rfl

theorem cell23_5281571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 5].length) (baseStart_5281571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281571 prefixEnd_5281571 := by exact prefixLift 5281571
  have htrace : WordTrace (prefixWord ++ tailWord_5281571) baseStart_5281571 baseEnd_5281571 := by
    simpa [prefixWord, tailWord_5281571, baseEnd_5281571] using wordTrace_append hprefix tailTrace_5281571
  have hstable : (prefixWord ++ tailWord_5281571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281571).length < 2 ^ (prefixWord ++ tailWord_5281571).sum := by decide
  have hdescent : baseEnd_5281571 < baseStart_5281571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281582 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5281582 : Nat := 118140960795 + 5281582 * 2 ^ 59
def prefixEnd_5281582 : Nat := 4983230072969 + 3 ^ 40 * 5281582 * 2
def baseEnd_5281582 : Nat := 2711990182134860019835453

theorem tailTrace_5281582 : CollatzResearch.WordTrace tailWord_5281582 prefixEnd_5281582 2711990182134860019835453 := by
  unfold tailWord_5281582
  simp only [CollatzResearch.WordTrace]
  refine ⟨24079390143967238904629875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128423414101158607491359333 24079390143967238904629875)
  ·
    refine ⟨36119085215950858356944813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24079390143967238904629875 36119085215950858356944813)
    ·
      refine ⟨13544656955981571883854305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36119085215950858356944813 13544656955981571883854305)
      ·
        refine ⟨10158492716986178912890729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13544656955981571883854305 10158492716986178912890729)
        ·
          refine ⟨7618869537739634184668047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10158492716986178912890729 7618869537739634184668047)
          ·
            refine ⟨11428304306609451277002071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7618869537739634184668047 11428304306609451277002071)
            ·
              refine ⟨17142456459914176915503107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11428304306609451277002071 17142456459914176915503107)
              ·
                refine ⟨25713684689871265373254661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17142456459914176915503107 25713684689871265373254661)
                ·
                  refine ⟨4821315879350862257485249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25713684689871265373254661 4821315879350862257485249)
                  ·
                    refine ⟨3615986909513146693113937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4821315879350862257485249 3615986909513146693113937)
                    ·
                      refine ⟨2711990182134860019835453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615986909513146693113937 2711990182134860019835453)
                      ·
                        rfl

theorem cell23_5281582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5281582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281582 prefixEnd_5281582 := by exact prefixLift 5281582
  have htrace : WordTrace (prefixWord ++ tailWord_5281582) baseStart_5281582 baseEnd_5281582 := by
    simpa [prefixWord, tailWord_5281582, baseEnd_5281582] using wordTrace_append hprefix tailTrace_5281582
  have hstable : (prefixWord ++ tailWord_5281582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281582).length < 2 ^ (prefixWord ++ tailWord_5281582).sum := by decide
  have hdescent : baseEnd_5281582 < baseStart_5281582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281588 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 7]
def baseStart_5281588 : Nat := 118140960795 + 5281588 * 2 ^ 59
def prefixEnd_5281588 : Nat := 4983230072969 + 3 ^ 40 * 5281588 * 2
def baseEnd_5281588 : Nat := 301332584779865221817825

theorem tailTrace_5281588 : CollatzResearch.WordTrace tailWord_5281588 prefixEnd_5281588 301332584779865221817825 := by
  unfold tailWord_5281588
  simp only [CollatzResearch.WordTrace]
  refine ⟨96317669994858087130878709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128423559993144116174504945 96317669994858087130878709)
  ·
    refine ⟨9029781562017945668519879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96317669994858087130878709 9029781562017945668519879)
    ·
      refine ⟨13544672343026918502779819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9029781562017945668519879 13544672343026918502779819)
      ·
        refine ⟨20317008514540377754169729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13544672343026918502779819 20317008514540377754169729)
        ·
          refine ⟨15237756385905283315627297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20317008514540377754169729 15237756385905283315627297)
          ·
            refine ⟨11428317289428962486720473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15237756385905283315627297 11428317289428962486720473)
            ·
              refine ⟨8571237967071721865040355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11428317289428962486720473 8571237967071721865040355)
              ·
                refine ⟨12856856950607582797560533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8571237967071721865040355 12856856950607582797560533)
                ·
                  refine ⟨301332584779865221817825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12856856950607582797560533 301332584779865221817825)
                  ·
                    rfl

theorem cell23_5281588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_5281588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281588 prefixEnd_5281588 := by exact prefixLift 5281588
  have htrace : WordTrace (prefixWord ++ tailWord_5281588) baseStart_5281588 baseEnd_5281588 := by
    simpa [prefixWord, tailWord_5281588, baseEnd_5281588] using wordTrace_append hprefix tailTrace_5281588
  have hstable : (prefixWord ++ tailWord_5281588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281588).length < 2 ^ (prefixWord ++ tailWord_5281588).sum := by decide
  have hdescent : baseEnd_5281588 < baseStart_5281588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281591 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 2, 5, 2]
def baseStart_5281591 : Nat := 118140960795 + 5281591 * 2 ^ 59
def prefixEnd_5281591 : Nat := 4983230072969 + 3 ^ 40 * 5281591 * 2
def baseEnd_5281591 : Nat := 2711994803460750484622911

theorem tailTrace_5281591 : CollatzResearch.WordTrace tailWord_5281591 prefixEnd_5281591 2711994803460750484622911 := by
  unfold tailWord_5281591
  simp only [CollatzResearch.WordTrace]
  refine ⟨192635449408705305774116627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128423632939136870516077751 192635449408705305774116627)
  ·
    refine ⟨288953174113057958661174941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192635449408705305774116627 288953174113057958661174941)
    ·
      refine ⟨108357440292396734497940603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288953174113057958661174941 108357440292396734497940603)
      ·
        refine ⟨162536160438595101746910905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108357440292396734497940603 162536160438595101746910905)
        ·
          refine ⟨121902120328946326310183179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162536160438595101746910905 121902120328946326310183179)
          ·
            refine ⟨182853180493419489465274769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121902120328946326310183179 182853180493419489465274769)
            ·
              refine ⟨137139885370064617098956077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182853180493419489465274769 137139885370064617098956077)
              ·
                refine ⟨51427457013774231412108529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137139885370064617098956077 51427457013774231412108529)
                ·
                  refine ⟨38570592760330673559081397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51427457013774231412108529 38570592760330673559081397)
                  ·
                    refine ⟨3615993071281000646163881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38570592760330673559081397 3615993071281000646163881)
                    ·
                      refine ⟨2711994803460750484622911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3615993071281000646163881 2711994803460750484622911)
                      ·
                        rfl

theorem cell23_5281591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_5281591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281591 prefixEnd_5281591 := by exact prefixLift 5281591
  have htrace : WordTrace (prefixWord ++ tailWord_5281591) baseStart_5281591 baseEnd_5281591 := by
    simpa [prefixWord, tailWord_5281591, baseEnd_5281591] using wordTrace_append hprefix tailTrace_5281591
  have hstable : (prefixWord ++ tailWord_5281591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281591).length < 2 ^ (prefixWord ++ tailWord_5281591).sum := by decide
  have hdescent : baseEnd_5281591 < baseStart_5281591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281598 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_5281598 : Nat := 118140960795 + 5281598 * 2 ^ 59
def prefixEnd_5281598 : Nat := 4983230072969 + 3 ^ 40 * 5281598 * 2
def baseEnd_5281598 : Nat := 2711998397825331957235379

theorem tailTrace_5281598 : CollatzResearch.WordTrace tailWord_5281598 prefixEnd_5281598 2711998397825331957235379 := by
  unfold tailWord_5281598
  simp only [CollatzResearch.WordTrace]
  refine ⟨24079463089959993246202681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128423803146453297313080965 24079463089959993246202681)
  ·
    refine ⟨18059597317469994934652011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24079463089959993246202681 18059597317469994934652011)
    ·
      refine ⟨27089395976204992401978017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18059597317469994934652011 27089395976204992401978017)
      ·
        refine ⟨20317046982153744301483513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27089395976204992401978017 20317046982153744301483513)
        ·
          refine ⟨15237785236615308226112635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20317046982153744301483513 15237785236615308226112635)
          ·
            refine ⟨22856677854922962339168953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15237785236615308226112635 22856677854922962339168953)
            ·
              refine ⟨17142508391192221754376715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22856677854922962339168953 17142508391192221754376715)
              ·
                refine ⟨25713762586788332631565073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17142508391192221754376715 25713762586788332631565073)
                ·
                  refine ⟨19285321940091249473673805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25713762586788332631565073 19285321940091249473673805)
                  ·
                    refine ⟨7231995727534218552627677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19285321940091249473673805 7231995727534218552627677)
                    ·
                      refine ⟨2711998397825331957235379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7231995727534218552627677 2711998397825331957235379)
                      ·
                        rfl

theorem cell23_5281598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_5281598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281598 prefixEnd_5281598 := by exact prefixLift 5281598
  have htrace : WordTrace (prefixWord ++ tailWord_5281598) baseStart_5281598 baseEnd_5281598 := by
    simpa [prefixWord, tailWord_5281598, baseEnd_5281598] using wordTrace_append hprefix tailTrace_5281598
  have hstable : (prefixWord ++ tailWord_5281598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281598).length < 2 ^ (prefixWord ++ tailWord_5281598).sum := by decide
  have hdescent : baseEnd_5281598 < baseStart_5281598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281621 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_5281621 : Nat := 118140960795 + 5281621 * 2 ^ 59
def prefixEnd_5281621 : Nat := 4983230072969 + 3 ^ 40 * 5281621 * 2
def baseEnd_5281621 : Nat := 2712010207880385367247773

theorem tailTrace_5281621 : CollatzResearch.WordTrace tailWord_5281621 prefixEnd_5281621 2712010207880385367247773 := by
  unfold tailWord_5281621
  simp only [CollatzResearch.WordTrace]
  refine ⟨192636543598596620897708717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128424362399064413931805811 192636543598596620897708717)
  ·
    refine ⟨72238703849473732836640769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192636543598596620897708717 72238703849473732836640769)
    ·
      refine ⟨54179027887105299627480577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72238703849473732836640769 54179027887105299627480577)
      ·
        refine ⟨40634270915328974720610433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54179027887105299627480577 40634270915328974720610433)
        ·
          refine ⟨30475703186496731040457825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40634270915328974720610433 30475703186496731040457825)
          ·
            refine ⟨22856777389872548280343369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30475703186496731040457825 22856777389872548280343369)
            ·
              refine ⟨17142583042404411210257527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22856777389872548280343369 17142583042404411210257527)
              ·
                refine ⟨25713874563606616815386291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17142583042404411210257527 25713874563606616815386291)
                ·
                  refine ⟨38570811845409925223079437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25713874563606616815386291 38570811845409925223079437)
                  ·
                    refine ⟨14464054442028721958654789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38570811845409925223079437 14464054442028721958654789)
                    ·
                      refine ⟨2712010207880385367247773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14464054442028721958654789 2712010207880385367247773)
                      ·
                        rfl

theorem cell23_5281621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_5281621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281621 prefixEnd_5281621 := by exact prefixLift 5281621
  have htrace : WordTrace (prefixWord ++ tailWord_5281621) baseStart_5281621 baseEnd_5281621 := by
    simpa [prefixWord, tailWord_5281621, baseEnd_5281621] using wordTrace_append hprefix tailTrace_5281621
  have hstable : (prefixWord ++ tailWord_5281621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281621).length < 2 ^ (prefixWord ++ tailWord_5281621).sum := by decide
  have hdescent : baseEnd_5281621 < baseStart_5281621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281624 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_5281624 : Nat := 118140960795 + 5281624 * 2 ^ 59
def prefixEnd_5281624 : Nat := 4983230072969 + 3 ^ 40 * 5281624 * 2
def baseEnd_5281624 : Nat := 2712011748322348855510259

theorem tailTrace_5281624 : CollatzResearch.WordTrace tailWord_5281624 prefixEnd_5281624 2712011748322348855510259 := by
  unfold tailWord_5281624
  simp only [CollatzResearch.WordTrace]
  refine ⟨96318326508792876205033963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128424435345057168273378617 96318326508792876205033963)
  ·
    refine ⟨144477489763189314307550945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96318326508792876205033963 144477489763189314307550945)
    ·
      refine ⟨108358117322391985730663209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144477489763189314307550945 108358117322391985730663209)
      ·
        refine ⟨81268587991793989297997407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108358117322391985730663209 81268587991793989297997407)
        ·
          refine ⟨121902881987690983946996111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81268587991793989297997407 121902881987690983946996111)
          ·
            refine ⟨182854322981536475920494167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121902881987690983946996111 182854322981536475920494167)
            ·
              refine ⟨274281484472304713880741251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182854322981536475920494167 274281484472304713880741251)
              ·
                refine ⟨411422226708457070821111877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274281484472304713880741251 411422226708457070821111877)
                ·
                  refine ⟨77141667507835700778958477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411422226708457070821111877 77141667507835700778958477)
                  ·
                    refine ⟨28928125315438387792109429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77141667507835700778958477 28928125315438387792109429)
                    ·
                      refine ⟨2712011748322348855510259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28928125315438387792109429 2712011748322348855510259)
                      ·
                        rfl

theorem cell23_5281624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_5281624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281624 prefixEnd_5281624 := by exact prefixLift 5281624
  have htrace : WordTrace (prefixWord ++ tailWord_5281624) baseStart_5281624 baseEnd_5281624 := by
    simpa [prefixWord, tailWord_5281624, baseEnd_5281624] using wordTrace_append hprefix tailTrace_5281624
  have hstable : (prefixWord ++ tailWord_5281624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281624).length < 2 ^ (prefixWord ++ tailWord_5281624).sum := by decide
  have hdescent : baseEnd_5281624 < baseStart_5281624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281711 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 4]
def baseStart_5281711 : Nat := 118140960795 + 5281711 * 2 ^ 59
def prefixEnd_5281711 : Nat := 4983230072969 + 3 ^ 40 * 5281711 * 2
def baseEnd_5281711 : Nat := 2712056421139290015122359

theorem tailTrace_5281711 : CollatzResearch.WordTrace tailWord_5281711 prefixEnd_5281711 2712056421139290015122359 := by
  unfold tailWord_5281711
  simp only [CollatzResearch.WordTrace]
  refine ⟨192639826168270566268484987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128426550778847044178989991 192639826168270566268484987)
  ·
    refine ⟨288959739252405849402727481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192639826168270566268484987 288959739252405849402727481)
    ·
      refine ⟨216719804439304387052045611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288959739252405849402727481 216719804439304387052045611)
      ·
        refine ⟨325079706658956580578068417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216719804439304387052045611 325079706658956580578068417)
        ·
          refine ⟨243809779994217435433551313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325079706658956580578068417 243809779994217435433551313)
          ·
            refine ⟨182857334995663076575163485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243809779994217435433551313 182857334995663076575163485)
            ·
              refine ⟨68571500623373653715686307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182857334995663076575163485 68571500623373653715686307)
              ·
                refine ⟨102857250935060480573529461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68571500623373653715686307 102857250935060480573529461)
                ·
                  refine ⟨9642867275161920053768387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102857250935060480573529461 9642867275161920053768387)
                  ·
                    refine ⟨14464300912742880080652581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9642867275161920053768387 14464300912742880080652581)
                    ·
                      refine ⟨2712056421139290015122359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14464300912742880080652581 2712056421139290015122359)
                      ·
                        rfl

theorem cell23_5281711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 1, 4].length) (baseStart_5281711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281711 prefixEnd_5281711 := by exact prefixLift 5281711
  have htrace : WordTrace (prefixWord ++ tailWord_5281711) baseStart_5281711 baseEnd_5281711 := by
    simpa [prefixWord, tailWord_5281711, baseEnd_5281711] using wordTrace_append hprefix tailTrace_5281711
  have hstable : (prefixWord ++ tailWord_5281711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281711).length < 2 ^ (prefixWord ++ tailWord_5281711).sum := by decide
  have hdescent : baseEnd_5281711 < baseStart_5281711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281728 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4]
def baseStart_5281728 : Nat := 118140960795 + 5281728 * 2 ^ 59
def prefixEnd_5281728 : Nat := 4983230072969 + 3 ^ 40 * 5281728 * 2
def baseEnd_5281728 : Nat := 2712065150310416448609781

theorem tailTrace_5281728 : CollatzResearch.WordTrace tailWord_5281728 prefixEnd_5281728 2712065150310416448609781 := by
  unfold tailWord_5281728
  simp only [CollatzResearch.WordTrace]
  refine ⟨96320223104604489085926919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128426964139472652114569225 96320223104604489085926919)
  ·
    refine ⟨144480334656906733628890379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96320223104604489085926919 144480334656906733628890379)
    ·
      refine ⟨216720501985360100443335569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144480334656906733628890379 216720501985360100443335569)
      ·
        refine ⟨162540376489020075332501677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216720501985360100443335569 162540376489020075332501677)
        ·
          refine ⟨60952641183382528249688129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162540376489020075332501677 60952641183382528249688129)
          ·
            refine ⟨45714480887536896187266097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60952641183382528249688129 45714480887536896187266097)
            ·
              refine ⟨34285860665652672140449573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45714480887536896187266097 34285860665652672140449573)
              ·
                refine ⟨6428598874809876026334295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34285860665652672140449573 6428598874809876026334295)
                ·
                  refine ⟨9642898312214814039501443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6428598874809876026334295 9642898312214814039501443)
                  ·
                    refine ⟨14464347468322221059252165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9642898312214814039501443 14464347468322221059252165)
                    ·
                      refine ⟨2712065150310416448609781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14464347468322221059252165 2712065150310416448609781)
                      ·
                        rfl

theorem cell23_5281728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_5281728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281728 prefixEnd_5281728 := by exact prefixLift 5281728
  have htrace : WordTrace (prefixWord ++ tailWord_5281728) baseStart_5281728 baseEnd_5281728 := by
    simpa [prefixWord, tailWord_5281728, baseEnd_5281728] using wordTrace_append hprefix tailTrace_5281728
  have hstable : (prefixWord ++ tailWord_5281728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281728).length < 2 ^ (prefixWord ++ tailWord_5281728).sum := by decide
  have hdescent : baseEnd_5281728 < baseStart_5281728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281748 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5281748 : Nat := 118140960795 + 5281748 * 2 ^ 59
def prefixEnd_5281748 : Nat := 4983230072969 + 3 ^ 40 * 5281748 * 2
def baseEnd_5281748 : Nat := 2712075419923506370359689

theorem tailTrace_5281748 : CollatzResearch.WordTrace tailWord_5281748 prefixEnd_5281748 2712075419923506370359689 := by
  unfold tailWord_5281748
  simp only [CollatzResearch.WordTrace]
  refine ⟨96320587834568260793790949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128427450446091014391721265 96320587834568260793790949)
  ·
    refine ⟨18060110218981548898835803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96320587834568260793790949 18060110218981548898835803)
    ·
      refine ⟨27090165328472323348253705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18060110218981548898835803 27090165328472323348253705)
      ·
        refine ⟨20317623996354242511190279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27090165328472323348253705 20317623996354242511190279)
        ·
          refine ⟨30476435994531363766785419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20317623996354242511190279 30476435994531363766785419)
          ·
            refine ⟨45714653991797045650178129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30476435994531363766785419 45714653991797045650178129)
            ·
              refine ⟨34285990493847784237633597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45714653991797045650178129 34285990493847784237633597)
              ·
                refine ⟨12857246435192919089112599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34285990493847784237633597 12857246435192919089112599)
                ·
                  refine ⟨19285869652789378633668899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12857246435192919089112599 19285869652789378633668899)
                  ·
                    refine ⟨28928804479184067950503349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19285869652789378633668899 28928804479184067950503349)
                    ·
                      refine ⟨2712075419923506370359689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28928804479184067950503349 2712075419923506370359689)
                      ·
                        rfl

theorem cell23_5281748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5281748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281748 prefixEnd_5281748 := by exact prefixLift 5281748
  have htrace : WordTrace (prefixWord ++ tailWord_5281748) baseStart_5281748 baseEnd_5281748 := by
    simpa [prefixWord, tailWord_5281748, baseEnd_5281748] using wordTrace_append hprefix tailTrace_5281748
  have hstable : (prefixWord ++ tailWord_5281748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281748).length < 2 ^ (prefixWord ++ tailWord_5281748).sum := by decide
  have hdescent : baseEnd_5281748 < baseStart_5281748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281756 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5281756 : Nat := 118140960795 + 5281756 * 2 ^ 59
def prefixEnd_5281756 : Nat := 4983230072969 + 3 ^ 40 * 5281756 * 2
def baseEnd_5281756 : Nat := 2712079527768742339059653

theorem tailTrace_5281756 : CollatzResearch.WordTrace tailWord_5281756 prefixEnd_5281756 2712079527768742339059653 := by
  unfold tailWord_5281756
  simp only [CollatzResearch.WordTrace]
  refine ⟨96320733726553769476936561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128427644968738359302582081 96320733726553769476936561)
  ·
    refine ⟨72240550294915327107702421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96320733726553769476936561 72240550294915327107702421)
    ·
      refine ⟨3386275795074155958173551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72240550294915327107702421 3386275795074155958173551)
      ·
        refine ⟨5079413692611233937260327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386275795074155958173551 5079413692611233937260327)
        ·
          refine ⟨7619120538916850905890491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5079413692611233937260327 7619120538916850905890491)
          ·
            refine ⟨11428680808375276358835737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7619120538916850905890491 11428680808375276358835737)
            ·
              refine ⟨8571510606281457269126803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11428680808375276358835737 8571510606281457269126803)
              ·
                refine ⟨12857265909422185903690205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8571510606281457269126803 12857265909422185903690205)
                ·
                  refine ⟨4821474716033319713883827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12857265909422185903690205 4821474716033319713883827)
                  ·
                    refine ⟨7232212074049979570825741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4821474716033319713883827 7232212074049979570825741)
                    ·
                      refine ⟨2712079527768742339059653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7232212074049979570825741 2712079527768742339059653)
                      ·
                        rfl

theorem cell23_5281756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5281756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281756 prefixEnd_5281756 := by exact prefixLift 5281756
  have htrace : WordTrace (prefixWord ++ tailWord_5281756) baseStart_5281756 baseEnd_5281756 := by
    simpa [prefixWord, tailWord_5281756, baseEnd_5281756] using wordTrace_append hprefix tailTrace_5281756
  have hstable : (prefixWord ++ tailWord_5281756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281756).length < 2 ^ (prefixWord ++ tailWord_5281756).sum := by decide
  have hdescent : baseEnd_5281756 < baseStart_5281756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281801 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_5281801 : Nat := 118140960795 + 5281801 * 2 ^ 59
def prefixEnd_5281801 : Nat := 4983230072969 + 3 ^ 40 * 5281801 * 2
def baseEnd_5281801 : Nat := 2712102634398194662996945

theorem tailTrace_5281801 : CollatzResearch.WordTrace tailWord_5281801 prefixEnd_5281801 2712102634398194662996945 := by
  unfold tailWord_5281801
  simp only [CollatzResearch.WordTrace]
  refine ⟨192643108737944511639261257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128428739158629674426174171 192643108737944511639261257)
  ·
    refine ⟨144482331553458383729445943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192643108737944511639261257 144482331553458383729445943)
    ·
      refine ⟨216723497330187575594168915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144482331553458383729445943 216723497330187575594168915)
      ·
        refine ⟨325085245995281363391253373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216723497330187575594168915 325085245995281363391253373)
        ·
          refine ⟨121906967248230511271720015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325085245995281363391253373 121906967248230511271720015)
          ·
            refine ⟨182860450872345766907580023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121906967248230511271720015 182860450872345766907580023)
            ·
              refine ⟨274290676308518650361370035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182860450872345766907580023 274290676308518650361370035)
              ·
                refine ⟨411436014462777975542055053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274290676308518650361370035 411436014462777975542055053)
                ·
                  refine ⟨154288505423541740828270645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 411436014462777975542055053 154288505423541740828270645)
                  ·
                    refine ⟨14464547383457038202650373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154288505423541740828270645 14464547383457038202650373)
                    ·
                      refine ⟨2712102634398194662996945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14464547383457038202650373 2712102634398194662996945)
                      ·
                        rfl

theorem cell23_5281801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_5281801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281801 prefixEnd_5281801 := by exact prefixLift 5281801
  have htrace : WordTrace (prefixWord ++ tailWord_5281801) baseStart_5281801 baseEnd_5281801 := by
    simpa [prefixWord, tailWord_5281801, baseEnd_5281801] using wordTrace_append hprefix tailTrace_5281801
  have hstable : (prefixWord ++ tailWord_5281801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281801).length < 2 ^ (prefixWord ++ tailWord_5281801).sum := by decide
  have hdescent : baseEnd_5281801 < baseStart_5281801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281811 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 4, 6]
def baseStart_5281811 : Nat := 118140960795 + 5281811 * 2 ^ 59
def prefixEnd_5281811 : Nat := 4983230072969 + 3 ^ 40 * 5281811 * 2
def baseEnd_5281811 : Nat := 904035923068246541290633

theorem tailTrace_5281811 : CollatzResearch.WordTrace tailWord_5281811 prefixEnd_5281811 904035923068246541290633 := by
  unfold tailWord_5281811
  simp only [CollatzResearch.WordTrace]
  refine ⟨192643473467908283347125287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128428982311938855564750191 192643473467908283347125287)
  ·
    refine ⟨288965210201862425020687931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192643473467908283347125287 288965210201862425020687931)
    ·
      refine ⟨433447815302793637531031897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288965210201862425020687931 433447815302793637531031897)
      ·
        refine ⟨325085861477095228148273923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433447815302793637531031897 325085861477095228148273923)
        ·
          refine ⟨487628792215642842222410885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325085861477095228148273923 487628792215642842222410885)
          ·
            refine ⟨91430398540433032916702041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 487628792215642842222410885 91430398540433032916702041)
            ·
              refine ⟨68572798905324774687526531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91430398540433032916702041 68572798905324774687526531)
              ·
                refine ⟨102859198357987162031289797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68572798905324774687526531 102859198357987162031289797)
                ·
                  refine ⟨19286099692122592880866837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102859198357987162031289797 19286099692122592880866837)
                  ·
                    refine ⟨904035923068246541290633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19286099692122592880866837 904035923068246541290633)
                    ·
                      rfl

theorem cell23_5281811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 6].length) (baseStart_5281811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281811 prefixEnd_5281811 := by exact prefixLift 5281811
  have htrace : WordTrace (prefixWord ++ tailWord_5281811) baseStart_5281811 baseEnd_5281811 := by
    simpa [prefixWord, tailWord_5281811, baseEnd_5281811] using wordTrace_append hprefix tailTrace_5281811
  have hstable : (prefixWord ++ tailWord_5281811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281811).length < 2 ^ (prefixWord ++ tailWord_5281811).sum := by decide
  have hdescent : baseEnd_5281811 < baseStart_5281811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281829 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 2, 1, 3]
def baseStart_5281829 : Nat := 118140960795 + 5281829 * 2 ^ 59
def prefixEnd_5281829 : Nat := 4983230072969 + 3 ^ 40 * 5281829 * 2
def baseEnd_5281829 : Nat := 2712117011856520553446817

theorem tailTrace_5281829 : CollatzResearch.WordTrace tailWord_5281829 prefixEnd_5281829 2712117011856520553446817 := by
  unfold tailWord_5281829
  simp only [CollatzResearch.WordTrace]
  refine ⟨192644129981843072421280541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128429419987895381614187027 192644129981843072421280541)
  ·
    refine ⟨72241548743191152157980203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192644129981843072421280541 72241548743191152157980203)
    ·
      refine ⟨108362323114786728236970305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72241548743191152157980203 108362323114786728236970305)
      ·
        refine ⟨81271742336090046177727729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108362323114786728236970305 81271742336090046177727729)
        ·
          refine ⟨60953806752067534633295797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81271742336090046177727729 60953806752067534633295797)
          ·
            refine ⟨5714419383006331371871481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60953806752067534633295797 5714419383006331371871481)
            ·
              refine ⟨4285814537254748528903611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5714419383006331371871481 4285814537254748528903611)
              ·
                refine ⟨6428721805882122793355417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4285814537254748528903611 6428721805882122793355417)
                ·
                  refine ⟨4821541354411592095016563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6428721805882122793355417 4821541354411592095016563)
                  ·
                    refine ⟨7232312031617388142524845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4821541354411592095016563 7232312031617388142524845)
                    ·
                      refine ⟨2712117011856520553446817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7232312031617388142524845 2712117011856520553446817)
                      ·
                        rfl

theorem cell23_5281829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_5281829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281829 prefixEnd_5281829 := by exact prefixLift 5281829
  have htrace : WordTrace (prefixWord ++ tailWord_5281829) baseStart_5281829 baseEnd_5281829 := by
    simpa [prefixWord, tailWord_5281829, baseEnd_5281829] using wordTrace_append hprefix tailTrace_5281829
  have hstable : (prefixWord ++ tailWord_5281829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281829).length < 2 ^ (prefixWord ++ tailWord_5281829).sum := by decide
  have hdescent : baseEnd_5281829 < baseStart_5281829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281835 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 6, 2, 2]
def baseStart_5281835 : Nat := 118140960795 + 5281835 * 2 ^ 59
def prefixEnd_5281835 : Nat := 4983230072969 + 3 ^ 40 * 5281835 * 2
def baseEnd_5281835 : Nat := 2712120092740447529971789

theorem tailTrace_5281835 : CollatzResearch.WordTrace tailWord_5281835 prefixEnd_5281835 2712120092740447529971789 := by
  unfold tailWord_5281835
  simp only [CollatzResearch.WordTrace]
  refine ⟨192644348819821335445998959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128429565879880890297332639 192644348819821335445998959)
  ·
    refine ⟨288966523229732003168998439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192644348819821335445998959 288966523229732003168998439)
    ·
      refine ⟨433449784844598004753497659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288966523229732003168998439 433449784844598004753497659)
      ·
        refine ⟨650174677266897007130246489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433449784844598004753497659 650174677266897007130246489)
        ·
          refine ⟨487631007950172755347684867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650174677266897007130246489 487631007950172755347684867)
          ·
            refine ⟨731446511925259133021527301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487631007950172755347684867 731446511925259133021527301)
            ·
              refine ⟨137146220985986087441536369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 731446511925259133021527301 137146220985986087441536369)
              ·
                refine ⟨102859665739489565581152277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137146220985986087441536369 102859665739489565581152277)
                ·
                  refine ⟨4821546831538573386616513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102859665739489565581152277 4821546831538573386616513)
                  ·
                    refine ⟨3616160123653930039962385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4821546831538573386616513 3616160123653930039962385)
                    ·
                      refine ⟨2712120092740447529971789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616160123653930039962385 2712120092740447529971789)
                      ·
                        rfl

theorem cell23_5281835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 2, 2].length) (baseStart_5281835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281835 prefixEnd_5281835 := by exact prefixLift 5281835
  have htrace : WordTrace (prefixWord ++ tailWord_5281835) baseStart_5281835 baseEnd_5281835 := by
    simpa [prefixWord, tailWord_5281835, baseEnd_5281835] using wordTrace_append hprefix tailTrace_5281835
  have hstable : (prefixWord ++ tailWord_5281835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281835).length < 2 ^ (prefixWord ++ tailWord_5281835).sum := by decide
  have hdescent : baseEnd_5281835 < baseStart_5281835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281895 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_5281895 : Nat := 118140960795 + 5281895 * 2 ^ 59
def prefixEnd_5281895 : Nat := 4983230072969 + 3 ^ 40 * 5281895 * 2
def baseEnd_5281895 : Nat := 2712150901579717295221513

theorem tailTrace_5281895 : CollatzResearch.WordTrace tailWord_5281895 prefixEnd_5281895 2712150901579717295221513 := by
  unfold tailWord_5281895
  simp only [CollatzResearch.WordTrace]
  refine ⟨192646537199603965693183139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128431024799735977128788759 192646537199603965693183139)
  ·
    refine ⟨288969805799405948539774709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192646537199603965693183139 288969805799405948539774709)
    ·
      refine ⟨27090919293694307675603879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 288969805799405948539774709 27090919293694307675603879)
      ·
        refine ⟨40636378940541461513405819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27090919293694307675603879 40636378940541461513405819)
        ·
          refine ⟨60954568410812192270108729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40636378940541461513405819 60954568410812192270108729)
          ·
            refine ⟨45715926308109144202581547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60954568410812192270108729 45715926308109144202581547)
            ·
              refine ⟨68573889462163716303872321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45715926308109144202581547 68573889462163716303872321)
              ·
                refine ⟨51430417096622787227904241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68573889462163716303872321 51430417096622787227904241)
                ·
                  refine ⟨38572812822467090420928181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51430417096622787227904241 38572812822467090420928181)
                  ·
                    refine ⟨3616201202106289726962017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38572812822467090420928181 3616201202106289726962017)
                    ·
                      refine ⟨2712150901579717295221513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616201202106289726962017 2712150901579717295221513)
                      ·
                        rfl

theorem cell23_5281895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_5281895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281895 prefixEnd_5281895 := by exact prefixLift 5281895
  have htrace : WordTrace (prefixWord ++ tailWord_5281895) baseStart_5281895 baseEnd_5281895 := by
    simpa [prefixWord, tailWord_5281895, baseEnd_5281895] using wordTrace_append hprefix tailTrace_5281895
  have hstable : (prefixWord ++ tailWord_5281895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281895).length < 2 ^ (prefixWord ++ tailWord_5281895).sum := by decide
  have hdescent : baseEnd_5281895 < baseStart_5281895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281965 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 8]
def baseStart_5281965 : Nat := 118140960795 + 5281965 * 2 ^ 59
def prefixEnd_5281965 : Nat := 4983230072969 + 3 ^ 40 * 5281965 * 2
def baseEnd_5281965 : Nat := 301354093913948002371799

theorem tailTrace_5281965 : CollatzResearch.WordTrace tailWord_5281965 prefixEnd_5281965 301354093913948002371799 := by
  unfold tailWord_5281965
  simp only [CollatzResearch.WordTrace]
  refine ⟨192649090309350367648231349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128432726872900245098820899 192649090309350367648231349)
  ·
    refine ⟨18060852216501596967021689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192649090309350367648231349 18060852216501596967021689)
    ·
      refine ⟨13545639162376197725266267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18060852216501596967021689 13545639162376197725266267)
      ·
        refine ⟨20318458743564296587899401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13545639162376197725266267 20318458743564296587899401)
        ·
          refine ⟨15238844057673222440924551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20318458743564296587899401 15238844057673222440924551)
          ·
            refine ⟨22858266086509833661386827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15238844057673222440924551 22858266086509833661386827)
            ·
              refine ⟨34287399129764750492080241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22858266086509833661386827 34287399129764750492080241)
              ·
                refine ⟨25715549347323562869060181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34287399129764750492080241 25715549347323562869060181)
                ·
                  refine ⟨301354093913948002371799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25715549347323562869060181 301354093913948002371799)
                  ·
                    rfl

theorem cell23_5281965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_5281965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281965 prefixEnd_5281965 := by exact prefixLift 5281965
  have htrace : WordTrace (prefixWord ++ tailWord_5281965) baseStart_5281965 baseEnd_5281965 := by
    simpa [prefixWord, tailWord_5281965, baseEnd_5281965] using wordTrace_append hprefix tailTrace_5281965
  have hstable : (prefixWord ++ tailWord_5281965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281965).length < 2 ^ (prefixWord ++ tailWord_5281965).sum := by decide
  have hdescent : baseEnd_5281965 < baseStart_5281965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5281986 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5281986 : Nat := 118140960795 + 5281986 * 2 ^ 59
def prefixEnd_5281986 : Nat := 4983230072969 + 3 ^ 40 * 5281986 * 2
def baseEnd_5281986 : Nat := 904065876106425479727865

theorem tailTrace_5281986 : CollatzResearch.WordTrace tailWord_5281986 prefixEnd_5281986 904065876106425479727865 := by
  unfold tailWord_5281986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48162464060568572058686453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128433237494849525489830541 48162464060568572058686453)
  ·
    refine ⟨4515231005678303630501855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48162464060568572058686453 4515231005678303630501855)
    ·
      refine ⟨6772846508517455445752783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515231005678303630501855 6772846508517455445752783)
      ·
        refine ⟨10159269762776183168629175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772846508517455445752783 10159269762776183168629175)
        ·
          refine ⟨15238904644164274752943763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159269762776183168629175 15238904644164274752943763)
          ·
            refine ⟨22858356966246412129415645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15238904644164274752943763 22858356966246412129415645)
            ·
              refine ⟨8571883862342404548530867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22858356966246412129415645 8571883862342404548530867)
              ·
                refine ⟨12857825793513606822796301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8571883862342404548530867 12857825793513606822796301)
                ·
                  refine ⟨4821684672567602558548613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12857825793513606822796301 4821684672567602558548613)
                  ·
                    refine ⟨904065876106425479727865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821684672567602558548613 904065876106425479727865)
                    ·
                      rfl

theorem cell23_5281986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5281986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5281986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5281986 prefixEnd_5281986 := by exact prefixLift 5281986
  have htrace : WordTrace (prefixWord ++ tailWord_5281986) baseStart_5281986 baseEnd_5281986 := by
    simpa [prefixWord, tailWord_5281986, baseEnd_5281986] using wordTrace_append hprefix tailTrace_5281986
  have hstable : (prefixWord ++ tailWord_5281986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5281986).length < 2 ^ (prefixWord ++ tailWord_5281986).sum := by decide
  have hdescent : baseEnd_5281986 < baseStart_5281986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5281986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282042 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 2, 4]
def baseStart_5282042 : Nat := 118140960795 + 5282042 * 2 ^ 59
def prefixEnd_5282042 : Nat := 4983230072969 + 3 ^ 40 * 5282042 * 2
def baseEnd_5282042 : Nat := 904075461078642740027779

theorem tailTrace_5282042 : CollatzResearch.WordTrace tailWord_5282042 prefixEnd_5282042 904075461078642740027779 := by
  unfold tailWord_5282042
  simp only [CollatzResearch.WordTrace]
  refine ⟨48162974682517852449696095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128434599153380939865856253 48162974682517852449696095)
  ·
    refine ⟨72244462023776778674544143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48162974682517852449696095 72244462023776778674544143)
    ·
      refine ⟨108366693035665168011816215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72244462023776778674544143 108366693035665168011816215)
      ·
        refine ⟨162550039553497752017724323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108366693035665168011816215 162550039553497752017724323)
        ·
          refine ⟨243825059330246628026586485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162550039553497752017724323 243825059330246628026586485)
          ·
            refine ⟨22858599312210621377492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 243825059330246628026586485 22858599312210621377492483)
            ·
              refine ⟨34287898968315932066238725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22858599312210621377492483 34287898968315932066238725)
              ·
                refine ⟨6428981056559237262419761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34287898968315932066238725 6428981056559237262419761)
                ·
                  refine ⟨4821735792419427946814821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6428981056559237262419761 4821735792419427946814821)
                  ·
                    refine ⟨904075461078642740027779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821735792419427946814821 904075461078642740027779)
                    ·
                      rfl

theorem cell23_5282042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_5282042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282042 prefixEnd_5282042 := by exact prefixLift 5282042
  have htrace : WordTrace (prefixWord ++ tailWord_5282042) baseStart_5282042 baseEnd_5282042 := by
    simpa [prefixWord, tailWord_5282042, baseEnd_5282042] using wordTrace_append hprefix tailTrace_5282042
  have hstable : (prefixWord ++ tailWord_5282042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282042).length < 2 ^ (prefixWord ++ tailWord_5282042).sum := by decide
  have hdescent : baseEnd_5282042 < baseStart_5282042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282049 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_5282049 : Nat := 118140960795 + 5282049 * 2 ^ 59
def prefixEnd_5282049 : Nat := 4983230072969 + 3 ^ 40 * 5282049 * 2
def baseEnd_5282049 : Nat := 2712229977600509692695805

theorem tailTrace_5282049 : CollatzResearch.WordTrace tailWord_5282049 prefixEnd_5282049 2712229977600509692695805 := by
  unfold tailWord_5282049
  simp only [CollatzResearch.WordTrace]
  refine ⟨192652154041046049994289201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128434769360697366662859467 192652154041046049994289201)
  ·
    refine ⟨144489115530784537495716901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192652154041046049994289201 144489115530784537495716901)
    ·
      refine ⟨27091709162022100780446919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144489115530784537495716901 27091709162022100780446919)
      ·
        refine ⟨40637563743033151170670379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27091709162022100780446919 40637563743033151170670379)
        ·
          refine ⟨60956345614549726756005569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40637563743033151170670379 60956345614549726756005569)
          ·
            refine ⟨45717259210912295067004177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60956345614549726756005569 45717259210912295067004177)
            ·
              refine ⟨34287944408184221300253133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45717259210912295067004177 34287944408184221300253133)
              ·
                refine ⟨12857979153069082987594925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34287944408184221300253133 12857979153069082987594925)
                ·
                  refine ⟨4821742182400906120348097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12857979153069082987594925 4821742182400906120348097)
                  ·
                    refine ⟨3616306636800679590261073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4821742182400906120348097 3616306636800679590261073)
                    ·
                      refine ⟨2712229977600509692695805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616306636800679590261073 2712229977600509692695805)
                      ·
                        rfl

theorem cell23_5282049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_5282049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282049 prefixEnd_5282049 := by exact prefixLift 5282049
  have htrace : WordTrace (prefixWord ++ tailWord_5282049) baseStart_5282049 baseEnd_5282049 := by
    simpa [prefixWord, tailWord_5282049, baseEnd_5282049] using wordTrace_append hprefix tailTrace_5282049
  have hstable : (prefixWord ++ tailWord_5282049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282049).length < 2 ^ (prefixWord ++ tailWord_5282049).sum := by decide
  have hdescent : baseEnd_5282049 < baseStart_5282049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282062 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_5282062 : Nat := 118140960795 + 5282062 * 2 ^ 59
def prefixEnd_5282062 : Nat := 4983230072969 + 3 ^ 40 * 5282062 * 2
def baseEnd_5282062 : Nat := 2712236652849018141833245

theorem tailTrace_5282062 : CollatzResearch.WordTrace tailWord_5282062 prefixEnd_5282062 2712236652849018141833245 := by
  unfold tailWord_5282062
  simp only [CollatzResearch.WordTrace]
  refine ⟨24081578523749869151814055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128435085459999302143008293 24081578523749869151814055)
  ·
    refine ⟨36122367785624803727721083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24081578523749869151814055 36122367785624803727721083)
    ·
      refine ⟨54183551678437205591581625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36122367785624803727721083 54183551678437205591581625)
      ·
        refine ⟨40637663758827904193686219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54183551678437205591581625 40637663758827904193686219)
        ·
          refine ⟨60956495638241856290529329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40637663758827904193686219 60956495638241856290529329)
          ·
            refine ⟨45717371728681392217896997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60956495638241856290529329 45717371728681392217896997)
            ·
              refine ⟨8572007199127761040855687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45717371728681392217896997 8572007199127761040855687)
              ·
                refine ⟨12858010798691641561283531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572007199127761040855687 12858010798691641561283531)
                ·
                  refine ⟨19287016198037462341925297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12858010798691641561283531 19287016198037462341925297)
                  ·
                    refine ⟨14465262148528096756443973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19287016198037462341925297 14465262148528096756443973)
                    ·
                      refine ⟨2712236652849018141833245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14465262148528096756443973 2712236652849018141833245)
                      ·
                        rfl

theorem cell23_5282062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_5282062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282062 prefixEnd_5282062 := by exact prefixLift 5282062
  have htrace : WordTrace (prefixWord ++ tailWord_5282062) baseStart_5282062 baseEnd_5282062 := by
    simpa [prefixWord, tailWord_5282062, baseEnd_5282062] using wordTrace_append hprefix tailTrace_5282062
  have hstable : (prefixWord ++ tailWord_5282062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282062).length < 2 ^ (prefixWord ++ tailWord_5282062).sum := by decide
  have hdescent : baseEnd_5282062 < baseStart_5282062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282093 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5282093 : Nat := 118140960795 + 5282093 * 2 ^ 59
def prefixEnd_5282093 : Nat := 4983230072969 + 3 ^ 40 * 5282093 * 2
def baseEnd_5282093 : Nat := 904084190249769173515201

theorem tailTrace_5282093 : CollatzResearch.WordTrace tailWord_5282093 prefixEnd_5282093 904084190249769173515201 := by
  unfold tailWord_5282093
  simp only [CollatzResearch.WordTrace]
  refine ⟨192653758852886645508890933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128435839235257763672593955 192653758852886645508890933)
  ·
    refine ⟨18061289892458123016458525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192653758852886645508890933 18061289892458123016458525)
    ·
      refine ⟨6772983709671796131171947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18061289892458123016458525 6772983709671796131171947)
      ·
        refine ⟨10159475564507694196757921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772983709671796131171947 10159475564507694196757921)
        ·
          refine ⟨7619606673380770647568441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10159475564507694196757921 7619606673380770647568441)
          ·
            refine ⟨5714705005035577985676331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7619606673380770647568441 5714705005035577985676331)
            ·
              refine ⟨8572057507553366978514497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5714705005035577985676331 8572057507553366978514497)
              ·
                refine ⟨6429043130665025233885873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8572057507553366978514497 6429043130665025233885873)
                ·
                  refine ⟨4821782347998768925414405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6429043130665025233885873 4821782347998768925414405)
                  ·
                    refine ⟨904084190249769173515201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4821782347998768925414405 904084190249769173515201)
                    ·
                      rfl

theorem cell23_5282093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5282093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282093 prefixEnd_5282093 := by exact prefixLift 5282093
  have htrace : WordTrace (prefixWord ++ tailWord_5282093) baseStart_5282093 baseEnd_5282093 := by
    simpa [prefixWord, tailWord_5282093, baseEnd_5282093] using wordTrace_append hprefix tailTrace_5282093
  have hstable : (prefixWord ++ tailWord_5282093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282093).length < 2 ^ (prefixWord ++ tailWord_5282093).sum := by decide
  have hdescent : baseEnd_5282093 < baseStart_5282093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282115 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 2, 6]
def baseStart_5282115 : Nat := 118140960795 + 5282115 * 2 ^ 59
def prefixEnd_5282115 : Nat := 4983230072969 + 3 ^ 40 * 5282115 * 2
def baseEnd_5282115 : Nat := 904087955774568811490167

theorem tailTrace_5282115 : CollatzResearch.WordTrace tailWord_5282115 prefixEnd_5282115 904087955774568811490167 := by
  unfold tailWord_5282115
  simp only [CollatzResearch.WordTrace]
  refine ⟨192654561258806943266191799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128436374172537962177461199 192654561258806943266191799)
  ·
    refine ⟨288981841888210414899287699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192654561258806943266191799 288981841888210414899287699)
    ·
      refine ⟨433472762832315622348931549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288981841888210414899287699 433472762832315622348931549)
      ·
        refine ⟨162552286062118358380849331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433472762832315622348931549 162552286062118358380849331)
        ·
          refine ⟨243828429093177537571273997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162552286062118358380849331 243828429093177537571273997)
          ·
            refine ⟨91435660909941576589227749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243828429093177537571273997 91435660909941576589227749)
            ·
              refine ⟨17144186420614045610480203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91435660909941576589227749 17144186420614045610480203)
              ·
                refine ⟨25716279630921068415720305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17144186420614045610480203 25716279630921068415720305)
                ·
                  refine ⟨19287209723190801311790229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25716279630921068415720305 19287209723190801311790229)
                  ·
                    refine ⟨904087955774568811490167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19287209723190801311790229 904087955774568811490167)
                    ·
                      rfl

theorem cell23_5282115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 6].length) (baseStart_5282115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282115 prefixEnd_5282115 := by exact prefixLift 5282115
  have htrace : WordTrace (prefixWord ++ tailWord_5282115) baseStart_5282115 baseEnd_5282115 := by
    simpa [prefixWord, tailWord_5282115, baseEnd_5282115] using wordTrace_append hprefix tailTrace_5282115
  have hstable : (prefixWord ++ tailWord_5282115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282115).length < 2 ^ (prefixWord ++ tailWord_5282115).sum := by decide
  have hdescent : baseEnd_5282115 < baseStart_5282115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282162 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_5282162 : Nat := 118140960795 + 5282162 * 2 ^ 59
def prefixEnd_5282162 : Nat := 4983230072969 + 3 ^ 40 * 5282162 * 2
def baseEnd_5282162 : Nat := 301365333434940861175865

theorem tailTrace_5282162 : CollatzResearch.WordTrace tailWord_5282162 prefixEnd_5282162 301365333434940861175865 := by
  unfold tailWord_5282162
  simp only [CollatzResearch.WordTrace]
  refine ⟨48164068872409167573288185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128437516993091113528768493 48164068872409167573288185)
  ·
    refine ⟨36123051654306875679966139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48164068872409167573288185 36123051654306875679966139)
    ·
      refine ⟨54184577481460313519949209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36123051654306875679966139 54184577481460313519949209)
      ·
        refine ⟨40638433111095235139961907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54184577481460313519949209 40638433111095235139961907)
        ·
          refine ⟨60957649666642852709942861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40638433111095235139961907 60957649666642852709942861)
          ·
            refine ⟨22859118624991069766228573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60957649666642852709942861 22859118624991069766228573)
            ·
              refine ⟨8572169484371651162335715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22859118624991069766228573 8572169484371651162335715)
              ·
                refine ⟨12858254226557476743503573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572169484371651162335715 12858254226557476743503573)
                ·
                  refine ⟨301365333434940861175865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12858254226557476743503573 301365333434940861175865)
                  ·
                    rfl

theorem cell23_5282162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_5282162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282162 prefixEnd_5282162 := by exact prefixLift 5282162
  have htrace : WordTrace (prefixWord ++ tailWord_5282162) baseStart_5282162 baseEnd_5282162 := by
    simpa [prefixWord, tailWord_5282162, baseEnd_5282162] using wordTrace_append hprefix tailTrace_5282162
  have hstable : (prefixWord ++ tailWord_5282162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282162).length < 2 ^ (prefixWord ++ tailWord_5282162).sum := by decide
  have hdescent : baseEnd_5282162 < baseStart_5282162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282173 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_5282173 : Nat := 118140960795 + 5282173 * 2 ^ 59
def prefixEnd_5282173 : Nat := 4983230072969 + 3 ^ 40 * 5282173 * 2
def baseEnd_5282173 : Nat := 2712293649201667207545235

theorem tailTrace_5282173 : CollatzResearch.WordTrace tailWord_5282173 prefixEnd_5282173 2712293649201667207545235 := by
  unfold tailWord_5282173
  simp only [CollatzResearch.WordTrace]
  refine ⟨192656676692596819171803173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128437784461731212781202115 192656676692596819171803173)
  ·
    refine ⟨36123126879861903594713095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192656676692596819171803173 36123126879861903594713095)
    ·
      refine ⟨54184690319792855392069643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36123126879861903594713095 54184690319792855392069643)
      ·
        refine ⟨81277035479689283088104465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54184690319792855392069643 81277035479689283088104465)
        ·
          refine ⟨60957776609766962316078349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81277035479689283088104465 60957776609766962316078349)
          ·
            refine ⟨22859166228662610868529381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60957776609766962316078349 22859166228662610868529381)
            ·
              refine ⟨4286093667874239537849259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22859166228662610868529381 4286093667874239537849259)
              ·
                refine ⟨6429140501811359306773889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286093667874239537849259 6429140501811359306773889)
                ·
                  refine ⟨4821855376358519480080417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6429140501811359306773889 4821855376358519480080417)
                  ·
                    refine ⟨3616391532268889610060313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4821855376358519480080417 3616391532268889610060313)
                    ·
                      refine ⟨2712293649201667207545235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616391532268889610060313 2712293649201667207545235)
                      ·
                        rfl

theorem cell23_5282173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_5282173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282173 prefixEnd_5282173 := by exact prefixLift 5282173
  have htrace : WordTrace (prefixWord ++ tailWord_5282173) baseStart_5282173 baseEnd_5282173 := by
    simpa [prefixWord, tailWord_5282173, baseEnd_5282173] using wordTrace_append hprefix tailTrace_5282173
  have hstable : (prefixWord ++ tailWord_5282173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282173).length < 2 ^ (prefixWord ++ tailWord_5282173).sum := by decide
  have hdescent : baseEnd_5282173 < baseStart_5282173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282202 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5282202 : Nat := 118140960795 + 5282202 * 2 ^ 59
def prefixEnd_5282202 : Nat := 4983230072969 + 3 ^ 40 * 5282202 * 2
def baseEnd_5282202 : Nat := 2712308540140647594082601

theorem tailTrace_5282202 : CollatzResearch.WordTrace tailWord_5282202 prefixEnd_5282202 2712308540140647594082601 := by
  unfold tailWord_5282202
  simp only [CollatzResearch.WordTrace]
  refine ⟨48164433602372939281152215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128438489606327838083072573 48164433602372939281152215)
  ·
    refine ⟨72246650403559408921728323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48164433602372939281152215 72246650403559408921728323)
    ·
      refine ⟨108369975605339113382592485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72246650403559408921728323 108369975605339113382592485)
      ·
        refine ⟨20319370426001083759236091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108369975605339113382592485 20319370426001083759236091)
        ·
          refine ⟨30479055639001625638854137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20319370426001083759236091 30479055639001625638854137)
          ·
            refine ⟨22859291729251219229140603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30479055639001625638854137 22859291729251219229140603)
            ·
              refine ⟨34288937593876828843710905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22859291729251219229140603 34288937593876828843710905)
              ·
                refine ⟨25716703195407621632783179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34288937593876828843710905 25716703195407621632783179)
                ·
                  refine ⟨38575054793111432449174769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25716703195407621632783179 38575054793111432449174769)
                  ·
                    refine ⟨28931291094833574336881077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38575054793111432449174769 28931291094833574336881077)
                    ·
                      refine ⟨2712308540140647594082601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28931291094833574336881077 2712308540140647594082601)
                      ·
                        rfl

theorem cell23_5282202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5282202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282202 prefixEnd_5282202 := by exact prefixLift 5282202
  have htrace : WordTrace (prefixWord ++ tailWord_5282202) baseStart_5282202 baseEnd_5282202 := by
    simpa [prefixWord, tailWord_5282202, baseEnd_5282202] using wordTrace_append hprefix tailTrace_5282202
  have hstable : (prefixWord ++ tailWord_5282202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282202).length < 2 ^ (prefixWord ++ tailWord_5282202).sum := by decide
  have hdescent : baseEnd_5282202 < baseStart_5282202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282216 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5282216 : Nat := 118140960795 + 5282216 * 2 ^ 59
def prefixEnd_5282216 : Nat := 4983230072969 + 3 ^ 40 * 5282216 * 2
def baseEnd_5282216 : Nat := 2712315728869810539307537

theorem tailTrace_5282216 : CollatzResearch.WordTrace tailWord_5282216 prefixEnd_5282216 2712315728869810539307537 := by
  unfold tailWord_5282216
  simp only [CollatzResearch.WordTrace]
  refine ⟨96329122515720518757809251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128438830020960691677079001 96329122515720518757809251)
  ·
    refine ⟨144493683773580778136713877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96329122515720518757809251 144493683773580778136713877)
    ·
      refine ⟨6773141426886598975158463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 144493683773580778136713877 6773141426886598975158463)
      ·
        refine ⟨10159712140329898462737695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773141426886598975158463 10159712140329898462737695)
        ·
          refine ⟨15239568210494847694106543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10159712140329898462737695 15239568210494847694106543)
          ·
            refine ⟨22859352315742271541159815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15239568210494847694106543 22859352315742271541159815)
            ·
              refine ⟨34289028473613407311739723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22859352315742271541159815 34289028473613407311739723)
              ·
                refine ⟨51433542710420110967609585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34289028473613407311739723 51433542710420110967609585)
                ·
                  refine ⟨38575157032815083225707189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51433542710420110967609585 38575157032815083225707189)
                  ·
                    refine ⟨3616420971826414052410049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38575157032815083225707189 3616420971826414052410049)
                    ·
                      refine ⟨2712315728869810539307537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616420971826414052410049 2712315728869810539307537)
                      ·
                        rfl

theorem cell23_5282216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5282216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282216 prefixEnd_5282216 := by exact prefixLift 5282216
  have htrace : WordTrace (prefixWord ++ tailWord_5282216) baseStart_5282216 baseEnd_5282216 := by
    simpa [prefixWord, tailWord_5282216, baseEnd_5282216] using wordTrace_append hprefix tailTrace_5282216
  have hstable : (prefixWord ++ tailWord_5282216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282216).length < 2 ^ (prefixWord ++ tailWord_5282216).sum := by decide
  have hdescent : baseEnd_5282216 < baseStart_5282216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282232 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_5282232 : Nat := 118140960795 + 5282232 * 2 ^ 59
def prefixEnd_5282232 : Nat := 4983230072969 + 3 ^ 40 * 5282232 * 2
def baseEnd_5282232 : Nat := 2712323944560282476707463

theorem tailTrace_5282232 : CollatzResearch.WordTrace tailWord_5282232 prefixEnd_5282232 2712323944560282476707463 := by
  unfold tailWord_5282232
  simp only [CollatzResearch.WordTrace]
  refine ⟨96329414299691536124100475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128439219066255381498800633 96329414299691536124100475)
  ·
    refine ⟨144494121449537304186150713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96329414299691536124100475 144494121449537304186150713)
    ·
      refine ⟨108370591087152978139613035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144494121449537304186150713 108370591087152978139613035)
      ·
        refine ⟨162555886630729467209419553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108370591087152978139613035 162555886630729467209419553)
        ·
          refine ⟨121916914973047100407064665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162555886630729467209419553 121916914973047100407064665)
          ·
            refine ⟨91437686229785325305298499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121916914973047100407064665 91437686229785325305298499)
            ·
              refine ⟨137156529344677987957947749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91437686229785325305298499 137156529344677987957947749)
              ·
                refine ⟨25716849252127122742115203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137156529344677987957947749 25716849252127122742115203)
                ·
                  refine ⟨38575273878190684113172805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25716849252127122742115203 38575273878190684113172805)
                  ·
                    refine ⟨7232863852160753271219901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38575273878190684113172805 7232863852160753271219901)
                    ·
                      refine ⟨2712323944560282476707463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7232863852160753271219901 2712323944560282476707463)
                      ·
                        rfl

theorem cell23_5282232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_5282232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282232 prefixEnd_5282232 := by exact prefixLift 5282232
  have htrace : WordTrace (prefixWord ++ tailWord_5282232) baseStart_5282232 baseEnd_5282232 := by
    simpa [prefixWord, tailWord_5282232, baseEnd_5282232] using wordTrace_append hprefix tailTrace_5282232
  have hstable : (prefixWord ++ tailWord_5282232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282232).length < 2 ^ (prefixWord ++ tailWord_5282232).sum := by decide
  have hdescent : baseEnd_5282232 < baseStart_5282232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282249 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 3]
def baseStart_5282249 : Nat := 118140960795 + 5282249 * 2 ^ 59
def prefixEnd_5282249 : Nat := 4983230072969 + 3 ^ 40 * 5282249 * 2
def baseEnd_5282249 : Nat := 2712332673731408910194885

theorem tailTrace_5282249 : CollatzResearch.WordTrace tailWord_5282249 prefixEnd_5282249 2712332673731408910194885 := by
  unfold tailWord_5282249
  simp only [CollatzResearch.WordTrace]
  refine ⟨192659448640321484151569801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128439632426880989434379867 192659448640321484151569801)
  ·
    refine ⟨144494586480241113113677351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192659448640321484151569801 144494586480241113113677351)
    ·
      refine ⟨216741879720361669670516027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144494586480241113113677351 216741879720361669670516027)
      ·
        refine ⟨325112819580542504505774041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216741879720361669670516027 325112819580542504505774041)
        ·
          refine ⟨243834614685406878379330531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325112819580542504505774041 243834614685406878379330531)
          ·
            refine ⟨365751922028110317568995797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243834614685406878379330531 365751922028110317568995797)
            ·
              refine ⟨8572310672533835568023339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 365751922028110317568995797 8572310672533835568023339)
              ·
                refine ⟨12858466008800753352035009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572310672533835568023339 12858466008800753352035009)
                ·
                  refine ⟨9643849506600565014026257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12858466008800753352035009 9643849506600565014026257)
                  ·
                    refine ⟨7232887129950423760519693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9643849506600565014026257 7232887129950423760519693)
                    ·
                      refine ⟨2712332673731408910194885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7232887129950423760519693 2712332673731408910194885)
                      ·
                        rfl

theorem cell23_5282249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_5282249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282249 prefixEnd_5282249 := by exact prefixLift 5282249
  have htrace : WordTrace (prefixWord ++ tailWord_5282249) baseStart_5282249 baseEnd_5282249 := by
    simpa [prefixWord, tailWord_5282249, baseEnd_5282249] using wordTrace_append hprefix tailTrace_5282249
  have hstable : (prefixWord ++ tailWord_5282249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282249).length < 2 ^ (prefixWord ++ tailWord_5282249).sum := by decide
  have hdescent : baseEnd_5282249 < baseStart_5282249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282286 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 6]
def baseStart_5282286 : Nat := 118140960795 + 5282286 * 2 ^ 59
def prefixEnd_5282286 : Nat := 4983230072969 + 3 ^ 40 * 5282286 * 2
def baseEnd_5282286 : Nat := 301372408057291696159135

theorem tailTrace_5282286 : CollatzResearch.WordTrace tailWord_5282286 prefixEnd_5282286 301372408057291696159135 := by
  unfold tailWord_5282286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082599767648429933833339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128440532094124959647111141 24082599767648429933833339)
  ·
    refine ⟨36123899651472644900750009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082599767648429933833339 36123899651472644900750009)
    ·
      refine ⟨27092924738604483675562507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36123899651472644900750009 27092924738604483675562507)
      ·
        refine ⟨40639387107906725513343761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27092924738604483675562507 40639387107906725513343761)
        ·
          refine ⟨30479540330930044135007821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40639387107906725513343761 30479540330930044135007821)
          ·
            refine ⟨11429827624098766550627933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30479540330930044135007821 11429827624098766550627933)
            ·
              refine ⟨4286185359037037456485475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11429827624098766550627933 4286185359037037456485475)
              ·
                refine ⟨6429278038555556184728213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286185359037037456485475 6429278038555556184728213)
                ·
                  refine ⟨301372408057291696159135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6429278038555556184728213 301372408057291696159135)
                  ·
                    rfl

theorem cell23_5282286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_5282286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282286 prefixEnd_5282286 := by exact prefixLift 5282286
  have htrace : WordTrace (prefixWord ++ tailWord_5282286) baseStart_5282286 baseEnd_5282286 := by
    simpa [prefixWord, tailWord_5282286, baseEnd_5282286] using wordTrace_append hprefix tailTrace_5282286
  have hstable : (prefixWord ++ tailWord_5282286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282286).length < 2 ^ (prefixWord ++ tailWord_5282286).sum := by decide
  have hdescent : baseEnd_5282286 < baseStart_5282286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282289 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 3, 5, 2]
def baseStart_5282289 : Nat := 118140960795 + 5282289 * 2 ^ 59
def prefixEnd_5282289 : Nat := 4983230072969 + 3 ^ 40 * 5282289 * 2
def baseEnd_5282289 : Nat := 2712353212957588753694701

theorem tailTrace_5282289 : CollatzResearch.WordTrace tailWord_5282289 prefixEnd_5282289 2712353212957588753694701 := by
  unfold tailWord_5282289
  simp only [CollatzResearch.WordTrace]
  refine ⟨192660907560176570983025921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128440605040117713988683947 192660907560176570983025921)
  ·
    refine ⟨144495680670132428237269441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192660907560176570983025921 144495680670132428237269441)
    ·
      refine ⟨108371760502599321177952081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144495680670132428237269441 108371760502599321177952081)
      ·
        refine ⟨81278820376949490883464061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108371760502599321177952081 81278820376949490883464061)
        ·
          refine ⟨30479557641356059081299023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81278820376949490883464061 30479557641356059081299023)
          ·
            refine ⟨45719336462034088621948535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30479557641356059081299023 45719336462034088621948535)
            ·
              refine ⟨68579004693051132932922803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45719336462034088621948535 68579004693051132932922803)
              ·
                refine ⟨102868507039576699399384205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68579004693051132932922803 102868507039576699399384205)
                ·
                  refine ⟨38575690139841262274769077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102868507039576699399384205 38575690139841262274769077)
                  ·
                    refine ⟨3616470950610118338259601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38575690139841262274769077 3616470950610118338259601)
                    ·
                      refine ⟨2712353212957588753694701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616470950610118338259601 2712353212957588753694701)
                      ·
                        rfl

theorem cell23_5282289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_5282289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282289 prefixEnd_5282289 := by exact prefixLift 5282289
  have htrace : WordTrace (prefixWord ++ tailWord_5282289) baseStart_5282289 baseEnd_5282289 := by
    simpa [prefixWord, tailWord_5282289, baseEnd_5282289] using wordTrace_append hprefix tailTrace_5282289
  have hstable : (prefixWord ++ tailWord_5282289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282289).length < 2 ^ (prefixWord ++ tailWord_5282289).sum := by decide
  have hdescent : baseEnd_5282289 < baseStart_5282289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282312 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_5282312 : Nat := 118140960795 + 5282312 * 2 ^ 59
def prefixEnd_5282312 : Nat := 4983230072969 + 3 ^ 40 * 5282312 * 2
def baseEnd_5282312 : Nat := 904121674337547387902365

theorem tailTrace_5282312 : CollatzResearch.WordTrace tailWord_5282312 prefixEnd_5282312 904121674337547387902365 := by
  unfold tailWord_5282312
  simp only [CollatzResearch.WordTrace]
  refine ⟨96330873219546622955556595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128441164292728830607408793 96330873219546622955556595)
  ·
    refine ⟨144496309829319934433334893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96330873219546622955556595 144496309829319934433334893)
    ·
      refine ⟨54186116185994975412500585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144496309829319934433334893 54186116185994975412500585)
      ·
        refine ⟨40639587139496231559375439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54186116185994975412500585 40639587139496231559375439)
        ·
          refine ⟨60959380709244347339063159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40639587139496231559375439 60959380709244347339063159)
          ·
            refine ⟨91439071063866521008594739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60959380709244347339063159 91439071063866521008594739)
            ·
              refine ⟨137158606595799781512892109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91439071063866521008594739 137158606595799781512892109)
              ·
                refine ⟨51434477473424918067334541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137158606595799781512892109 51434477473424918067334541)
                ·
                  refine ⟨19287929052534344275250453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51434477473424918067334541 19287929052534344275250453)
                  ·
                    refine ⟨904121674337547387902365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19287929052534344275250453 904121674337547387902365)
                    ·
                      rfl

theorem cell23_5282312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_5282312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282312 prefixEnd_5282312 := by exact prefixLift 5282312
  have htrace : WordTrace (prefixWord ++ tailWord_5282312) baseStart_5282312 baseEnd_5282312 := by
    simpa [prefixWord, tailWord_5282312, baseEnd_5282312] using wordTrace_append hprefix tailTrace_5282312
  have hstable : (prefixWord ++ tailWord_5282312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282312).length < 2 ^ (prefixWord ++ tailWord_5282312).sum := by decide
  have hdescent : baseEnd_5282312 < baseStart_5282312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282339 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5]
def baseStart_5282339 : Nat := 118140960795 + 5282339 * 2 ^ 59
def prefixEnd_5282339 : Nat := 4983230072969 + 3 ^ 40 * 5282339 * 2
def baseEnd_5282339 : Nat := 2712378886990313558069471

theorem tailTrace_5282339 : CollatzResearch.WordTrace tailWord_5282339 prefixEnd_5282339 2712378886990313558069471 := by
  unfold tailWord_5282339
  simp only [CollatzResearch.WordTrace]
  refine ⟨192662731209995429522346071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128441820806663619681564047 192662731209995429522346071)
  ·
    refine ⟨288994096814993144283519107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192662731209995429522346071 288994096814993144283519107)
    ·
      refine ⟨433491145222489716425278661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288994096814993144283519107 433491145222489716425278661)
      ·
        refine ⟨81279589729216821829739749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 433491145222489716425278661 81279589729216821829739749)
        ·
          refine ⟨15239923074228154093076203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81279589729216821829739749 15239923074228154093076203)
          ·
            refine ⟨22859884611342231139614305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15239923074228154093076203 22859884611342231139614305)
            ·
              refine ⟨17144913458506673354710729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22859884611342231139614305 17144913458506673354710729)
              ·
                refine ⟨12858685093880005016033047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17144913458506673354710729 12858685093880005016033047)
                ·
                  refine ⟨19288027640820007524049571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12858685093880005016033047 19288027640820007524049571)
                  ·
                    refine ⟨28932041461230011286074357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19288027640820007524049571 28932041461230011286074357)
                    ·
                      refine ⟨2712378886990313558069471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28932041461230011286074357 2712378886990313558069471)
                      ·
                        rfl

theorem cell23_5282339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_5282339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282339 prefixEnd_5282339 := by exact prefixLift 5282339
  have htrace : WordTrace (prefixWord ++ tailWord_5282339) baseStart_5282339 baseEnd_5282339 := by
    simpa [prefixWord, tailWord_5282339, baseEnd_5282339] using wordTrace_append hprefix tailTrace_5282339
  have hstable : (prefixWord ++ tailWord_5282339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282339).length < 2 ^ (prefixWord ++ tailWord_5282339).sum := by decide
  have hdescent : baseEnd_5282339 < baseStart_5282339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282350 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5282350 : Nat := 118140960795 + 5282350 * 2 ^ 59
def prefixEnd_5282350 : Nat := 4983230072969 + 3 ^ 40 * 5282350 * 2
def baseEnd_5282350 : Nat := 904128178425837671677307

theorem tailTrace_5282350 : CollatzResearch.WordTrace tailWord_5282350 prefixEnd_5282350 904128178425837671677307 := by
  unfold tailWord_5282350
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082891551619447300124563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128442088275303718933997669 24082891551619447300124563)
  ·
    refine ⟨36124337327429170950186845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082891551619447300124563 36124337327429170950186845)
    ·
      refine ⟨13546626497785939106320067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36124337327429170950186845 13546626497785939106320067)
      ·
        refine ⟨20319939746678908659480101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13546626497785939106320067 20319939746678908659480101)
        ·
          refine ⟨3809988702502295373652519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20319939746678908659480101 3809988702502295373652519)
          ·
            refine ⟨5714983053753443060478779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3809988702502295373652519 5714983053753443060478779)
            ·
              refine ⟨8572474580630164590718169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5714983053753443060478779 8572474580630164590718169)
              ·
                refine ⟨6429355935472623443038627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8572474580630164590718169 6429355935472623443038627)
                ·
                  refine ⟨9644033903208935164557941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429355935472623443038627 9644033903208935164557941)
                  ·
                    refine ⟨904128178425837671677307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9644033903208935164557941 904128178425837671677307)
                    ·
                      rfl

theorem cell23_5282350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5282350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282350 prefixEnd_5282350 := by exact prefixLift 5282350
  have htrace : WordTrace (prefixWord ++ tailWord_5282350) baseStart_5282350 baseEnd_5282350 := by
    simpa [prefixWord, tailWord_5282350, baseEnd_5282350] using wordTrace_append hprefix tailTrace_5282350
  have hstable : (prefixWord ++ tailWord_5282350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282350).length < 2 ^ (prefixWord ++ tailWord_5282350).sum := by decide
  have hdescent : baseEnd_5282350 < baseStart_5282350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282373 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 1, 2, 3]
def baseStart_5282373 : Nat := 118140960795 + 5282373 * 2 ^ 59
def prefixEnd_5282373 : Nat := 4983230072969 + 3 ^ 40 * 5282373 * 2
def baseEnd_5282373 : Nat := 2712396345332566425044315

theorem tailTrace_5282373 : CollatzResearch.WordTrace tailWord_5282373 prefixEnd_5282373 2712396345332566425044315 := by
  unfold tailWord_5282373
  simp only [CollatzResearch.WordTrace]
  refine ⟨192663971291872253329083773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128442647527914835552722515 192663971291872253329083773)
  ·
    refine ⟨72248989234452094998406415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192663971291872253329083773 72248989234452094998406415)
    ·
      refine ⟨108373483851678142497609623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72248989234452094998406415 108373483851678142497609623)
      ·
        refine ⟨162560225777517213746414435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108373483851678142497609623 162560225777517213746414435)
        ·
          refine ⟨243840338666275820619621653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162560225777517213746414435 243840338666275820619621653)
          ·
            refine ⟨11430015874981679091544765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 243840338666275820619621653 11430015874981679091544765)
            ·
              refine ⟨4286255953118129659329287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11430015874981679091544765 4286255953118129659329287)
              ·
                refine ⟨6429383929677194488993931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286255953118129659329287 6429383929677194488993931)
                ·
                  refine ⟨9644075894515791733490897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429383929677194488993931 9644075894515791733490897)
                  ·
                    refine ⟨7233056920886843800118173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9644075894515791733490897 7233056920886843800118173)
                    ·
                      refine ⟨2712396345332566425044315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7233056920886843800118173 2712396345332566425044315)
                      ·
                        rfl

theorem cell23_5282373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_5282373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282373 prefixEnd_5282373 := by exact prefixLift 5282373
  have htrace : WordTrace (prefixWord ++ tailWord_5282373) baseStart_5282373 baseEnd_5282373 := by
    simpa [prefixWord, tailWord_5282373, baseEnd_5282373] using wordTrace_append hprefix tailTrace_5282373
  have hstable : (prefixWord ++ tailWord_5282373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282373).length < 2 ^ (prefixWord ++ tailWord_5282373).sum := by decide
  have hdescent : baseEnd_5282373 < baseStart_5282373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282413 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5282413 : Nat := 118140960795 + 5282413 * 2 ^ 59
def prefixEnd_5282413 : Nat := 4983230072969 + 3 ^ 40 * 5282413 * 2
def baseEnd_5282413 : Nat := 2712416884558746268544131

theorem tailTrace_5282413 : CollatzResearch.WordTrace tailWord_5282413 prefixEnd_5282413 2712416884558746268544131 := by
  unfold tailWord_5282413
  simp only [CollatzResearch.WordTrace]
  refine ⟨192665430211727340160539893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128443620141151560107026595 192665430211727340160539893)
  ·
    refine ⟨18062384082349438140050615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192665430211727340160539893 18062384082349438140050615)
    ·
      refine ⟨27093576123524157210075923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18062384082349438140050615 27093576123524157210075923)
      ·
        refine ⟨40640364185286235815113885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27093576123524157210075923 40640364185286235815113885)
        ·
          refine ⟨15240136569482338430667707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40640364185286235815113885 15240136569482338430667707)
          ·
            refine ⟨22860204854223507646001561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15240136569482338430667707 22860204854223507646001561)
            ·
              refine ⟨17145153640667630734501171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22860204854223507646001561 17145153640667630734501171)
              ·
                refine ⟨25717730461001446101751757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17145153640667630734501171 25717730461001446101751757)
                ·
                  refine ⟨9644148922875542288156909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25717730461001446101751757 9644148922875542288156909)
                  ·
                    refine ⟨3616555846078328358058841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9644148922875542288156909 3616555846078328358058841)
                    ·
                      refine ⟨2712416884558746268544131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616555846078328358058841 2712416884558746268544131)
                      ·
                        rfl

theorem cell23_5282413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5282413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282413 prefixEnd_5282413 := by exact prefixLift 5282413
  have htrace : WordTrace (prefixWord ++ tailWord_5282413) baseStart_5282413 baseEnd_5282413 := by
    simpa [prefixWord, tailWord_5282413, baseEnd_5282413] using wordTrace_append hprefix tailTrace_5282413
  have hstable : (prefixWord ++ tailWord_5282413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282413).length < 2 ^ (prefixWord ++ tailWord_5282413).sum := by decide
  have hdescent : baseEnd_5282413 < baseStart_5282413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282439 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_5282439 : Nat := 118140960795 + 5282439 * 2 ^ 59
def prefixEnd_5282439 : Nat := 4983230072969 + 3 ^ 40 * 5282439 * 2
def baseEnd_5282439 : Nat := 2712430235055763166819011

theorem tailTrace_5282439 : CollatzResearch.WordTrace tailWord_5282439 prefixEnd_5282439 2712430235055763166819011 := by
  unfold tailWord_5282439
  simp only [CollatzResearch.WordTrace]
  refine ⟨192666378509633146600986371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128444252339755431067324247 192666378509633146600986371)
  ·
    refine ⟨288999567764449719901479557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192666378509633146600986371 288999567764449719901479557)
    ·
      refine ⟨54187418955834322481527417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 288999567764449719901479557 54187418955834322481527417)
      ·
        refine ⟨40640564216875741861145563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54187418955834322481527417 40640564216875741861145563)
        ·
          refine ⟨60960846325313612791718345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40640564216875741861145563 60960846325313612791718345)
          ·
            refine ⟨45720634743985209593788759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60960846325313612791718345 45720634743985209593788759)
            ·
              refine ⟨68580952115977814390683139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45720634743985209593788759 68580952115977814390683139)
              ·
                refine ⟨102871428173966721586024709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68580952115977814390683139 102871428173966721586024709)
                ·
                  refine ⟨19288392782618760297379633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102871428173966721586024709 19288392782618760297379633)
                  ·
                    refine ⟨14466294586964070223034725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19288392782618760297379633 14466294586964070223034725)
                    ·
                      refine ⟨2712430235055763166819011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14466294586964070223034725 2712430235055763166819011)
                      ·
                        rfl

theorem cell23_5282439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_5282439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282439 prefixEnd_5282439 := by exact prefixLift 5282439
  have htrace : WordTrace (prefixWord ++ tailWord_5282439) baseStart_5282439 baseEnd_5282439 := by
    simpa [prefixWord, tailWord_5282439, baseEnd_5282439] using wordTrace_append hprefix tailTrace_5282439
  have hstable : (prefixWord ++ tailWord_5282439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282439).length < 2 ^ (prefixWord ++ tailWord_5282439).sum := by decide
  have hdescent : baseEnd_5282439 < baseStart_5282439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282443 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 2, 2, 2]
def baseStart_5282443 : Nat := 118140960795 + 5282443 * 2 ^ 59
def prefixEnd_5282443 : Nat := 4983230072969 + 3 ^ 40 * 5282443 * 2
def baseEnd_5282443 : Nat := 2712432288978381151168993

theorem tailTrace_5282443 : CollatzResearch.WordTrace tailWord_5282443 prefixEnd_5282443 2712432288978381151168993 := by
  unfold tailWord_5282443
  simp only [CollatzResearch.WordTrace]
  refine ⟨192666524401618655284131983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128444349601079103522754655 192666524401618655284131983)
  ·
    refine ⟨288999786602427982926197975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192666524401618655284131983 288999786602427982926197975)
    ·
      refine ⟨433499679903641974389296963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288999786602427982926197975 433499679903641974389296963)
      ·
        refine ⟨650249519855462961583945445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433499679903641974389296963 650249519855462961583945445)
        ·
          refine ⟨121921784972899305296989771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 650249519855462961583945445 121921784972899305296989771)
          ·
            refine ⟨182882677459348957945484657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121921784972899305296989771 182882677459348957945484657)
            ·
              refine ⟨137162008094511718459113493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182882677459348957945484657 137162008094511718459113493)
              ·
                refine ⟨6429469129430236802770945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137162008094511718459113493 6429469129430236802770945)
                ·
                  refine ⟨4822101847072677602078209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6429469129430236802770945 4822101847072677602078209)
                  ·
                    refine ⟨3616576385304508201558657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4822101847072677602078209 3616576385304508201558657)
                    ·
                      refine ⟨2712432288978381151168993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616576385304508201558657 2712432288978381151168993)
                      ·
                        rfl

theorem cell23_5282443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 2, 2].length) (baseStart_5282443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282443 prefixEnd_5282443 := by exact prefixLift 5282443
  have htrace : WordTrace (prefixWord ++ tailWord_5282443) baseStart_5282443 baseEnd_5282443 := by
    simpa [prefixWord, tailWord_5282443, baseEnd_5282443] using wordTrace_append hprefix tailTrace_5282443
  have hstable : (prefixWord ++ tailWord_5282443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282443).length < 2 ^ (prefixWord ++ tailWord_5282443).sum := by decide
  have hdescent : baseEnd_5282443 < baseStart_5282443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282460 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5282460 : Nat := 118140960795 + 5282460 * 2 ^ 59
def prefixEnd_5282460 : Nat := 4983230072969 + 3 ^ 40 * 5282460 * 2
def baseEnd_5282460 : Nat := 2712441018149507584656415

theorem tailTrace_5282460 : CollatzResearch.WordTrace tailWord_5282460 prefixEnd_5282460 2712441018149507584656415 := by
  unfold tailWord_5282460
  simp only [CollatzResearch.WordTrace]
  refine ⟨96333572221278533593750417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128444762961704711458333889 96333572221278533593750417)
  ·
    refine ⟨72250179165958900195312813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96333572221278533593750417 72250179165958900195312813)
    ·
      refine ⟨27093817187234587573242305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72250179165958900195312813 27093817187234587573242305)
      ·
        refine ⟨20320362890425940679931729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27093817187234587573242305 20320362890425940679931729)
        ·
          refine ⟨15240272167819455509948797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20320362890425940679931729 15240272167819455509948797)
          ·
            refine ⟨5715102062932295816230799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15240272167819455509948797 5715102062932295816230799)
            ·
              refine ⟨8572653094398443724346199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715102062932295816230799 8572653094398443724346199)
              ·
                refine ⟨12858979641597665586519299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572653094398443724346199 12858979641597665586519299)
                ·
                  refine ⟨19288469462396498379778949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12858979641597665586519299 19288469462396498379778949)
                  ·
                    refine ⟨3616588024199343446208553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19288469462396498379778949 3616588024199343446208553)
                    ·
                      refine ⟨2712441018149507584656415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616588024199343446208553 2712441018149507584656415)
                      ·
                        rfl

theorem cell23_5282460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5282460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282460 prefixEnd_5282460 := by exact prefixLift 5282460
  have htrace : WordTrace (prefixWord ++ tailWord_5282460) baseStart_5282460 baseEnd_5282460 := by
    simpa [prefixWord, tailWord_5282460, baseEnd_5282460] using wordTrace_append hprefix tailTrace_5282460
  have hstable : (prefixWord ++ tailWord_5282460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282460).length < 2 ^ (prefixWord ++ tailWord_5282460).sum := by decide
  have hdescent : baseEnd_5282460 < baseStart_5282460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282479 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 1, 7]
def baseStart_5282479 : Nat := 118140960795 + 5282479 * 2 ^ 59
def prefixEnd_5282479 : Nat := 4983230072969 + 3 ^ 40 * 5282479 * 2
def baseEnd_5282479 : Nat := 904150258093981003439609

theorem tailTrace_5282479 : CollatzResearch.WordTrace tailWord_5282479 prefixEnd_5282479 904150258093981003439609 := by
  unfold tailWord_5282479
  simp only [CollatzResearch.WordTrace]
  refine ⟨192667837429488233432442491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128445224952992155621628327 192667837429488233432442491)
  ·
    refine ⟨289001756144232350148663737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192667837429488233432442491 289001756144232350148663737)
    ·
      refine ⟨216751317108174262611497803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289001756144232350148663737 216751317108174262611497803)
      ·
        refine ⟨325126975662261393917246705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216751317108174262611497803 325126975662261393917246705)
        ·
          refine ⟨243845231746696045437935029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325126975662261393917246705 243845231746696045437935029)
          ·
            refine ⟨22860490476252754259806409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 243845231746696045437935029 22860490476252754259806409)
            ·
              refine ⟨17145367857189565694854807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22860490476252754259806409 17145367857189565694854807)
              ·
                refine ⟨25718051785784348542282211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17145367857189565694854807 25718051785784348542282211)
                ·
                  refine ⟨38577077678676522813423317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25718051785784348542282211 38577077678676522813423317)
                  ·
                    refine ⟨904150258093981003439609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38577077678676522813423317 904150258093981003439609)
                    ·
                      rfl

theorem cell23_5282479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_5282479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282479 prefixEnd_5282479 := by exact prefixLift 5282479
  have htrace : WordTrace (prefixWord ++ tailWord_5282479) baseStart_5282479 baseEnd_5282479 := by
    simpa [prefixWord, tailWord_5282479, baseEnd_5282479] using wordTrace_append hprefix tailTrace_5282479
  have hstable : (prefixWord ++ tailWord_5282479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282479).length < 2 ^ (prefixWord ++ tailWord_5282479).sum := by decide
  have hdescent : baseEnd_5282479 < baseStart_5282479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282483 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 5]
def baseStart_5282483 : Nat := 118140960795 + 5282483 * 2 ^ 59
def prefixEnd_5282483 : Nat := 4983230072969 + 3 ^ 40 * 5282483 * 2
def baseEnd_5282483 : Nat := 301383647578284554963201

theorem tailTrace_5282483 : CollatzResearch.WordTrace tailWord_5282483 prefixEnd_5282483 301383647578284554963201 := by
  unfold tailWord_5282483
  simp only [CollatzResearch.WordTrace]
  refine ⟨192667983321473742115588103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128445322214315828077058735 192667983321473742115588103)
  ·
    refine ⟨289001974982210613173382155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192667983321473742115588103 289001974982210613173382155)
    ·
      refine ⟨433502962473315919760073233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289001974982210613173382155 433502962473315919760073233)
      ·
        refine ⟨325127221854986939820054925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433502962473315919760073233 325127221854986939820054925)
        ·
          refine ⟨121922708195620102432520597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325127221854986939820054925 121922708195620102432520597)
          ·
            refine ⟨5715126946669692301524403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121922708195620102432520597 5715126946669692301524403)
            ·
              refine ⟨8572690420004538452286605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715126946669692301524403 8572690420004538452286605)
              ·
                refine ⟨3214758907501701919607477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8572690420004538452286605 3214758907501701919607477)
                ·
                  refine ⟨301383647578284554963201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3214758907501701919607477 301383647578284554963201)
                  ·
                    rfl

theorem cell23_5282483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 5].length) (baseStart_5282483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282483 prefixEnd_5282483 := by exact prefixLift 5282483
  have htrace : WordTrace (prefixWord ++ tailWord_5282483) baseStart_5282483 baseEnd_5282483 := by
    simpa [prefixWord, tailWord_5282483, baseEnd_5282483] using wordTrace_append hprefix tailTrace_5282483
  have hstable : (prefixWord ++ tailWord_5282483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282483).length < 2 ^ (prefixWord ++ tailWord_5282483).sum := by decide
  have hdescent : baseEnd_5282483 < baseStart_5282483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282489 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5282489 : Nat := 118140960795 + 5282489 * 2 ^ 59
def prefixEnd_5282489 : Nat := 4983230072969 + 3 ^ 40 * 5282489 * 2
def baseEnd_5282489 : Nat := 2712455909088487971193781

theorem tailTrace_5282489 : CollatzResearch.WordTrace tailWord_5282489 prefixEnd_5282489 2712455909088487971193781 := by
  unfold tailWord_5282489
  simp only [CollatzResearch.WordTrace]
  refine ⟨192668202159452005140306521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128445468106301336760204347 192668202159452005140306521)
  ·
    refine ⟨144501151619589003855229891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192668202159452005140306521 144501151619589003855229891)
    ·
      refine ⟨216751727429383505782844837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144501151619589003855229891 216751727429383505782844837)
      ·
        refine ⟨40640948893009407334283407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216751727429383505782844837 40640948893009407334283407)
        ·
          refine ⟨60961423339514111001425111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40640948893009407334283407 60961423339514111001425111)
          ·
            refine ⟨91442135009271166502137667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60961423339514111001425111 91442135009271166502137667)
            ·
              refine ⟨137163202513906749753206501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91442135009271166502137667 137163202513906749753206501)
              ·
                refine ⟨25718100471357515578726219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137163202513906749753206501 25718100471357515578726219)
                ·
                  refine ⟨38577150707036273368089329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25718100471357515578726219 38577150707036273368089329)
                  ·
                    refine ⟨28932863030277205026066997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38577150707036273368089329 28932863030277205026066997)
                    ·
                      refine ⟨2712455909088487971193781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28932863030277205026066997 2712455909088487971193781)
                      ·
                        rfl

theorem cell23_5282489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5282489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282489 prefixEnd_5282489 := by exact prefixLift 5282489
  have htrace : WordTrace (prefixWord ++ tailWord_5282489) baseStart_5282489 baseEnd_5282489 := by
    simpa [prefixWord, tailWord_5282489, baseEnd_5282489] using wordTrace_append hprefix tailTrace_5282489
  have hstable : (prefixWord ++ tailWord_5282489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282489).length < 2 ^ (prefixWord ++ tailWord_5282489).sum := by decide
  have hdescent : baseEnd_5282489 < baseStart_5282489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282496 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_5282496 : Nat := 118140960795 + 5282496 * 2 ^ 59
def prefixEnd_5282496 : Nat := 4983230072969 + 3 ^ 40 * 5282496 * 2
def baseEnd_5282496 : Nat := 904153167817689814602083

theorem tailTrace_5282496 : CollatzResearch.WordTrace tailWord_5282496 prefixEnd_5282496 904153167817689814602083 := by
  unfold tailWord_5282496
  simp only [CollatzResearch.WordTrace]
  refine ⟨96334228735213322667905671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128445638313617763557207561 96334228735213322667905671)
  ·
    refine ⟨144501343102819984001858507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96334228735213322667905671 144501343102819984001858507)
    ·
      refine ⟨216752014654229976002787761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144501343102819984001858507 216752014654229976002787761)
      ·
        refine ⟨162564010990672482002090821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216752014654229976002787761 162564010990672482002090821)
        ·
          refine ⟨30480752060751090375392029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162564010990672482002090821 30480752060751090375392029)
          ·
            refine ⟨11430282022781658890772011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30480752060751090375392029 11430282022781658890772011)
            ·
              refine ⟨17145423034172488336158017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430282022781658890772011 17145423034172488336158017)
              ·
                refine ⟨12859067275629366252118513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17145423034172488336158017 12859067275629366252118513)
                ·
                  refine ⟨9644300456722024689088885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12859067275629366252118513 9644300456722024689088885)
                  ·
                    refine ⟨904153167817689814602083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9644300456722024689088885 904153167817689814602083)
                    ·
                      rfl

theorem cell23_5282496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_5282496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282496 prefixEnd_5282496 := by exact prefixLift 5282496
  have htrace : WordTrace (prefixWord ++ tailWord_5282496) baseStart_5282496 baseEnd_5282496 := by
    simpa [prefixWord, tailWord_5282496, baseEnd_5282496] using wordTrace_append hprefix tailTrace_5282496
  have hstable : (prefixWord ++ tailWord_5282496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282496).length < 2 ^ (prefixWord ++ tailWord_5282496).sum := by decide
  have hdescent : baseEnd_5282496 < baseStart_5282496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282500 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 5]
def baseStart_5282500 : Nat := 118140960795 + 5282500 * 2 ^ 59
def prefixEnd_5282500 : Nat := 4983230072969 + 3 ^ 40 * 5282500 * 2
def baseEnd_5282500 : Nat := 301384617486187492017359

theorem tailTrace_5282500 : CollatzResearch.WordTrace tailWord_5282500 prefixEnd_5282500 301384617486187492017359 := by
  unfold tailWord_5282500
  simp only [CollatzResearch.WordTrace]
  refine ⟨96334301681206077009478477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128445735574941436012637969 96334301681206077009478477)
  ·
    refine ⟨36125363130452278878554429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96334301681206077009478477 36125363130452278878554429)
    ·
      refine ⟨13547011173919604579457911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36125363130452278878554429 13547011173919604579457911)
      ·
        refine ⟨20320516760879406869186867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13547011173919604579457911 20320516760879406869186867)
        ·
          refine ⟨30480775141319110303780301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20320516760879406869186867 30480775141319110303780301)
          ·
            refine ⟨11430290677994666363917613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30480775141319110303780301 11430290677994666363917613)
            ·
              refine ⟨4286359004247999886469105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11430290677994666363917613 4286359004247999886469105)
              ·
                refine ⟨3214769253185999914851829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4286359004247999886469105 3214769253185999914851829)
                ·
                  refine ⟨301384617486187492017359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3214769253185999914851829 301384617486187492017359)
                  ·
                    rfl

theorem cell23_5282500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_5282500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282500 prefixEnd_5282500 := by exact prefixLift 5282500
  have htrace : WordTrace (prefixWord ++ tailWord_5282500) baseStart_5282500 baseEnd_5282500 := by
    simpa [prefixWord, tailWord_5282500, baseEnd_5282500] using wordTrace_append hprefix tailTrace_5282500
  have hstable : (prefixWord ++ tailWord_5282500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282500).length < 2 ^ (prefixWord ++ tailWord_5282500).sum := by decide
  have hdescent : baseEnd_5282500 < baseStart_5282500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282506 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_5282506 : Nat := 118140960795 + 5282506 * 2 ^ 59
def prefixEnd_5282506 : Nat := 4983230072969 + 3 ^ 40 * 5282506 * 2
def baseEnd_5282506 : Nat := 2712464638259614404681203

theorem tailTrace_5282506 : CollatzResearch.WordTrace tailWord_5282506 prefixEnd_5282506 2712464638259614404681203 := by
  unfold tailWord_5282506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48167205550097604260918843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128445881466926944695783581 48167205550097604260918843)
  ·
    refine ⟨72250808325146406391378265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48167205550097604260918843 72250808325146406391378265)
    ·
      refine ⟨54188106243859804793533699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72250808325146406391378265 54188106243859804793533699)
      ·
        refine ⟨81282159365789707190300549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54188106243859804793533699 81282159365789707190300549)
        ·
          refine ⟨15240404881085570098181353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81282159365789707190300549 15240404881085570098181353)
          ·
            refine ⟨11430303660814177573636015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15240404881085570098181353 11430303660814177573636015)
            ·
              refine ⟨17145455491221266360454023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11430303660814177573636015 17145455491221266360454023)
              ·
                refine ⟨25718183236831899540681035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17145455491221266360454023 25718183236831899540681035)
                ·
                  refine ⟨38577274855247849311021553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25718183236831899540681035 38577274855247849311021553)
                  ·
                    refine ⟨28932956141435886983266165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38577274855247849311021553 28932956141435886983266165)
                    ·
                      refine ⟨2712464638259614404681203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28932956141435886983266165 2712464638259614404681203)
                      ·
                        rfl

theorem cell23_5282506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_5282506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282506 prefixEnd_5282506 := by exact prefixLift 5282506
  have htrace : WordTrace (prefixWord ++ tailWord_5282506) baseStart_5282506 baseEnd_5282506 := by
    simpa [prefixWord, tailWord_5282506, baseEnd_5282506] using wordTrace_append hprefix tailTrace_5282506
  have hstable : (prefixWord ++ tailWord_5282506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282506).length < 2 ^ (prefixWord ++ tailWord_5282506).sum := by decide
  have hdescent : baseEnd_5282506 < baseStart_5282506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282533 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5282533 : Nat := 118140960795 + 5282533 * 2 ^ 59
def prefixEnd_5282533 : Nat := 4983230072969 + 3 ^ 40 * 5282533 * 2
def baseEnd_5282533 : Nat := 2712478502237285799043579

theorem tailTrace_5282533 : CollatzResearch.WordTrace tailWord_5282533 prefixEnd_5282533 2712478502237285799043579 := by
  unfold tailWord_5282533
  simp only [CollatzResearch.WordTrace]
  refine ⟨192669806971292600654908253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128446537980861733769938835 192669806971292600654908253)
  ·
    refine ⟨72251177614234725245590595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192669806971292600654908253 72251177614234725245590595)
    ·
      refine ⟨108376766421352087868385893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72251177614234725245590595 108376766421352087868385893)
      ·
        refine ⟨20320643704003516475322355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108376766421352087868385893 20320643704003516475322355)
        ·
          refine ⟨30480965556005274712983533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20320643704003516475322355 30480965556005274712983533)
          ·
            refine ⟨11430362083501978017368825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30480965556005274712983533 11430362083501978017368825)
            ·
              refine ⟨8572771562626483513026619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11430362083501978017368825 8572771562626483513026619)
              ·
                refine ⟨12859157343939725269539929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572771562626483513026619 12859157343939725269539929)
                ·
                  refine ⟨9644368007954793952154947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12859157343939725269539929 9644368007954793952154947)
                  ·
                    refine ⟨14466552011932190928232421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9644368007954793952154947 14466552011932190928232421)
                    ·
                      refine ⟨2712478502237285799043579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14466552011932190928232421 2712478502237285799043579)
                      ·
                        rfl

theorem cell23_5282533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5282533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282533 prefixEnd_5282533 := by exact prefixLift 5282533
  have htrace : WordTrace (prefixWord ++ tailWord_5282533) baseStart_5282533 baseEnd_5282533 := by
    simpa [prefixWord, tailWord_5282533, baseEnd_5282533] using wordTrace_append hprefix tailTrace_5282533
  have hstable : (prefixWord ++ tailWord_5282533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282533).length < 2 ^ (prefixWord ++ tailWord_5282533).sum := by decide
  have hdescent : baseEnd_5282533 < baseStart_5282533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282556 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 6]
def baseStart_5282556 : Nat := 118140960795 + 5282556 * 2 ^ 59
def prefixEnd_5282556 : Nat := 4983230072969 + 3 ^ 40 * 5282556 * 2
def baseEnd_5282556 : Nat := 301387812476926578783997

theorem tailTrace_5282556 : CollatzResearch.WordTrace tailWord_5282556 prefixEnd_5282556 301387812476926578783997 := by
  unfold tailWord_5282556
  simp only [CollatzResearch.WordTrace]
  refine ⟨96335322925104637791497761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128447097233472850388663681 96335322925104637791497761)
  ·
    refine ⟨72251492193828478343623321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96335322925104637791497761 72251492193828478343623321)
    ·
      refine ⟨54188619145371358757717491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72251492193828478343623321 54188619145371358757717491)
      ·
        refine ⟨81282928718057038136576237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54188619145371358757717491 81282928718057038136576237)
        ·
          refine ⟨30481098269271389301216089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81282928718057038136576237 30481098269271389301216089)
          ·
            refine ⟨22860823701953541975912067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30481098269271389301216089 22860823701953541975912067)
            ·
              refine ⟨34291235552930312963868101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22860823701953541975912067 34291235552930312963868101)
              ·
                refine ⟨6429606666174433680725269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34291235552930312963868101 6429606666174433680725269)
                ·
                  refine ⟨301387812476926578783997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6429606666174433680725269 301387812476926578783997)
                  ·
                    rfl

theorem cell23_5282556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_5282556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282556 prefixEnd_5282556 := by exact prefixLift 5282556
  have htrace : WordTrace (prefixWord ++ tailWord_5282556) baseStart_5282556 baseEnd_5282556 := by
    simpa [prefixWord, tailWord_5282556, baseEnd_5282556] using wordTrace_append hprefix tailTrace_5282556
  have hstable : (prefixWord ++ tailWord_5282556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282556).length < 2 ^ (prefixWord ++ tailWord_5282556).sum := by decide
  have hdescent : baseEnd_5282556 < baseStart_5282556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282559 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 6]
def baseStart_5282559 : Nat := 118140960795 + 5282559 * 2 ^ 59
def prefixEnd_5282559 : Nat := 4983230072969 + 3 ^ 40 * 5282559 * 2
def baseEnd_5282559 : Nat := 2712491852734302697318459

theorem tailTrace_5282559 : CollatzResearch.WordTrace tailWord_5282559 prefixEnd_5282559 2712491852734302697318459 := by
  unfold tailWord_5282559
  simp only [CollatzResearch.WordTrace]
  refine ⟨192670755269198407095354731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128447170179465604730236487 192670755269198407095354731)
  ·
    refine ⟨289006132903797610643032097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192670755269198407095354731 289006132903797610643032097)
    ·
      refine ⟨216754599677848207982274073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289006132903797610643032097 216754599677848207982274073)
      ·
        refine ⟨162565949758386155986705555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216754599677848207982274073 162565949758386155986705555)
        ·
          refine ⟨243848924637579233980058333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162565949758386155986705555 243848924637579233980058333)
          ·
            refine ⟨91443346739092212742521875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243848924637579233980058333 91443346739092212742521875)
            ·
              refine ⟨137165020108638319113782813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91443346739092212742521875 137165020108638319113782813)
              ·
                refine ⟨51436882540739369667668555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137165020108638319113782813 51436882540739369667668555)
                ·
                  refine ⟨77155323811109054501502833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51436882540739369667668555 77155323811109054501502833)
                  ·
                    refine ⟨57866492858331790876127125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77155323811109054501502833 57866492858331790876127125)
                    ·
                      refine ⟨2712491852734302697318459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57866492858331790876127125 2712491852734302697318459)
                      ·
                        rfl

theorem cell23_5282559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_5282559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282559 prefixEnd_5282559 := by exact prefixLift 5282559
  have htrace : WordTrace (prefixWord ++ tailWord_5282559) baseStart_5282559 baseEnd_5282559 := by
    simpa [prefixWord, tailWord_5282559, baseEnd_5282559] using wordTrace_append hprefix tailTrace_5282559
  have hstable : (prefixWord ++ tailWord_5282559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282559).length < 2 ^ (prefixWord ++ tailWord_5282559).sum := by decide
  have hdescent : baseEnd_5282559 < baseStart_5282559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282579 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7]
def baseStart_5282579 : Nat := 118140960795 + 5282579 * 2 ^ 59
def prefixEnd_5282579 : Nat := 4983230072969 + 3 ^ 40 * 5282579 * 2
def baseEnd_5282579 : Nat := 2712502122347392619068367

theorem tailTrace_5282579 : CollatzResearch.WordTrace tailWord_5282579 prefixEnd_5282579 2712502122347392619068367 := by
  unfold tailWord_5282579
  simp only [CollatzResearch.WordTrace]
  refine ⟨192671484729125950511082791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128447656486083967007388527 192671484729125950511082791)
  ·
    refine ⟨289007227093688925766624187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192671484729125950511082791 289007227093688925766624187)
    ·
      refine ⟨433510840640533388649936281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289007227093688925766624187 433510840640533388649936281)
      ·
        refine ⟨325133130480400041487452211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433510840640533388649936281 325133130480400041487452211)
        ·
          refine ⟨487699695720600062231178317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325133130480400041487452211 487699695720600062231178317)
          ·
            refine ⟨182887385895225023336691869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487699695720600062231178317 182887385895225023336691869)
            ·
              refine ⟨68582769710709383751259451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182887385895225023336691869 68582769710709383751259451)
              ·
                refine ⟨102874154566064075626889177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68582769710709383751259451 102874154566064075626889177)
                ·
                  refine ⟨77155615924548056720166883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102874154566064075626889177 77155615924548056720166883)
                  ·
                    refine ⟨115733423886822085080250325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77155615924548056720166883 115733423886822085080250325)
                    ·
                      refine ⟨2712502122347392619068367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 115733423886822085080250325 2712502122347392619068367)
                      ·
                        rfl

theorem cell23_5282579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_5282579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282579 prefixEnd_5282579 := by exact prefixLift 5282579
  have htrace : WordTrace (prefixWord ++ tailWord_5282579) baseStart_5282579 baseEnd_5282579 := by
    simpa [prefixWord, tailWord_5282579, baseEnd_5282579] using wordTrace_append hprefix tailTrace_5282579
  have hstable : (prefixWord ++ tailWord_5282579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282579).length < 2 ^ (prefixWord ++ tailWord_5282579).sum := by decide
  have hdescent : baseEnd_5282579 < baseStart_5282579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282586 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 3, 5]
def baseStart_5282586 : Nat := 118140960795 + 5282586 * 2 ^ 59
def prefixEnd_5282586 : Nat := 4983230072969 + 3 ^ 40 * 5282586 * 2
def baseEnd_5282586 : Nat := 904168572237324697226945

theorem tailTrace_5282586 : CollatzResearch.WordTrace tailWord_5282586 prefixEnd_5282586 904168572237324697226945 := by
  unfold tailWord_5282586
  simp only [CollatzResearch.WordTrace]
  refine ⟨48167935010025147676646903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128447826693400393804391741 48167935010025147676646903)
  ·
    refine ⟨72251902515037721514970355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48167935010025147676646903 72251902515037721514970355)
    ·
      refine ⟨108377853772556582272455533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72251902515037721514970355 108377853772556582272455533)
      ·
        refine ⟨40641695164708718352170825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108377853772556582272455533 40641695164708718352170825)
        ·
          refine ⟨30481271373531538764128119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40641695164708718352170825 30481271373531538764128119)
          ·
            refine ⟨45721907060297308146192179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30481271373531538764128119 45721907060297308146192179)
            ·
              refine ⟨68582860590445962219288269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45721907060297308146192179 68582860590445962219288269)
              ·
                refine ⟨25718572721417235832233101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68582860590445962219288269 25718572721417235832233101)
                ·
                  refine ⟨9644464770531463437087413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25718572721417235832233101 9644464770531463437087413)
                  ·
                    refine ⟨904168572237324697226945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9644464770531463437087413 904168572237324697226945)
                    ·
                      rfl

theorem cell23_5282586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_5282586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282586 prefixEnd_5282586 := by exact prefixLift 5282586
  have htrace : WordTrace (prefixWord ++ tailWord_5282586) baseStart_5282586 baseEnd_5282586 := by
    simpa [prefixWord, tailWord_5282586, baseEnd_5282586] using wordTrace_append hprefix tailTrace_5282586
  have hstable : (prefixWord ++ tailWord_5282586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282586).length < 2 ^ (prefixWord ++ tailWord_5282586).sum := by decide
  have hdescent : baseEnd_5282586 < baseStart_5282586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282593 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_5282593 : Nat := 118140960795 + 5282593 * 2 ^ 59
def prefixEnd_5282593 : Nat := 4983230072969 + 3 ^ 40 * 5282593 * 2
def baseEnd_5282593 : Nat := 2712509311076555564293303

theorem tailTrace_5282593 : CollatzResearch.WordTrace tailWord_5282593 prefixEnd_5282593 2712509311076555564293303 := by
  unfold tailWord_5282593
  simp only [CollatzResearch.WordTrace]
  refine ⟨192671995351075230902092433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128447996900716820601394955 192671995351075230902092433)
  ·
    refine ⟨144503996513306423176569325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192671995351075230902092433 144503996513306423176569325)
    ·
      refine ⟨54188998692489908691213497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144503996513306423176569325 54188998692489908691213497)
      ·
        refine ⟨40641749019367431518410123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54188998692489908691213497 40641749019367431518410123)
        ·
          refine ⟨60962623529051147277615185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40641749019367431518410123 60962623529051147277615185)
          ·
            refine ⟨45721967646788360458211389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60962623529051147277615185 45721967646788360458211389)
            ·
              refine ⟨17145737867545635171829271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45721967646788360458211389 17145737867545635171829271)
              ·
                refine ⟨25718606801318452757743907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17145737867545635171829271 25718606801318452757743907)
                ·
                  refine ⟨38577910201977679136615861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25718606801318452757743907 38577910201977679136615861)
                  ·
                    refine ⟨3616679081435407419057737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38577910201977679136615861 3616679081435407419057737)
                    ·
                      refine ⟨2712509311076555564293303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616679081435407419057737 2712509311076555564293303)
                      ·
                        rfl

theorem cell23_5282593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_5282593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282593 prefixEnd_5282593 := by exact prefixLift 5282593
  have htrace : WordTrace (prefixWord ++ tailWord_5282593) baseStart_5282593 baseEnd_5282593 := by
    simpa [prefixWord, tailWord_5282593, baseEnd_5282593] using wordTrace_append hprefix tailTrace_5282593
  have hstable : (prefixWord ++ tailWord_5282593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282593).length < 2 ^ (prefixWord ++ tailWord_5282593).sum := by decide
  have hdescent : baseEnd_5282593 < baseStart_5282593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282633 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 1, 6]
def baseStart_5282633 : Nat := 118140960795 + 5282633 * 2 ^ 59
def prefixEnd_5282633 : Nat := 4983230072969 + 3 ^ 40 * 5282633 * 2
def baseEnd_5282633 : Nat := 904176616767578469264373

theorem tailTrace_5282633 : CollatzResearch.WordTrace tailWord_5282633 prefixEnd_5282633 904176616767578469264373 := by
  unfold tailWord_5282633
  simp only [CollatzResearch.WordTrace]
  refine ⟨192673454270930317733548553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128448969513953545155699035 192673454270930317733548553)
  ·
    refine ⟨144505090703197738300161415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192673454270930317733548553 144505090703197738300161415)
    ·
      refine ⟨216757636054796607450242123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144505090703197738300161415 216757636054796607450242123)
      ·
        refine ⟨325136454082194911175363185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216757636054796607450242123 325136454082194911175363185)
        ·
          refine ⟨243852340561646183381522389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325136454082194911175363185 243852340561646183381522389)
          ·
            refine ⟨5715289231913582423004431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 243852340561646183381522389 5715289231913582423004431)
            ·
              refine ⟨8572933847870373634506647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715289231913582423004431 8572933847870373634506647)
              ·
                refine ⟨12859400771805560451759971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8572933847870373634506647 12859400771805560451759971)
                ·
                  refine ⟨19289101157708340677639957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12859400771805560451759971 19289101157708340677639957)
                  ·
                    refine ⟨904176616767578469264373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19289101157708340677639957 904176616767578469264373)
                    ·
                      rfl

theorem cell23_5282633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_5282633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282633 prefixEnd_5282633 := by exact prefixLift 5282633
  have htrace : WordTrace (prefixWord ++ tailWord_5282633) baseStart_5282633 baseEnd_5282633 := by
    simpa [prefixWord, tailWord_5282633, baseEnd_5282633] using wordTrace_append hprefix tailTrace_5282633
  have hstable : (prefixWord ++ tailWord_5282633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282633).length < 2 ^ (prefixWord ++ tailWord_5282633).sum := by decide
  have hdescent : baseEnd_5282633 < baseStart_5282633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282637 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5282637 : Nat := 118140960795 + 5282637 * 2 ^ 59
def prefixEnd_5282637 : Nat := 4983230072969 + 3 ^ 40 * 5282637 * 2
def baseEnd_5282637 : Nat := 904177301408451130714367

theorem tailTrace_5282637 : CollatzResearch.WordTrace tailWord_5282637 prefixEnd_5282637 904177301408451130714367 := by
  unfold tailWord_5282637
  simp only [CollatzResearch.WordTrace]
  refine ⟨192673600162915826416694165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128449066775277217611129443 192673600162915826416694165)
  ·
    refine ⟨9031575007636679363282539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 192673600162915826416694165 9031575007636679363282539)
    ·
      refine ⟨13547362511455019044923809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9031575007636679363282539 13547362511455019044923809)
      ·
        refine ⟨10160521883591264283692857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13547362511455019044923809 10160521883591264283692857)
        ·
          refine ⟨7620391412693448212769643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10160521883591264283692857 7620391412693448212769643)
          ·
            refine ⟨11430587119040172319154465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620391412693448212769643 11430587119040172319154465)
            ·
              refine ⟨8572940339280129239365849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11430587119040172319154465 8572940339280129239365849)
              ·
                refine ⟨6429705254460096929524387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8572940339280129239365849 6429705254460096929524387)
                ·
                  refine ⟨9644557881690145394286581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429705254460096929524387 9644557881690145394286581)
                  ·
                    refine ⟨904177301408451130714367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9644557881690145394286581 904177301408451130714367)
                    ·
                      rfl

theorem cell23_5282637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5282637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282637 prefixEnd_5282637 := by exact prefixLift 5282637
  have htrace : WordTrace (prefixWord ++ tailWord_5282637) baseStart_5282637 baseEnd_5282637 := by
    simpa [prefixWord, tailWord_5282637, baseEnd_5282637] using wordTrace_append hprefix tailTrace_5282637
  have hstable : (prefixWord ++ tailWord_5282637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282637).length < 2 ^ (prefixWord ++ tailWord_5282637).sum := by decide
  have hdescent : baseEnd_5282637 < baseStart_5282637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282640 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 3, 2, 2]
def baseStart_5282640 : Nat := 118140960795 + 5282640 * 2 ^ 59
def prefixEnd_5282640 : Nat := 4983230072969 + 3 ^ 40 * 5282640 * 2
def baseEnd_5282640 : Nat := 2712533444667316880405587

theorem tailTrace_5282640 : CollatzResearch.WordTrace tailWord_5282640 prefixEnd_5282640 2712533444667316880405587 := by
  unfold tailWord_5282640
  simp only [CollatzResearch.WordTrace]
  refine ⟨96336854790952478964526687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128449139721269971952702249 96336854790952478964526687)
  ·
    refine ⟨144505282186428718446790031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96336854790952478964526687 144505282186428718446790031)
    ·
      refine ⟨216757923279643077670185047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144505282186428718446790031 216757923279643077670185047)
      ·
        refine ⟨325136884919464616505277571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216757923279643077670185047 325136884919464616505277571)
        ·
          refine ⟨487705327379196924757916357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325136884919464616505277571 487705327379196924757916357)
          ·
            refine ⟨91444748883599423392109317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 487705327379196924757916357 91444748883599423392109317)
            ·
              refine ⟨17145890415674891886020497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91444748883599423392109317 17145890415674891886020497)
              ·
                refine ⟨12859417811756168914515373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17145890415674891886020497 12859417811756168914515373)
                ·
                  refine ⟨4822281679408563342943265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12859417811756168914515373 4822281679408563342943265)
                  ·
                    refine ⟨3616711259556422507207449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4822281679408563342943265 3616711259556422507207449)
                    ·
                      refine ⟨2712533444667316880405587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616711259556422507207449 2712533444667316880405587)
                      ·
                        rfl

theorem cell23_5282640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 2, 2].length) (baseStart_5282640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282640 prefixEnd_5282640 := by exact prefixLift 5282640
  have htrace : WordTrace (prefixWord ++ tailWord_5282640) baseStart_5282640 baseEnd_5282640 := by
    simpa [prefixWord, tailWord_5282640, baseEnd_5282640] using wordTrace_append hprefix tailTrace_5282640
  have hstable : (prefixWord ++ tailWord_5282640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282640).length < 2 ^ (prefixWord ++ tailWord_5282640).sum := by decide
  have hdescent : baseEnd_5282640 < baseStart_5282640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282657 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_5282657 : Nat := 118140960795 + 5282657 * 2 ^ 59
def prefixEnd_5282657 : Nat := 4983230072969 + 3 ^ 40 * 5282657 * 2
def baseEnd_5282657 : Nat := 2712542173838443313893009

theorem tailTrace_5282657 : CollatzResearch.WordTrace tailWord_5282657 prefixEnd_5282657 2712542173838443313893009 := by
  unfold tailWord_5282657
  simp only [CollatzResearch.WordTrace]
  refine ⟨192674329622843369832422225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128449553081895579888281483 192674329622843369832422225)
  ·
    refine ⟨144505747217132527374316669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192674329622843369832422225 144505747217132527374316669)
    ·
      refine ⟨54189655206424697765368751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144505747217132527374316669 54189655206424697765368751)
      ·
        refine ⟨81284482809637046648053127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54189655206424697765368751 81284482809637046648053127)
        ·
          refine ⟨121926724214455569972079691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81284482809637046648053127 121926724214455569972079691)
          ·
            refine ⟨182890086321683354958119537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121926724214455569972079691 182890086321683354958119537)
            ·
              refine ⟨137167564741262516218589653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182890086321683354958119537 137167564741262516218589653)
              ·
                refine ⟨3214864798623340223873195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137167564741262516218589653 3214864798623340223873195)
                ·
                  refine ⟨4822297197935010335809793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3214864798623340223873195 4822297197935010335809793)
                  ·
                    refine ⟨3616722898451257751857345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4822297197935010335809793 3616722898451257751857345)
                    ·
                      refine ⟨2712542173838443313893009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616722898451257751857345 2712542173838443313893009)
                      ·
                        rfl

theorem cell23_5282657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_5282657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282657 prefixEnd_5282657 := by exact prefixLift 5282657
  have htrace : WordTrace (prefixWord ++ tailWord_5282657) baseStart_5282657 baseEnd_5282657 := by
    simpa [prefixWord, tailWord_5282657, baseEnd_5282657] using wordTrace_append hprefix tailTrace_5282657
  have hstable : (prefixWord ++ tailWord_5282657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282657).length < 2 ^ (prefixWord ++ tailWord_5282657).sum := by decide
  have hdescent : baseEnd_5282657 < baseStart_5282657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282660 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_5282660 : Nat := 118140960795 + 5282660 * 2 ^ 59
def prefixEnd_5282660 : Nat := 4983230072969 + 3 ^ 40 * 5282660 * 2
def baseEnd_5282660 : Nat := 2712543714280406802155495

theorem tailTrace_5282660 : CollatzResearch.WordTrace tailWord_5282660 prefixEnd_5282660 2712543714280406802155495 := by
  unfold tailWord_5282660
  simp only [CollatzResearch.WordTrace]
  refine ⟨96337219520916250672390717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128449626027888334229854289 96337219520916250672390717)
  ·
    refine ⟨36126457320343594002146519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96337219520916250672390717 36126457320343594002146519)
    ·
      refine ⟨54189685980515391003219779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36126457320343594002146519 54189685980515391003219779)
      ·
        refine ⟨81284528970773086504829669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54189685980515391003219779 81284528970773086504829669)
        ·
          refine ⟨15240849182019953719655563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81284528970773086504829669 15240849182019953719655563)
          ·
            refine ⟨22861273773029930579483345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15240849182019953719655563 22861273773029930579483345)
            ·
              refine ⟨17145955329772447934612509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22861273773029930579483345 17145955329772447934612509)
              ·
                refine ⟨6429733248664667975479691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17145955329772447934612509 6429733248664667975479691)
                ·
                  refine ⟨9644599872997001963219537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6429733248664667975479691 9644599872997001963219537)
                  ·
                    refine ⟨7233449904747751472414653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9644599872997001963219537 7233449904747751472414653)
                    ·
                      refine ⟨2712543714280406802155495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7233449904747751472414653 2712543714280406802155495)
                      ·
                        rfl

theorem cell23_5282660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_5282660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282660 prefixEnd_5282660 := by exact prefixLift 5282660
  have htrace : WordTrace (prefixWord ++ tailWord_5282660) baseStart_5282660 baseEnd_5282660 := by
    simpa [prefixWord, tailWord_5282660, baseEnd_5282660] using wordTrace_append hprefix tailTrace_5282660
  have hstable : (prefixWord ++ tailWord_5282660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282660).length < 2 ^ (prefixWord ++ tailWord_5282660).sum := by decide
  have hdescent : baseEnd_5282660 < baseStart_5282660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282740 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_5282740 : Nat := 118140960795 + 5282740 * 2 ^ 59
def prefixEnd_5282740 : Nat := 4983230072969 + 3 ^ 40 * 5282740 * 2
def baseEnd_5282740 : Nat := 904194930910922163051709

theorem tailTrace_5282740 : CollatzResearch.WordTrace tailWord_5282740 prefixEnd_5282740 904194930910922163051709 := by
  unfold tailWord_5282740
  simp only [CollatzResearch.WordTrace]
  refine ⟨96338678440771337503846837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128451571254361783338462449 96338678440771337503846837)
  ·
    refine ⟨9031751103822312890985641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96338678440771337503846837 9031751103822312890985641)
    ·
      refine ⟨6773813327866734668239231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9031751103822312890985641 6773813327866734668239231)
      ·
        refine ⟨10160719991800102002358847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6773813327866734668239231 10160719991800102002358847)
        ·
          refine ⟨15241079987700153003538271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10160719991800102002358847 15241079987700153003538271)
          ·
            refine ⟨22861619981550229505307407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15241079987700153003538271 22861619981550229505307407)
            ·
              refine ⟨34292429972325344257961111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22861619981550229505307407 34292429972325344257961111)
              ·
                refine ⟨51438644958488016386941667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34292429972325344257961111 51438644958488016386941667)
                ·
                  refine ⟨77157967437732024580412501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51438644958488016386941667 77157967437732024580412501)
                  ·
                    refine ⟨904194930910922163051709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77157967437732024580412501 904194930910922163051709)
                    ·
                      rfl

theorem cell23_5282740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_5282740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282740 prefixEnd_5282740 := by exact prefixLift 5282740
  have htrace : WordTrace (prefixWord ++ tailWord_5282740) baseStart_5282740 baseEnd_5282740 := by
    simpa [prefixWord, tailWord_5282740, baseEnd_5282740] using wordTrace_append hprefix tailTrace_5282740
  have hstable : (prefixWord ++ tailWord_5282740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282740).length < 2 ^ (prefixWord ++ tailWord_5282740).sum := by decide
  have hdescent : baseEnd_5282740 < baseStart_5282740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282781 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_5282781 : Nat := 118140960795 + 5282781 * 2 ^ 59
def prefixEnd_5282781 : Nat := 4983230072969 + 3 ^ 40 * 5282781 * 2
def baseEnd_5282781 : Nat := 2712605845439600828742439

theorem tailTrace_5282781 : CollatzResearch.WordTrace tailWord_5282781 prefixEnd_5282781 2712605845439600828742439 := by
  unfold tailWord_5282781
  simp only [CollatzResearch.WordTrace]
  refine ⟨192678852274394139009936197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128452568182929426006624131 192678852274394139009936197)
  ·
    refine ⟨36127284801448901064363037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192678852274394139009936197 36127284801448901064363037)
    ·
      refine ⟨13547731800543337899136139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36127284801448901064363037 13547731800543337899136139)
      ·
        refine ⟨20321597700815006848704209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13547731800543337899136139 20321597700815006848704209)
        ·
          refine ⟨15241198275611255136528157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20321597700815006848704209 15241198275611255136528157)
          ·
            refine ⟨5715449353354220676198059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15241198275611255136528157 5715449353354220676198059)
            ·
              refine ⟨8573174030031331014297089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715449353354220676198059 8573174030031331014297089)
              ·
                refine ⟨6429880522523498260722817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8573174030031331014297089 6429880522523498260722817)
                ·
                  refine ⟨4822410391892623695542113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6429880522523498260722817 4822410391892623695542113)
                  ·
                    refine ⟨3616807793919467771656585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4822410391892623695542113 3616807793919467771656585)
                    ·
                      refine ⟨2712605845439600828742439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616807793919467771656585 2712605845439600828742439)
                      ·
                        rfl

theorem cell23_5282781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_5282781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282781 prefixEnd_5282781 := by exact prefixLift 5282781
  have htrace : WordTrace (prefixWord ++ tailWord_5282781) baseStart_5282781 baseEnd_5282781 := by
    simpa [prefixWord, tailWord_5282781, baseEnd_5282781] using wordTrace_append hprefix tailTrace_5282781
  have hstable : (prefixWord ++ tailWord_5282781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282781).length < 2 ^ (prefixWord ++ tailWord_5282781).sum := by decide
  have hdescent : baseEnd_5282781 < baseStart_5282781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282840 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_5282840 : Nat := 118140960795 + 5282840 * 2 ^ 59
def prefixEnd_5282840 : Nat := 4983230072969 + 3 ^ 40 * 5282840 * 2
def baseEnd_5282840 : Nat := 2712636140798216097904667

theorem tailTrace_5282840 : CollatzResearch.WordTrace tailWord_5282840 prefixEnd_5282840 2712636140798216097904667 := by
  unfold tailWord_5282840
  simp only [CollatzResearch.WordTrace]
  refine ⟨96340502090590196043166987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128454002787453594724222649 96340502090590196043166987)
  ·
    refine ⟨144510753135885294064750481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96340502090590196043166987 144510753135885294064750481)
    ·
      refine ⟨108383064851913970548562861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144510753135885294064750481 108383064851913970548562861)
      ·
        refine ⟨40643649319467738955711073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108383064851913970548562861 40643649319467738955711073)
        ·
          refine ⟨30482736989600804216783305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40643649319467738955711073 30482736989600804216783305)
          ·
            refine ⟨22862052742200603162587479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30482736989600804216783305 22862052742200603162587479)
            ·
              refine ⟨34293079113300904743881219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22862052742200603162587479 34293079113300904743881219)
              ·
                refine ⟨51439618669951357115821829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34293079113300904743881219 51439618669951357115821829)
                ·
                  refine ⟨9644928500615879459216593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51439618669951357115821829 9644928500615879459216593)
                  ·
                    refine ⟨7233696375461909594412445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9644928500615879459216593 7233696375461909594412445)
                    ·
                      refine ⟨2712636140798216097904667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7233696375461909594412445 2712636140798216097904667)
                      ·
                        rfl

theorem cell23_5282840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_5282840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282840 prefixEnd_5282840 := by exact prefixLift 5282840
  have htrace : WordTrace (prefixWord ++ tailWord_5282840) baseStart_5282840 baseEnd_5282840 := by
    simpa [prefixWord, tailWord_5282840, baseEnd_5282840] using wordTrace_append hprefix tailTrace_5282840
  have hstable : (prefixWord ++ tailWord_5282840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282840).length < 2 ^ (prefixWord ++ tailWord_5282840).sum := by decide
  have hdescent : baseEnd_5282840 < baseStart_5282840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282847 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 3, 4]
def baseStart_5282847 : Nat := 118140960795 + 5282847 * 2 ^ 59
def prefixEnd_5282847 : Nat := 4983230072969 + 3 ^ 40 * 5282847 * 2
def baseEnd_5282847 : Nat := 904213245054265856839045

theorem tailTrace_5282847 : CollatzResearch.WordTrace tailWord_5282847 prefixEnd_5282847 904213245054265856839045 := by
  unfold tailWord_5282847
  simp only [CollatzResearch.WordTrace]
  refine ⟨192681259492155032281838795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128454172994770021521225863 192681259492155032281838795)
  ·
    refine ⟨289021889238232548422758193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192681259492155032281838795 289021889238232548422758193)
    ·
      refine ⟨216766416928674411317068645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289021889238232548422758193 216766416928674411317068645)
      ·
        refine ⟨40643703174126452121950371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216766416928674411317068645 40643703174126452121950371)
        ·
          refine ⟨60965554761189678182925557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40643703174126452121950371 60965554761189678182925557)
          ·
            refine ⟨5715520758861532329649271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60965554761189678182925557 5715520758861532329649271)
            ·
              refine ⟨8573281138292298494473907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715520758861532329649271 8573281138292298494473907)
              ·
                refine ⟨12859921707438447741710861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8573281138292298494473907 12859921707438447741710861)
                ·
                  refine ⟨4822470640289417903141573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12859921707438447741710861 4822470640289417903141573)
                  ·
                    refine ⟨904213245054265856839045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822470640289417903141573 904213245054265856839045)
                    ·
                      rfl

theorem cell23_5282847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 4].length) (baseStart_5282847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282847 prefixEnd_5282847 := by exact prefixLift 5282847
  have htrace : WordTrace (prefixWord ++ tailWord_5282847) baseStart_5282847 baseEnd_5282847 := by
    simpa [prefixWord, tailWord_5282847, baseEnd_5282847] using wordTrace_append hprefix tailTrace_5282847
  have hstable : (prefixWord ++ tailWord_5282847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282847).length < 2 ^ (prefixWord ++ tailWord_5282847).sum := by decide
  have hdescent : baseEnd_5282847 < baseStart_5282847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282890 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 1, 5]
def baseStart_5282890 : Nat := 118140960795 + 5282890 * 2 ^ 59
def prefixEnd_5282890 : Nat := 4983230072969 + 3 ^ 40 * 5282890 * 2
def baseEnd_5282890 : Nat := 904220604943646967426479

theorem tailTrace_5282890 : CollatzResearch.WordTrace tailWord_5282890 prefixEnd_5282890 904220604943646967426479 := by
  unfold tailWord_5282890
  simp only [CollatzResearch.WordTrace]
  refine ⟨48170706957749812656413531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128455218553999500417102749 48170706957749812656413531)
  ·
    refine ⟨72256060436624718984620297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48170706957749812656413531 72256060436624718984620297)
    ·
      refine ⟨54192045327468539238465223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72256060436624718984620297 54192045327468539238465223)
      ·
        refine ⟨81288067991202808857697835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54192045327468539238465223 81288067991202808857697835)
        ·
          refine ⟨121932101986804213286546753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81288067991202808857697835 121932101986804213286546753)
          ·
            refine ⟨91449076490103159964910065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121932101986804213286546753 91449076490103159964910065)
            ·
              refine ⟨68586807367577369973682549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91449076490103159964910065 68586807367577369973682549)
              ·
                refine ⟨6430013190710378435032739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68586807367577369973682549 6430013190710378435032739)
                ·
                  refine ⟨9645019786065567652549109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6430013190710378435032739 9645019786065567652549109)
                  ·
                    refine ⟨904220604943646967426479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9645019786065567652549109 904220604943646967426479)
                    ·
                      rfl

theorem cell23_5282890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_5282890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282890 prefixEnd_5282890 := by exact prefixLift 5282890
  have htrace : WordTrace (prefixWord ++ tailWord_5282890) baseStart_5282890 baseEnd_5282890 := by
    simpa [prefixWord, tailWord_5282890, baseEnd_5282890] using wordTrace_append hprefix tailTrace_5282890
  have hstable : (prefixWord ++ tailWord_5282890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282890).length < 2 ^ (prefixWord ++ tailWord_5282890).sum := by decide
  have hdescent : baseEnd_5282890 < baseStart_5282890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282897 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 2, 3, 2]
def baseStart_5282897 : Nat := 118140960795 + 5282897 * 2 ^ 59
def prefixEnd_5282897 : Nat := 4983230072969 + 3 ^ 40 * 5282897 * 2
def baseEnd_5282897 : Nat := 2712665409195522374891905

theorem tailTrace_5282897 : CollatzResearch.WordTrace tailWord_5282897 prefixEnd_5282897 2712665409195522374891905 := by
  unfold tailWord_5282897
  simp only [CollatzResearch.WordTrace]
  refine ⟨192683083141973890821158945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128455388761315927214105963 192683083141973890821158945)
  ·
    refine ⟨144512312356480418115869209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192683083141973890821158945 144512312356480418115869209)
    ·
      refine ⟨108384234267360313586901907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144512312356480418115869209 108384234267360313586901907)
      ·
        refine ⟨162576351401040470380352861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108384234267360313586901907 162576351401040470380352861)
        ·
          refine ⟨60966131775390176392632323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162576351401040470380352861 60966131775390176392632323)
          ·
            refine ⟨91449197663085264588948485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60966131775390176392632323 91449197663085264588948485)
            ·
              refine ⟨17146724561828487110427841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91449197663085264588948485 17146724561828487110427841)
              ·
                refine ⟨12860043421371365332820881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17146724561828487110427841 12860043421371365332820881)
                ·
                  refine ⟨9645032566028523999615661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12860043421371365332820881 9645032566028523999615661)
                  ·
                    refine ⟨3616887212260696499855873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9645032566028523999615661 3616887212260696499855873)
                    ·
                      refine ⟨2712665409195522374891905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3616887212260696499855873 2712665409195522374891905)
                      ·
                        rfl

theorem cell23_5282897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_5282897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282897 prefixEnd_5282897 := by exact prefixLift 5282897
  have htrace : WordTrace (prefixWord ++ tailWord_5282897) baseStart_5282897 baseEnd_5282897 := by
    simpa [prefixWord, tailWord_5282897, baseEnd_5282897] using wordTrace_append hprefix tailTrace_5282897
  have hstable : (prefixWord ++ tailWord_5282897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282897).length < 2 ^ (prefixWord ++ tailWord_5282897).sum := by decide
  have hdescent : baseEnd_5282897 < baseStart_5282897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282903 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 5, 6]
def baseStart_5282903 : Nat := 118140960795 + 5282903 * 2 ^ 59
def prefixEnd_5282903 : Nat := 4983230072969 + 3 ^ 40 * 5282903 * 2
def baseEnd_5282903 : Nat := 904222830026483117138959

theorem tailTrace_5282903 : CollatzResearch.WordTrace tailWord_5282903 prefixEnd_5282903 904222830026483117138959 := by
  unfold tailWord_5282903
  simp only [CollatzResearch.WordTrace]
  refine ⟨192683301979952153845877363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128455534653301435897251575 192683301979952153845877363)
  ·
    refine ⟨289024952969928230768816045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192683301979952153845877363 289024952969928230768816045)
    ·
      refine ⟨108384357363723086538306017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289024952969928230768816045 108384357363723086538306017)
      ·
        refine ⟨81288268022792314903729513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108384357363723086538306017 81288268022792314903729513)
        ·
          refine ⟨60966201017094236177797135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81288268022792314903729513 60966201017094236177797135)
          ·
            refine ⟨91449301525641354266695703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60966201017094236177797135 91449301525641354266695703)
            ·
              refine ⟨137173952288462031400043555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91449301525641354266695703 137173952288462031400043555)
              ·
                refine ⟨205760928432693047100065333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137173952288462031400043555 205760928432693047100065333)
                ·
                  refine ⟨19290087040564973165631125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205760928432693047100065333 19290087040564973165631125)
                  ·
                    refine ⟨904222830026483117138959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19290087040564973165631125 904222830026483117138959)
                    ·
                      rfl

theorem cell23_5282903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_5282903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282903 prefixEnd_5282903 := by exact prefixLift 5282903
  have htrace : WordTrace (prefixWord ++ tailWord_5282903) baseStart_5282903 baseEnd_5282903 := by
    simpa [prefixWord, tailWord_5282903, baseEnd_5282903] using wordTrace_append hprefix tailTrace_5282903
  have hstable : (prefixWord ++ tailWord_5282903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282903).length < 2 ^ (prefixWord ++ tailWord_5282903).sum := by decide
  have hdescent : baseEnd_5282903 < baseStart_5282903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282904 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 1, 1, 3]
def baseStart_5282904 : Nat := 118140960795 + 5282904 * 2 ^ 59
def prefixEnd_5282904 : Nat := 4983230072969 + 3 ^ 40 * 5282904 * 2
def baseEnd_5282904 : Nat := 2712669003560103847504373

theorem tailTrace_5282904 : CollatzResearch.WordTrace tailWord_5282904 prefixEnd_5282904 2712669003560103847504373 := by
  unfold tailWord_5282904
  simp only [CollatzResearch.WordTrace]
  refine ⟨96341669226474265508331883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128455558968632354011109177 96341669226474265508331883)
  ·
    refine ⟨144512503839711398262497825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96341669226474265508331883 144512503839711398262497825)
    ·
      refine ⟨108384377879783548696873369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144512503839711398262497825 108384377879783548696873369)
      ·
        refine ⟨81288283409837661522655027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108384377879783548696873369 81288283409837661522655027)
        ·
          refine ⟨121932425114756492283982541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81288283409837661522655027 121932425114756492283982541)
          ·
            refine ⟨45724659418033684606493453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121932425114756492283982541 45724659418033684606493453)
            ·
              refine ⟨17146747281762631727435045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45724659418033684606493453 17146747281762631727435045)
              ·
                refine ⟨3215015115330493448894071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17146747281762631727435045 3215015115330493448894071)
                ·
                  refine ⟨4822522672995740173341107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215015115330493448894071 4822522672995740173341107)
                  ·
                    refine ⟨7233784009493610260011661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4822522672995740173341107 7233784009493610260011661)
                    ·
                      refine ⟨2712669003560103847504373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7233784009493610260011661 2712669003560103847504373)
                      ·
                        rfl

theorem cell23_5282904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_5282904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282904 prefixEnd_5282904 := by exact prefixLift 5282904
  have htrace : WordTrace (prefixWord ++ tailWord_5282904) baseStart_5282904 baseEnd_5282904 := by
    simpa [prefixWord, tailWord_5282904, baseEnd_5282904] using wordTrace_append hprefix tailTrace_5282904
  have hstable : (prefixWord ++ tailWord_5282904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282904).length < 2 ^ (prefixWord ++ tailWord_5282904).sum := by decide
  have hdescent : baseEnd_5282904 < baseStart_5282904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282940 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_5282940 : Nat := 118140960795 + 5282940 * 2 ^ 59
def prefixEnd_5282940 : Nat := 4983230072969 + 3 ^ 40 * 5282940 * 2
def baseEnd_5282940 : Nat := 2712687488863665706654207

theorem tailTrace_5282940 : CollatzResearch.WordTrace tailWord_5282940 prefixEnd_5282940 2712687488863665706654207 := by
  unfold tailWord_5282940
  simp only [CollatzResearch.WordTrace]
  refine ⟨96342325740409054582487137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128456434320545406109982849 96342325740409054582487137)
  ·
    refine ⟨72256744305306790936865353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96342325740409054582487137 72256744305306790936865353)
    ·
      refine ⟨54192558228980093202649015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72256744305306790936865353 54192558228980093202649015)
      ·
        refine ⟨81288837343470139803973523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54192558228980093202649015 81288837343470139803973523)
        ·
          refine ⟨121933256015205209705960285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81288837343470139803973523 121933256015205209705960285)
          ·
            refine ⟨45724971005701953639735107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121933256015205209705960285 45724971005701953639735107)
            ·
              refine ⟨68587456508552930459602661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45724971005701953639735107 68587456508552930459602661)
              ·
                refine ⟨12860148095353674461175499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68587456508552930459602661 12860148095353674461175499)
                ·
                  refine ⟨19290222143030511691763249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12860148095353674461175499 19290222143030511691763249)
                  ·
                    refine ⟨14467666607272883768822437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19290222143030511691763249 14467666607272883768822437)
                    ·
                      refine ⟨2712687488863665706654207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14467666607272883768822437 2712687488863665706654207)
                      ·
                        rfl

theorem cell23_5282940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_5282940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282940 prefixEnd_5282940 := by exact prefixLift 5282940
  have htrace : WordTrace (prefixWord ++ tailWord_5282940) baseStart_5282940 baseEnd_5282940 := by
    simpa [prefixWord, tailWord_5282940, baseEnd_5282940] using wordTrace_append hprefix tailTrace_5282940
  have hstable : (prefixWord ++ tailWord_5282940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282940).length < 2 ^ (prefixWord ++ tailWord_5282940).sum := by decide
  have hdescent : baseEnd_5282940 < baseStart_5282940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282947 : List Nat := [1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 3]
def baseStart_5282947 : Nat := 118140960795 + 5282947 * 2 ^ 59
def prefixEnd_5282947 : Nat := 4983230072969 + 3 ^ 40 * 5282947 * 2
def baseEnd_5282947 : Nat := 2712691083228247179266675

theorem tailTrace_5282947 : CollatzResearch.WordTrace tailWord_5282947 prefixEnd_5282947 2712691083228247179266675 := by
  unfold tailWord_5282947
  simp only [CollatzResearch.WordTrace]
  refine ⟨192684906791792749360479095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128456604527861832906986063 192684906791792749360479095)
  ·
    refine ⟨289027360187689124040718643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192684906791792749360479095 289027360187689124040718643)
    ·
      refine ⟨433541040281533686061077965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289027360187689124040718643 433541040281533686061077965)
      ·
        refine ⟨162577890105575132272904237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433541040281533686061077965 162577890105575132272904237)
        ·
          refine ⟨60966708789590674602339089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162577890105575132272904237 60966708789590674602339089)
          ·
            refine ⟨45725031592193005951754317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60966708789590674602339089 45725031592193005951754317)
            ·
              refine ⟨17146886847072377231907869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45725031592193005951754317 17146886847072377231907869)
              ·
                refine ⟨6430082567652141461965451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17146886847072377231907869 6430082567652141461965451)
                ·
                  refine ⟨9645123851478212192948177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6430082567652141461965451 9645123851478212192948177)
                  ·
                    refine ⟨7233842888608659144711133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9645123851478212192948177 7233842888608659144711133)
                    ·
                      refine ⟨2712691083228247179266675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7233842888608659144711133 2712691083228247179266675)
                      ·
                        rfl

theorem cell23_5282947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_5282947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282947 prefixEnd_5282947 := by exact prefixLift 5282947
  have htrace : WordTrace (prefixWord ++ tailWord_5282947) baseStart_5282947 baseEnd_5282947 := by
    simpa [prefixWord, tailWord_5282947, baseEnd_5282947] using wordTrace_append hprefix tailTrace_5282947
  have hstable : (prefixWord ++ tailWord_5282947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282947).length < 2 ^ (prefixWord ++ tailWord_5282947).sum := by decide
  have hdescent : baseEnd_5282947 < baseStart_5282947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282963 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 1, 9]
def baseStart_5282963 : Nat := 118140960795 + 5282963 * 2 ^ 59
def prefixEnd_5282963 : Nat := 4983230072969 + 3 ^ 40 * 5282963 * 2
def baseEnd_5282963 : Nat := 904233099639573038888867

theorem tailTrace_5282963 : CollatzResearch.WordTrace tailWord_5282963 prefixEnd_5282963 904233099639573038888867 := by
  unfold tailWord_5282963
  simp only [CollatzResearch.WordTrace]
  refine ⟨192685490359734784093061543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128456993573156522728707695 192685490359734784093061543)
  ·
    refine ⟨289028235539602176139592315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192685490359734784093061543 289028235539602176139592315)
    ·
      refine ⟨433542353309403264209388473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289028235539602176139592315 433542353309403264209388473)
      ·
        refine ⟨325156764982052448157041355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 433542353309403264209388473 325156764982052448157041355)
        ·
          refine ⟨487735147473078672235562033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325156764982052448157041355 487735147473078672235562033)
          ·
            refine ⟨365801360604809004176671525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487735147473078672235562033 365801360604809004176671525)
            ·
              refine ⟨68587755113401688283125911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 365801360604809004176671525 68587755113401688283125911)
              ·
                refine ⟨102881632670102532424688867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68587755113401688283125911 102881632670102532424688867)
                ·
                  refine ⟨154322449005153798637033301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102881632670102532424688867 154322449005153798637033301)
                  ·
                    refine ⟨904233099639573038888867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 154322449005153798637033301 904233099639573038888867)
                    ·
                      rfl

theorem cell23_5282963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 9].length) (baseStart_5282963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282963 prefixEnd_5282963 := by exact prefixLift 5282963
  have htrace : WordTrace (prefixWord ++ tailWord_5282963) baseStart_5282963 baseEnd_5282963 := by
    simpa [prefixWord, tailWord_5282963, baseEnd_5282963] using wordTrace_append hprefix tailTrace_5282963
  have hstable : (prefixWord ++ tailWord_5282963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282963).length < 2 ^ (prefixWord ++ tailWord_5282963).sum := by decide
  have hdescent : baseEnd_5282963 < baseStart_5282963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5282974 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_5282974 : Nat := 118140960795 + 5282974 * 2 ^ 59
def prefixEnd_5282974 : Nat := 4983230072969 + 3 ^ 40 * 5282974 * 2
def baseEnd_5282974 : Nat := 2712704947205918573629051

theorem tailTrace_5282974 : CollatzResearch.WordTrace tailWord_5282974 prefixEnd_5282974 2712704947205918573629051 := by
  unfold tailWord_5282974
  simp only [CollatzResearch.WordTrace]
  refine ⟨24085736445336866621463997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128457261041796621981141317 24085736445336866621463997)
  ·
    refine ⟨9032151167001324983048999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24085736445336866621463997 9032151167001324983048999)
    ·
      refine ⟨13548226750501987474573499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9032151167001324983048999 13548226750501987474573499)
      ·
        refine ⟨20322340125752981211860249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13548226750501987474573499 20322340125752981211860249)
        ·
          refine ⟨15241755094314735908895187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20322340125752981211860249 15241755094314735908895187)
          ·
            refine ⟨22862632641472103863342781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15241755094314735908895187 22862632641472103863342781)
            ·
              refine ⟨8573487240552038948753543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22862632641472103863342781 8573487240552038948753543)
              ·
                refine ⟨12860230860828058423130315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8573487240552038948753543 12860230860828058423130315)
                ·
                  refine ⟨19290346291242087634695473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12860230860828058423130315 19290346291242087634695473)
                  ·
                    refine ⟨14467759718431565726021605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19290346291242087634695473 14467759718431565726021605)
                    ·
                      refine ⟨2712704947205918573629051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14467759718431565726021605 2712704947205918573629051)
                      ·
                        rfl

theorem cell23_5282974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_5282974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5282974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5282974 prefixEnd_5282974 := by exact prefixLift 5282974
  have htrace : WordTrace (prefixWord ++ tailWord_5282974) baseStart_5282974 baseEnd_5282974 := by
    simpa [prefixWord, tailWord_5282974, baseEnd_5282974] using wordTrace_append hprefix tailTrace_5282974
  have hstable : (prefixWord ++ tailWord_5282974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5282974).length < 2 ^ (prefixWord ++ tailWord_5282974).sum := by decide
  have hdescent : baseEnd_5282974 < baseStart_5282974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5282974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283028 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_5283028 : Nat := 118140960795 + 5283028 * 2 ^ 59
def prefixEnd_5283028 : Nat := 4983230072969 + 3 ^ 40 * 5283028 * 2
def baseEnd_5283028 : Nat := 2712732675161261362353803

theorem tailTrace_5283028 : CollatzResearch.WordTrace tailWord_5283028 prefixEnd_5283028 2712732675161261362353803 := by
  unfold tailWord_5283028
  simp only [CollatzResearch.WordTrace]
  refine ⟨96343930552249650097088869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128458574069666200129451825 96343930552249650097088869)
  ·
    refine ⟨18064486978546809393204163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96343930552249650097088869 18064486978546809393204163)
    ·
      refine ⟨27096730467820214089806245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18064486978546809393204163 27096730467820214089806245)
      ·
        refine ⟨5080636962716290141838671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27096730467820214089806245 5080636962716290141838671)
        ·
          refine ⟨7620955444074435212758007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5080636962716290141838671 7620955444074435212758007)
          ·
            refine ⟨11431433166111652819137011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7620955444074435212758007 11431433166111652819137011)
            ·
              refine ⟨17147149749167479228705517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11431433166111652819137011 17147149749167479228705517)
              ·
                refine ⟨6430181155937804710764569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17147149749167479228705517 6430181155937804710764569)
                ·
                  refine ⟨4822635866953353533073427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430181155937804710764569 4822635866953353533073427)
                  ·
                    refine ⟨7233953800430030299610141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4822635866953353533073427 7233953800430030299610141)
                    ·
                      refine ⟨2712732675161261362353803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7233953800430030299610141 2712732675161261362353803)
                      ·
                        rfl

theorem cell23_5283028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_5283028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283028 prefixEnd_5283028 := by exact prefixLift 5283028
  have htrace : WordTrace (prefixWord ++ tailWord_5283028) baseStart_5283028 baseEnd_5283028 := by
    simpa [prefixWord, tailWord_5283028, baseEnd_5283028] using wordTrace_append hprefix tailTrace_5283028
  have hstable : (prefixWord ++ tailWord_5283028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283028).length < 2 ^ (prefixWord ++ tailWord_5283028).sum := by decide
  have hdescent : baseEnd_5283028 < baseStart_5283028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283057 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 5]
def baseStart_5283057 : Nat := 118140960795 + 5283057 * 2 ^ 59
def prefixEnd_5283057 : Nat := 4983230072969 + 3 ^ 40 * 5283057 * 2
def baseEnd_5283057 : Nat := 301416396233360194321241

theorem tailTrace_5283057 : CollatzResearch.WordTrace tailWord_5283057 prefixEnd_5283057 301416396233360194321241 := by
  unfold tailWord_5283057
  simp only [CollatzResearch.WordTrace]
  refine ⟨192688918821394238146983425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128459279214262825431322283 192688918821394238146983425)
  ·
    refine ⟨144516689116045678610237569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192688918821394238146983425 144516689116045678610237569)
    ·
      refine ⟨108387516837034258957678177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144516689116045678610237569 108387516837034258957678177)
      ·
        refine ⟨81290637627775694218258633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108387516837034258957678177 81290637627775694218258633)
        ·
          refine ⟨60967978220831770663693975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81290637627775694218258633 60967978220831770663693975)
          ·
            refine ⟨91451967331247655995540963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60967978220831770663693975 91451967331247655995540963)
            ·
              refine ⟨137177950996871483993311445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91451967331247655995540963 137177950996871483993311445)
              ·
                refine ⟨3215108226489175406093237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137177950996871483993311445 3215108226489175406093237)
                ·
                  refine ⟨301416396233360194321241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3215108226489175406093237 301416396233360194321241)
                  ·
                    rfl

theorem cell23_5283057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 5].length) (baseStart_5283057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283057 prefixEnd_5283057 := by exact prefixLift 5283057
  have htrace : WordTrace (prefixWord ++ tailWord_5283057) baseStart_5283057 baseEnd_5283057 := by
    simpa [prefixWord, tailWord_5283057, baseEnd_5283057] using wordTrace_append hprefix tailTrace_5283057
  have hstable : (prefixWord ++ tailWord_5283057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283057).length < 2 ^ (prefixWord ++ tailWord_5283057).sum := by decide
  have hdescent : baseEnd_5283057 < baseStart_5283057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283068 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_5283068 : Nat := 118140960795 + 5283068 * 2 ^ 59
def prefixEnd_5283068 : Nat := 4983230072969 + 3 ^ 40 * 5283068 * 2
def baseEnd_5283068 : Nat := 2712753214387441205853619

theorem tailTrace_5283068 : CollatzResearch.WordTrace tailWord_5283068 prefixEnd_5283068 2712753214387441205853619 := by
  unfold tailWord_5283068
  simp only [CollatzResearch.WordTrace]
  refine ⟨96344660012177193512816929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128459546682902924683755905 96344660012177193512816929)
  ·
    refine ⟨72258495009132895134612697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96344660012177193512816929 72258495009132895134612697)
    ·
      refine ⟨54193871256849671350959523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72258495009132895134612697 54193871256849671350959523)
      ·
        refine ⟨81290806885274507026439285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54193871256849671350959523 81290806885274507026439285)
        ·
          refine ⟨7621013145494485033728683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81290806885274507026439285 7621013145494485033728683)
          ·
            refine ⟨11431519718241727550593025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7621013145494485033728683 11431519718241727550593025)
            ·
              refine ⟨8573639788681295662944769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11431519718241727550593025 8573639788681295662944769)
              ·
                refine ⟨6430229841510971747208577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8573639788681295662944769 6430229841510971747208577)
                ·
                  refine ⟨4822672381133228810406433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430229841510971747208577 4822672381133228810406433)
                  ·
                    refine ⟨3617004285849921607804825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4822672381133228810406433 3617004285849921607804825)
                    ·
                      refine ⟨2712753214387441205853619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617004285849921607804825 2712753214387441205853619)
                      ·
                        rfl

theorem cell23_5283068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_5283068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283068 prefixEnd_5283068 := by exact prefixLift 5283068
  have htrace : WordTrace (prefixWord ++ tailWord_5283068) baseStart_5283068 baseEnd_5283068 := by
    simpa [prefixWord, tailWord_5283068, baseEnd_5283068] using wordTrace_append hprefix tailTrace_5283068
  have hstable : (prefixWord ++ tailWord_5283068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283068).length < 2 ^ (prefixWord ++ tailWord_5283068).sum := by decide
  have hdescent : baseEnd_5283068 < baseStart_5283068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283077 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 7, 2]
def baseStart_5283077 : Nat := 118140960795 + 5283077 * 2 ^ 59
def prefixEnd_5283077 : Nat := 4983230072969 + 3 ^ 40 * 5283077 * 2
def baseEnd_5283077 : Nat := 2712757835713331670641077

theorem tailTrace_5283077 : CollatzResearch.WordTrace tailWord_5283077 prefixEnd_5283077 2712757835713331670641077 := by
  unfold tailWord_5283077
  simp only [CollatzResearch.WordTrace]
  refine ⟨192689648281321781562711485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128459765520881187708474323 192689648281321781562711485)
  ·
    refine ⟨72258618105495668086016807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192689648281321781562711485 72258618105495668086016807)
    ·
      refine ⟨108387927158243502129025211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72258618105495668086016807 108387927158243502129025211)
      ·
        refine ⟨162581890737365253193537817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108387927158243502129025211 162581890737365253193537817)
        ·
          refine ⟨121936418053023939895153363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162581890737365253193537817 121936418053023939895153363)
          ·
            refine ⟨182904627079535909842730045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121936418053023939895153363 182904627079535909842730045)
            ·
              refine ⟨68589235154825966191023767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182904627079535909842730045 68589235154825966191023767)
              ·
                refine ⟨102883852732238949286535651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68589235154825966191023767 102883852732238949286535651)
                ·
                  refine ⟨154325779098358423929803477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102883852732238949286535651 154325779098358423929803477)
                  ·
                    refine ⟨3617010447617775560854769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154325779098358423929803477 3617010447617775560854769)
                    ·
                      refine ⟨2712757835713331670641077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617010447617775560854769 2712757835713331670641077)
                      ·
                        rfl

theorem cell23_5283077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_5283077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283077 prefixEnd_5283077 := by exact prefixLift 5283077
  have htrace : WordTrace (prefixWord ++ tailWord_5283077) baseStart_5283077 baseEnd_5283077 := by
    simpa [prefixWord, tailWord_5283077, baseEnd_5283077] using wordTrace_append hprefix tailTrace_5283077
  have hstable : (prefixWord ++ tailWord_5283077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283077).length < 2 ^ (prefixWord ++ tailWord_5283077).sum := by decide
  have hdescent : baseEnd_5283077 < baseStart_5283077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283107 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4]
def baseStart_5283107 : Nat := 118140960795 + 5283107 * 2 ^ 59
def prefixEnd_5283107 : Nat := 4983230072969 + 3 ^ 40 * 5283107 * 2
def baseEnd_5283107 : Nat := 2712773240132966553265939

theorem tailTrace_5283107 : CollatzResearch.WordTrace tailWord_5283107 prefixEnd_5283107 2712773240132966553265939 := by
  unfold tailWord_5283107
  simp only [CollatzResearch.WordTrace]
  refine ⟨192690742471213096686303575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128460494980808731124202383 192690742471213096686303575)
  ·
    refine ⟨289036113706819645029455363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192690742471213096686303575 289036113706819645029455363)
    ·
      refine ⟨433554170560229467544183045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289036113706819645029455363 433554170560229467544183045)
      ·
        refine ⟨81291406980043025164534321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 433554170560229467544183045 81291406980043025164534321)
        ·
          refine ⟨60968555235032268873400741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81291406980043025164534321 60968555235032268873400741)
          ·
            refine ⟨11431604106568550413762639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60968555235032268873400741 11431604106568550413762639)
            ·
              refine ⟨17147406159852825620643959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11431604106568550413762639 17147406159852825620643959)
              ·
                refine ⟨25721109239779238430965939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17147406159852825620643959 25721109239779238430965939)
                ·
                  refine ⟨38581663859668857646448909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25721109239779238430965939 38581663859668857646448909)
                  ·
                    refine ⟨14468123947375821617418341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38581663859668857646448909 14468123947375821617418341)
                    ·
                      refine ⟨2712773240132966553265939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14468123947375821617418341 2712773240132966553265939)
                      ·
                        rfl

theorem cell23_5283107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_5283107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283107 prefixEnd_5283107 := by exact prefixLift 5283107
  have htrace : WordTrace (prefixWord ++ tailWord_5283107) baseStart_5283107 baseEnd_5283107 := by
    simpa [prefixWord, tailWord_5283107, baseEnd_5283107] using wordTrace_append hprefix tailTrace_5283107
  have hstable : (prefixWord ++ tailWord_5283107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283107).length < 2 ^ (prefixWord ++ tailWord_5283107).sum := by decide
  have hdescent : baseEnd_5283107 < baseStart_5283107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283120 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_5283120 : Nat := 118140960795 + 5283120 * 2 ^ 59
def prefixEnd_5283120 : Nat := 4983230072969 + 3 ^ 40 * 5283120 * 2
def baseEnd_5283120 : Nat := 2712779915381475002403379

theorem tailTrace_5283120 : CollatzResearch.WordTrace tailWord_5283120 prefixEnd_5283120 2712779915381475002403379 := by
  unfold tailWord_5283120
  simp only [CollatzResearch.WordTrace]
  refine ⟨96345608310082999953263407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128460811080110666604351209 96345608310082999953263407)
  ·
    refine ⟨144518412465124499929895111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96345608310082999953263407 144518412465124499929895111)
    ·
      refine ⟨216777618697686749894842667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144518412465124499929895111 216777618697686749894842667)
      ·
        refine ⟨325166428046530124842264001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216777618697686749894842667 325166428046530124842264001)
        ·
          refine ⟨243874821034897593631698001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325166428046530124842264001 243874821034897593631698001)
          ·
            refine ⟨182906115776173195223773501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243874821034897593631698001 182906115776173195223773501)
            ·
              refine ⟨68589793416064948208915063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182906115776173195223773501 68589793416064948208915063)
              ·
                refine ⟨102884690124097422313372595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68589793416064948208915063 102884690124097422313372595)
                ·
                  refine ⟨154327035186146133470058893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102884690124097422313372595 154327035186146133470058893)
                  ·
                    refine ⟨57872638194804800051272085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154327035186146133470058893 57872638194804800051272085)
                    ·
                      refine ⟨2712779915381475002403379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57872638194804800051272085 2712779915381475002403379)
                      ·
                        rfl

theorem cell23_5283120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_5283120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283120 prefixEnd_5283120 := by exact prefixLift 5283120
  have htrace : WordTrace (prefixWord ++ tailWord_5283120) baseStart_5283120 baseEnd_5283120 := by
    simpa [prefixWord, tailWord_5283120, baseEnd_5283120] using wordTrace_append hprefix tailTrace_5283120
  have hstable : (prefixWord ++ tailWord_5283120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283120).length < 2 ^ (prefixWord ++ tailWord_5283120).sum := by decide
  have hdescent : baseEnd_5283120 < baseStart_5283120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283124 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5283124 : Nat := 118140960795 + 5283124 * 2 ^ 59
def prefixEnd_5283124 : Nat := 4983230072969 + 3 ^ 40 * 5283124 * 2
def baseEnd_5283124 : Nat := 2712781969304092986753361

theorem tailTrace_5283124 : CollatzResearch.WordTrace tailWord_5283124 prefixEnd_5283124 2712781969304092986753361 := by
  unfold tailWord_5283124
  simp only [CollatzResearch.WordTrace]
  refine ⟨96345681256075754294836213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128460908341434339059781617 96345681256075754294836213)
  ·
    refine ⟨9032407617757101965140895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96345681256075754294836213 9032407617757101965140895)
    ·
      refine ⟨13548611426635652947711343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9032407617757101965140895 13548611426635652947711343)
      ·
        refine ⟨20322917139953479421567015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13548611426635652947711343 20322917139953479421567015)
        ·
          refine ⟨30484375709930219132350523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20322917139953479421567015 30484375709930219132350523)
          ·
            refine ⟨45726563564895328698525785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30484375709930219132350523 45726563564895328698525785)
            ·
              refine ⟨34294922673671496523894339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45726563564895328698525785 34294922673671496523894339)
              ·
                refine ⟨51442384010507244785841509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34294922673671496523894339 51442384010507244785841509)
                ·
                  refine ⟨9645447001970108397345283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51442384010507244785841509 9645447001970108397345283)
                  ·
                    refine ⟨14468170502955162596017925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9645447001970108397345283 14468170502955162596017925)
                    ·
                      refine ⟨2712781969304092986753361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14468170502955162596017925 2712781969304092986753361)
                      ·
                        rfl

theorem cell23_5283124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5283124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283124 prefixEnd_5283124 := by exact prefixLift 5283124
  have htrace : WordTrace (prefixWord ++ tailWord_5283124) baseStart_5283124 baseEnd_5283124 := by
    simpa [prefixWord, tailWord_5283124, baseEnd_5283124] using wordTrace_append hprefix tailTrace_5283124
  have hstable : (prefixWord ++ tailWord_5283124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283124).length < 2 ^ (prefixWord ++ tailWord_5283124).sum := by decide
  have hdescent : baseEnd_5283124 < baseStart_5283124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283168 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 1, 4]
def baseStart_5283168 : Nat := 118140960795 + 5283168 * 2 ^ 59
def prefixEnd_5283168 : Nat := 4983230072969 + 3 ^ 40 * 5283168 * 2
def baseEnd_5283168 : Nat := 904268187484296938201053

theorem tailTrace_5283168 : CollatzResearch.WordTrace tailWord_5283168 prefixEnd_5283168 904268187484296938201053 := by
  unfold tailWord_5283168
  simp only [CollatzResearch.WordTrace]
  refine ⟨96346483661996052052137079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128461978215994736069516105 96346483661996052052137079)
  ·
    refine ⟨144519725492994078078205619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96346483661996052052137079 144519725492994078078205619)
    ·
      refine ⟨216779588239491117117308429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144519725492994078078205619 216779588239491117117308429)
      ·
        refine ⟨81292345589809168918990661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216779588239491117117308429 81292345589809168918990661)
        ·
          refine ⟨15242314798089219172310749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81292345589809168918990661 15242314798089219172310749)
          ·
            refine ⟨5715868049283457189616531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15242314798089219172310749 5715868049283457189616531)
            ·
              refine ⟨8573802073925185784424797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5715868049283457189616531 8573802073925185784424797)
              ·
                refine ⟨3215175777721944669159299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8573802073925185784424797 3215175777721944669159299)
                ·
                  refine ⟨4822763666582917003738949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215175777721944669159299 4822763666582917003738949)
                  ·
                    refine ⟨904268187484296938201053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4822763666582917003738949 904268187484296938201053)
                    ·
                      rfl

theorem cell23_5283168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 1, 4].length) (baseStart_5283168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283168 prefixEnd_5283168 := by exact prefixLift 5283168
  have htrace : WordTrace (prefixWord ++ tailWord_5283168) baseStart_5283168 baseEnd_5283168 := by
    simpa [prefixWord, tailWord_5283168, baseEnd_5283168] using wordTrace_append hprefix tailTrace_5283168
  have hstable : (prefixWord ++ tailWord_5283168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283168).length < 2 ^ (prefixWord ++ tailWord_5283168).sum := by decide
  have hdescent : baseEnd_5283168 < baseStart_5283168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283198 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 6]
def baseStart_5283198 : Nat := 118140960795 + 5283198 * 2 ^ 59
def prefixEnd_5283198 : Nat := 4983230072969 + 3 ^ 40 * 5283198 * 2
def baseEnd_5283198 : Nat := 301424440763613966358669

theorem tailTrace_5283198 : CollatzResearch.WordTrace tailWord_5283198 prefixEnd_5283198 301424440763613966358669 := by
  unfold tailWord_5283198
  simp only [CollatzResearch.WordTrace]
  refine ⟨24086757689235427403483281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128462707675922279485244165 24086757689235427403483281)
  ·
    refine ⟨18065068266926570552612461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24086757689235427403483281 18065068266926570552612461)
    ·
      refine ⟨6774400600097463957229673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18065068266926570552612461 6774400600097463957229673)
      ·
        refine ⟨5080800450073097967922255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6774400600097463957229673 5080800450073097967922255)
        ·
          refine ⟨7621200675109646951883383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5080800450073097967922255 7621200675109646951883383)
          ·
            refine ⟨11431801012664470427825075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7621200675109646951883383 11431801012664470427825075)
            ·
              refine ⟨17147701518996705641737613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11431801012664470427825075 17147701518996705641737613)
              ·
                refine ⟨6430388069623764615651605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17147701518996705641737613 6430388069623764615651605)
                ·
                  refine ⟨301424440763613966358669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6430388069623764615651605 301424440763613966358669)
                  ·
                    rfl

theorem cell23_5283198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_5283198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283198 prefixEnd_5283198 := by exact prefixLift 5283198
  have htrace : WordTrace (prefixWord ++ tailWord_5283198) baseStart_5283198 baseEnd_5283198 := by
    simpa [prefixWord, tailWord_5283198, baseEnd_5283198] using wordTrace_append hprefix tailTrace_5283198
  have hstable : (prefixWord ++ tailWord_5283198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283198).length < 2 ^ (prefixWord ++ tailWord_5283198).sum := by decide
  have hdescent : baseEnd_5283198 < baseStart_5283198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283217 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 3]
def baseStart_5283217 : Nat := 118140960795 + 5283217 * 2 ^ 59
def prefixEnd_5283217 : Nat := 4983230072969 + 3 ^ 40 * 5283217 * 2
def baseEnd_5283217 : Nat := 2712829723004961122890433

theorem tailTrace_5283217 : CollatzResearch.WordTrace tailWord_5283217 prefixEnd_5283217 2712829723004961122890433 := by
  unfold tailWord_5283217
  simp only [CollatzResearch.WordTrace]
  refine ⟨192694754500814585472807905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128463169667209723648538603 192694754500814585472807905)
  ·
    refine ⟨144521065875610939104605929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192694754500814585472807905 144521065875610939104605929)
    ·
      refine ⟨108390799406708204328454447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144521065875610939104605929 108390799406708204328454447)
      ·
        refine ⟨162586199110062306492681671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108390799406708204328454447 162586199110062306492681671)
        ·
          refine ⟨243879298665093459739022507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162586199110062306492681671 243879298665093459739022507)
          ·
            refine ⟨365818947997640189608533761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243879298665093459739022507 365818947997640189608533761)
            ·
              refine ⟨274364210998230142206400321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365818947997640189608533761 274364210998230142206400321)
              ·
                refine ⟨205773158248672606654800241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274364210998230142206400321 205773158248672606654800241)
                ·
                  refine ⟨154329868686504454991100181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205773158248672606654800241 154329868686504454991100181)
                  ·
                    refine ⟨7234212594679896327707821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 154329868686504454991100181 7234212594679896327707821)
                    ·
                      refine ⟨2712829723004961122890433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234212594679896327707821 2712829723004961122890433)
                      ·
                        rfl

theorem cell23_5283217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_5283217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283217 prefixEnd_5283217 := by exact prefixLift 5283217
  have htrace : WordTrace (prefixWord ++ tailWord_5283217) baseStart_5283217 baseEnd_5283217 := by
    simpa [prefixWord, tailWord_5283217, baseEnd_5283217] using wordTrace_append hprefix tailTrace_5283217
  have hstable : (prefixWord ++ tailWord_5283217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283217).length < 2 ^ (prefixWord ++ tailWord_5283217).sum := by decide
  have hdescent : baseEnd_5283217 < baseStart_5283217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283264 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_5283264 : Nat := 118140960795 + 5283264 * 2 ^ 59
def prefixEnd_5283264 : Nat := 4983230072969 + 3 ^ 40 * 5283264 * 2
def baseEnd_5283264 : Nat := 2712853856595722439002717

theorem tailTrace_5283264 : CollatzResearch.WordTrace tailWord_5283264 prefixEnd_5283264 2712853856595722439002717 := by
  unfold tailWord_5283264
  simp only [CollatzResearch.WordTrace]
  refine ⟨96348234365822156249884423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128464312487762874999845897 96348234365822156249884423)
  ·
    refine ⟨144522351548733234374826635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96348234365822156249884423 144522351548733234374826635)
    ·
      refine ⟨216783527323099851562239953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144522351548733234374826635 216783527323099851562239953)
      ·
        refine ⟨162587645492324888671679965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216783527323099851562239953 162587645492324888671679965)
        ·
          refine ⟨60970367059621833251879987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162587645492324888671679965 60970367059621833251879987)
          ·
            refine ⟨91455550589432749877819981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60970367059621833251879987 91455550589432749877819981)
            ·
              refine ⟨34295831471037281204182493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91455550589432749877819981 34295831471037281204182493)
              ·
                refine ⟨12860936801638980451568435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34295831471037281204182493 12860936801638980451568435)
                ·
                  refine ⟨19291405202458470677352653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12860936801638980451568435 19291405202458470677352653)
                  ·
                    refine ⟨7234276950921926504007245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19291405202458470677352653 7234276950921926504007245)
                    ·
                      refine ⟨2712853856595722439002717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234276950921926504007245 2712853856595722439002717)
                      ·
                        rfl

theorem cell23_5283264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_5283264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283264 prefixEnd_5283264 := by exact prefixLift 5283264
  have htrace : WordTrace (prefixWord ++ tailWord_5283264) baseStart_5283264 baseEnd_5283264 := by
    simpa [prefixWord, tailWord_5283264, baseEnd_5283264] using wordTrace_append hprefix tailTrace_5283264
  have hstable : (prefixWord ++ tailWord_5283264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283264).length < 2 ^ (prefixWord ++ tailWord_5283264).sum := by decide
  have hdescent : baseEnd_5283264 < baseStart_5283264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283307 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5]
def baseStart_5283307 : Nat := 118140960795 + 5283307 * 2 ^ 59
def prefixEnd_5283307 : Nat := 4983230072969 + 3 ^ 40 * 5283307 * 2
def baseEnd_5283307 : Nat := 2712875936263865770765019

theorem tailTrace_5283307 : CollatzResearch.WordTrace tailWord_5283307 prefixEnd_5283307 2712875936263865770765019 := by
  unfold tailWord_5283307
  simp only [CollatzResearch.WordTrace]
  refine ⟨192698037070488530843584175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128465358046992353895722783 192698037070488530843584175)
  ·
    refine ⟨289047055605732796265376263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192698037070488530843584175 289047055605732796265376263)
    ·
      refine ⟨433570583408599194398064395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289047055605732796265376263 433570583408599194398064395)
      ·
        refine ⟨650355875112898791597096593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433570583408599194398064395 650355875112898791597096593)
        ·
          refine ⟨487766906334674093697822445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650355875112898791597096593 487766906334674093697822445)
          ·
            refine ⟨182912589875502785136683417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487766906334674093697822445 182912589875502785136683417)
            ·
              refine ⟨137184442406627088852512563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182912589875502785136683417 137184442406627088852512563)
              ·
                refine ⟨205776663609940633278768845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137184442406627088852512563 205776663609940633278768845)
                ·
                  refine ⟨77166248853727737479538317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205776663609940633278768845 77166248853727737479538317)
                  ·
                    refine ⟨28937343320147901554826869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77166248853727737479538317 28937343320147901554826869)
                    ·
                      refine ⟨2712875936263865770765019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28937343320147901554826869 2712875936263865770765019)
                      ·
                        rfl

theorem cell23_5283307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_5283307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283307 prefixEnd_5283307 := by exact prefixLift 5283307
  have htrace : WordTrace (prefixWord ++ tailWord_5283307) baseStart_5283307 baseEnd_5283307 := by
    simpa [prefixWord, tailWord_5283307, baseEnd_5283307] using wordTrace_append hprefix tailTrace_5283307
  have hstable : (prefixWord ++ tailWord_5283307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283307).length < 2 ^ (prefixWord ++ tailWord_5283307).sum := by decide
  have hdescent : baseEnd_5283307 < baseStart_5283307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283324 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_5283324 : Nat := 118140960795 + 5283324 * 2 ^ 59
def prefixEnd_5283324 : Nat := 4983230072969 + 3 ^ 40 * 5283324 * 2
def baseEnd_5283324 : Nat := 2712884665434992204252441

theorem tailTrace_5283324 : CollatzResearch.WordTrace tailWord_5283324 prefixEnd_5283324 2712884665434992204252441 := by
  unfold tailWord_5283324
  simp only [CollatzResearch.WordTrace]
  refine ⟨96349328555713471373476513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128465771407617961831302017 96349328555713471373476513)
  ·
    refine ⟨72261996416785103530107385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96349328555713471373476513 72261996416785103530107385)
    ·
      refine ⟨54196497312588827647580539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72261996416785103530107385 54196497312588827647580539)
      ·
        refine ⟨81294745968883241471370809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54196497312588827647580539 81294745968883241471370809)
        ·
          refine ⟨60971059476662431103528107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81294745968883241471370809 60971059476662431103528107)
          ·
            refine ⟨91456589214993646655292161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60971059476662431103528107 91456589214993646655292161)
            ·
              refine ⟨68592441911245234991469121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91456589214993646655292161 68592441911245234991469121)
              ·
                refine ⟨51444331433433926243601841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68592441911245234991469121 51444331433433926243601841)
                ·
                  refine ⟨38583248575075444682701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51444331433433926243601841 38583248575075444682701381)
                  ·
                    refine ⟨7234359107826645878006509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38583248575075444682701381 7234359107826645878006509)
                    ·
                      refine ⟨2712884665434992204252441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234359107826645878006509 2712884665434992204252441)
                      ·
                        rfl

theorem cell23_5283324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_5283324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283324 prefixEnd_5283324 := by exact prefixLift 5283324
  have htrace : WordTrace (prefixWord ++ tailWord_5283324) baseStart_5283324 baseEnd_5283324 := by
    simpa [prefixWord, tailWord_5283324, baseEnd_5283324] using wordTrace_append hprefix tailTrace_5283324
  have hstable : (prefixWord ++ tailWord_5283324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283324).length < 2 ^ (prefixWord ++ tailWord_5283324).sum := by decide
  have hdescent : baseEnd_5283324 < baseStart_5283324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283327 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 9]
def baseStart_5283327 : Nat := 118140960795 + 5283327 * 2 ^ 59
def prefixEnd_5283327 : Nat := 4983230072969 + 3 ^ 40 * 5283327 * 2
def baseEnd_5283327 : Nat := 301431800652995076946103

theorem tailTrace_5283327 : CollatzResearch.WordTrace tailWord_5283327 prefixEnd_5283327 301431800652995076946103 := by
  unfold tailWord_5283327
  simp only [CollatzResearch.WordTrace]
  refine ⟨192698766530416074259312235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128465844353610716172874823 192698766530416074259312235)
  ·
    refine ⟨289048149795624111388968353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192698766530416074259312235 289048149795624111388968353)
    ·
      refine ⟨216786112346718083541726265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289048149795624111388968353 216786112346718083541726265)
      ·
        refine ⟨162589584260038562656294699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216786112346718083541726265 162589584260038562656294699)
        ·
          refine ⟨243884376390057843984442049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162589584260038562656294699 243884376390057843984442049)
          ·
            refine ⟨182913282292543382988331537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243884376390057843984442049 182913282292543382988331537)
            ·
              refine ⟨137184961719407537241248653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182913282292543382988331537 137184961719407537241248653)
              ·
                refine ⟨51444360644777826465468245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137184961719407537241248653 51444360644777826465468245)
                ·
                  refine ⟨301431800652995076946103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51444360644777826465468245 301431800652995076946103)
                  ·
                    rfl

theorem cell23_5283327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 9].length) (baseStart_5283327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283327 prefixEnd_5283327 := by exact prefixLift 5283327
  have htrace : WordTrace (prefixWord ++ tailWord_5283327) baseStart_5283327 baseEnd_5283327 := by
    simpa [prefixWord, tailWord_5283327, baseEnd_5283327] using wordTrace_append hprefix tailTrace_5283327
  have hstable : (prefixWord ++ tailWord_5283327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283327).length < 2 ^ (prefixWord ++ tailWord_5283327).sum := by decide
  have hdescent : baseEnd_5283327 < baseStart_5283327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283338 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_5283338 : Nat := 118140960795 + 5283338 * 2 ^ 59
def prefixEnd_5283338 : Nat := 4983230072969 + 3 ^ 40 * 5283338 * 2
def baseEnd_5283338 : Nat := 2712891854164155149477377

theorem tailTrace_5283338 : CollatzResearch.WordTrace tailWord_5283338 prefixEnd_5283338 2712891854164155149477377 := by
  unfold tailWord_5283338
  simp only [CollatzResearch.WordTrace]
  refine ⟨48174791933344055784490667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128466111822250815425308445 48174791933344055784490667)
  ·
    refine ⟨72262187900016083676736001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48174791933344055784490667 72262187900016083676736001)
    ·
      refine ⟨54196640925012062757552001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72262187900016083676736001 54196640925012062757552001)
      ·
        refine ⟨40647480693759047068164001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54196640925012062757552001 40647480693759047068164001)
        ·
          refine ⟨30485610520319285301123001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40647480693759047068164001 30485610520319285301123001)
          ·
            refine ⟨22864207890239463975842251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30485610520319285301123001 22864207890239463975842251)
            ·
              refine ⟨34296311835359195963763377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22864207890239463975842251 34296311835359195963763377)
              ·
                refine ⟨25722233876519396972822533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34296311835359195963763377 25722233876519396972822533)
                ·
                  refine ⟨4822918851847386932404225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25722233876519396972822533 4822918851847386932404225)
                  ·
                    refine ⟨3617189138885540199303169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4822918851847386932404225 3617189138885540199303169)
                    ·
                      refine ⟨2712891854164155149477377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617189138885540199303169 2712891854164155149477377)
                      ·
                        rfl

theorem cell23_5283338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_5283338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283338 prefixEnd_5283338 := by exact prefixLift 5283338
  have htrace : WordTrace (prefixWord ++ tailWord_5283338) baseStart_5283338 baseEnd_5283338 := by
    simpa [prefixWord, tailWord_5283338, baseEnd_5283338] using wordTrace_append hprefix tailTrace_5283338
  have hstable : (prefixWord ++ tailWord_5283338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283338).length < 2 ^ (prefixWord ++ tailWord_5283338).sum := by decide
  have hdescent : baseEnd_5283338 < baseStart_5283338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283361 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 7]
def baseStart_5283361 : Nat := 118140960795 + 5283361 * 2 ^ 59
def prefixEnd_5283361 : Nat := 4983230072969 + 3 ^ 40 * 5283361 * 2
def baseEnd_5283361 : Nat := 301433740468800951054419

theorem tailTrace_5283361 : CollatzResearch.WordTrace tailWord_5283361 prefixEnd_5283361 301433740468800951054419 := by
  unfold tailWord_5283361
  simp only [CollatzResearch.WordTrace]
  refine ⟨192700006612292898066049937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128466671074861932044033291 192700006612292898066049937)
  ·
    refine ⟨144525004959219673549537453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192700006612292898066049937 144525004959219673549537453)
    ·
      refine ⟨54196876859707377581076545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144525004959219673549537453 54196876859707377581076545)
      ·
        refine ⟨40647657644780533185807409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54196876859707377581076545 40647657644780533185807409)
        ·
          refine ⟨30485743233585399889355557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40647657644780533185807409 30485743233585399889355557)
          ·
            refine ⟨5716076856297262479254167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30485743233585399889355557 5716076856297262479254167)
            ·
              refine ⟨8574115284445893718881251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716076856297262479254167 8574115284445893718881251)
              ·
                refine ⟨12861172926668840578321877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574115284445893718881251 12861172926668840578321877)
                ·
                  refine ⟨301433740468800951054419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12861172926668840578321877 301433740468800951054419)
                  ·
                    rfl

theorem cell23_5283361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 7].length) (baseStart_5283361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283361 prefixEnd_5283361 := by exact prefixLift 5283361
  have htrace : WordTrace (prefixWord ++ tailWord_5283361) baseStart_5283361 baseEnd_5283361 := by
    simpa [prefixWord, tailWord_5283361, baseEnd_5283361] using wordTrace_append hprefix tailTrace_5283361
  have hstable : (prefixWord ++ tailWord_5283361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283361).length < 2 ^ (prefixWord ++ tailWord_5283361).sum := by decide
  have hdescent : baseEnd_5283361 < baseStart_5283361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283391 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 2, 5]
def baseStart_5283391 : Nat := 118140960795 + 5283391 * 2 ^ 59
def prefixEnd_5283391 : Nat := 4983230072969 + 3 ^ 40 * 5283391 * 2
def baseEnd_5283391 : Nat := 904306356212947814038211

theorem tailTrace_5283391 : CollatzResearch.WordTrace tailWord_5283391 prefixEnd_5283391 904306356212947814038211 := by
  unfold tailWord_5283391
  simp only [CollatzResearch.WordTrace]
  refine ⟨192701100802184213189642027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128467400534789475459761351 192701100802184213189642027)
  ·
    refine ⟨289051651203276319784463041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192701100802184213189642027 289051651203276319784463041)
    ·
      refine ⟨216788738402457239838347281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289051651203276319784463041 216788738402457239838347281)
      ·
        refine ⟨162591553801842929878760461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216788738402457239838347281 162591553801842929878760461)
        ·
          refine ⟨60971832675691098704535173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162591553801842929878760461 60971832675691098704535173)
          ·
            refine ⟨11432218626692081007100345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60971832675691098704535173 11432218626692081007100345)
            ·
              refine ⟨8574163970019060755325259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11432218626692081007100345 8574163970019060755325259)
              ·
                refine ⟨12861245955028591132987889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574163970019060755325259 12861245955028591132987889)
                ·
                  refine ⟨9645934466271443349740917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12861245955028591132987889 9645934466271443349740917)
                  ·
                    refine ⟨904306356212947814038211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9645934466271443349740917 904306356212947814038211)
                    ·
                      rfl

theorem cell23_5283391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_5283391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283391 prefixEnd_5283391 := by exact prefixLift 5283391
  have htrace : WordTrace (prefixWord ++ tailWord_5283391) baseStart_5283391 baseEnd_5283391 := by
    simpa [prefixWord, tailWord_5283391, baseEnd_5283391] using wordTrace_append hprefix tailTrace_5283391
  have hstable : (prefixWord ++ tailWord_5283391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283391).length < 2 ^ (prefixWord ++ tailWord_5283391).sum := by decide
  have hdescent : baseEnd_5283391 < baseStart_5283391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283424 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_5283424 : Nat := 118140960795 + 5283424 * 2 ^ 59
def prefixEnd_5283424 : Nat := 4983230072969 + 3 ^ 40 * 5283424 * 2
def baseEnd_5283424 : Nat := 2712936013500441813001981

theorem tailTrace_5283424 : CollatzResearch.WordTrace tailWord_5283424 prefixEnd_5283424 2712936013500441813001981 := by
  unfold tailWord_5283424
  simp only [CollatzResearch.WordTrace]
  refine ⟨96351152205532329912796663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128468202940709773217062217 96351152205532329912796663)
  ·
    refine ⟨144526728308298494869194995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96351152205532329912796663 144526728308298494869194995)
    ·
      refine ⟨216790092462447742303792493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144526728308298494869194995 216790092462447742303792493)
      ·
        refine ⟨81296284673417903363922185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216790092462447742303792493 81296284673417903363922185)
        ·
          refine ⟨60972213505063427522941639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81296284673417903363922185 60972213505063427522941639)
          ·
            refine ⟨91458320257595141284412459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60972213505063427522941639 91458320257595141284412459)
            ·
              refine ⟨137187480386392711926618689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91458320257595141284412459 137187480386392711926618689)
              ·
                refine ⟨102890610289794533944964017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137187480386392711926618689 102890610289794533944964017)
                ·
                  refine ⟨77167957717345900458723013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102890610289794533944964017 77167957717345900458723013)
                  ·
                    refine ⟨14468992072002356336010565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77167957717345900458723013 14468992072002356336010565)
                    ·
                      refine ⟨2712936013500441813001981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14468992072002356336010565 2712936013500441813001981)
                      ·
                        rfl

theorem cell23_5283424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_5283424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283424 prefixEnd_5283424 := by exact prefixLift 5283424
  have htrace : WordTrace (prefixWord ++ tailWord_5283424) baseStart_5283424 baseEnd_5283424 := by
    simpa [prefixWord, tailWord_5283424, baseEnd_5283424] using wordTrace_append hprefix tailTrace_5283424
  have hstable : (prefixWord ++ tailWord_5283424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283424).length < 2 ^ (prefixWord ++ tailWord_5283424).sum := by decide
  have hdescent : baseEnd_5283424 < baseStart_5283424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283428 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_5283428 : Nat := 118140960795 + 5283428 * 2 ^ 59
def prefixEnd_5283428 : Nat := 4983230072969 + 3 ^ 40 * 5283428 * 2
def baseEnd_5283428 : Nat := 2712938067423059797351963

theorem tailTrace_5283428 : CollatzResearch.WordTrace tailWord_5283428 prefixEnd_5283428 2712938067423059797351963 := by
  unfold tailWord_5283428
  simp only [CollatzResearch.WordTrace]
  refine ⟨96351225151525084254369469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128468300202033445672492625 96351225151525084254369469)
  ·
    refine ⟨36131709431821906595388551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96351225151525084254369469 36131709431821906595388551)
    ·
      refine ⟨54197564147732859893082827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36131709431821906595388551 54197564147732859893082827)
      ·
        refine ⟨81296346221599289839624241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54197564147732859893082827 81296346221599289839624241)
        ·
          refine ⟨60972259666199467379718181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81296346221599289839624241 60972259666199467379718181)
          ·
            refine ⟨11432298687412400133697159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60972259666199467379718181 11432298687412400133697159)
            ·
              refine ⟨17148448031118600200545739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11432298687412400133697159 17148448031118600200545739)
              ·
                refine ⟨25722672046677900300818609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17148448031118600200545739 25722672046677900300818609)
                ·
                  refine ⟨19292004035008425225613957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25722672046677900300818609 19292004035008425225613957)
                  ·
                    refine ⟨3617250756564079729802617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19292004035008425225613957 3617250756564079729802617)
                    ·
                      refine ⟨2712938067423059797351963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617250756564079729802617 2712938067423059797351963)
                      ·
                        rfl

theorem cell23_5283428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_5283428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283428 prefixEnd_5283428 := by exact prefixLift 5283428
  have htrace : WordTrace (prefixWord ++ tailWord_5283428) baseStart_5283428 baseEnd_5283428 := by
    simpa [prefixWord, tailWord_5283428, baseEnd_5283428] using wordTrace_append hprefix tailTrace_5283428
  have hstable : (prefixWord ++ tailWord_5283428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283428).length < 2 ^ (prefixWord ++ tailWord_5283428).sum := by decide
  have hdescent : baseEnd_5283428 < baseStart_5283428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283431 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_5283431 : Nat := 118140960795 + 5283431 * 2 ^ 59
def prefixEnd_5283431 : Nat := 4983230072969 + 3 ^ 40 * 5283431 * 2
def baseEnd_5283431 : Nat := 2712939607865023285614449

theorem tailTrace_5283431 : CollatzResearch.WordTrace tailWord_5283431 prefixEnd_5283431 2712939607865023285614449 := by
  unfold tailWord_5283431
  simp only [CollatzResearch.WordTrace]
  refine ⟨192702559722039300021098147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128468373148026200014065431 192702559722039300021098147)
  ·
    refine ⟨289053839583058950031647221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192702559722039300021098147 289053839583058950031647221)
    ·
      refine ⟨27098797460911776565466927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 289053839583058950031647221 27098797460911776565466927)
      ·
        refine ⟨40648196191367664848200391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27098797460911776565466927 40648196191367664848200391)
        ·
          refine ⟨60972294287051497272300587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40648196191367664848200391 60972294287051497272300587)
          ·
            refine ⟨91458441430577245908450881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60972294287051497272300587 91458441430577245908450881)
            ·
              refine ⟨68593831072932934431338161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91458441430577245908450881 68593831072932934431338161)
              ·
                refine ⟨51445373304699700823503621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68593831072932934431338161 51445373304699700823503621)
                ·
                  refine ⟨9646007494631193904406929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51445373304699700823503621 9646007494631193904406929)
                  ·
                    refine ⟨7234505620973395428305197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9646007494631193904406929 7234505620973395428305197)
                    ·
                      refine ⟨2712939607865023285614449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234505620973395428305197 2712939607865023285614449)
                      ·
                        rfl

theorem cell23_5283431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_5283431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283431 prefixEnd_5283431 := by exact prefixLift 5283431
  have htrace : WordTrace (prefixWord ++ tailWord_5283431) baseStart_5283431 baseEnd_5283431 := by
    simpa [prefixWord, tailWord_5283431, baseEnd_5283431] using wordTrace_append hprefix tailTrace_5283431
  have hstable : (prefixWord ++ tailWord_5283431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283431).length < 2 ^ (prefixWord ++ tailWord_5283431).sum := by decide
  have hdescent : baseEnd_5283431 < baseStart_5283431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283445 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_5283445 : Nat := 118140960795 + 5283445 * 2 ^ 59
def prefixEnd_5283445 : Nat := 4983230072969 + 3 ^ 40 * 5283445 * 2
def baseEnd_5283445 : Nat := 2712946796594186230839385

theorem tailTrace_5283445 : CollatzResearch.WordTrace tailWord_5283445 prefixEnd_5283445 2712946796594186230839385 := by
  unfold tailWord_5283445
  simp only [CollatzResearch.WordTrace]
  refine ⟨192703070343988580412107789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128468713562659053608071859 192703070343988580412107789)
  ·
    refine ⟨72263651378995717654540421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192703070343988580412107789 72263651378995717654540421)
    ·
      refine ⟨13549434633561697060226329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72263651378995717654540421 13549434633561697060226329)
      ·
        refine ⟨10162075975171272795169747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13549434633561697060226329 10162075975171272795169747)
        ·
          refine ⟨15243113962756909192754621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10162075975171272795169747 15243113962756909192754621)
          ·
            refine ⟨5716167736033840947282983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15243113962756909192754621 5716167736033840947282983)
            ·
              refine ⟨8574251604050761420924475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716167736033840947282983 8574251604050761420924475)
              ·
                refine ⟨12861377406076142131386713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574251604050761420924475 12861377406076142131386713)
                ·
                  refine ⟨9646033054557106598540035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12861377406076142131386713 9646033054557106598540035)
                  ·
                    refine ⟨14469049581835659897810053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9646033054557106598540035 14469049581835659897810053)
                    ·
                      refine ⟨2712946796594186230839385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14469049581835659897810053 2712946796594186230839385)
                      ·
                        rfl

theorem cell23_5283445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_5283445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283445 prefixEnd_5283445 := by exact prefixLift 5283445
  have htrace : WordTrace (prefixWord ++ tailWord_5283445) baseStart_5283445 baseEnd_5283445 := by
    simpa [prefixWord, tailWord_5283445, baseEnd_5283445] using wordTrace_append hprefix tailTrace_5283445
  have hstable : (prefixWord ++ tailWord_5283445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283445).length < 2 ^ (prefixWord ++ tailWord_5283445).sum := by decide
  have hdescent : baseEnd_5283445 < baseStart_5283445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283471 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 5, 5, 2]
def baseStart_5283471 : Nat := 118140960795 + 5283471 * 2 ^ 59
def prefixEnd_5283471 : Nat := 4983230072969 + 3 ^ 40 * 5283471 * 2
def baseEnd_5283471 : Nat := 2712960147091203129114265

theorem tailTrace_5283471 : CollatzResearch.WordTrace tailWord_5283471 prefixEnd_5283471 2712960147091203129114265 := by
  unfold tailWord_5283471
  simp only [CollatzResearch.WordTrace]
  refine ⟨192704018641894386852554267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128469345761262924568369511 192704018641894386852554267)
  ·
    refine ⟨289056027962841580278831401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192704018641894386852554267 289056027962841580278831401)
    ·
      refine ⟨216792020972131185209123551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289056027962841580278831401 216792020972131185209123551)
      ·
        refine ⟨325188031458196777813685327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216792020972131185209123551 325188031458196777813685327)
        ·
          refine ⟨487782047187295166720527991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325188031458196777813685327 487782047187295166720527991)
          ·
            refine ⟨731673070780942750080791987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487782047187295166720527991 731673070780942750080791987)
            ·
              refine ⟨1097509606171414125121187981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731673070780942750080791987 1097509606171414125121187981)
              ·
                refine ⟨411566102314280296920445493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1097509606171414125121187981 411566102314280296920445493)
                ·
                  refine ⟨38584322091963777836291765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411566102314280296920445493 38584322091963777836291765)
                  ·
                    refine ⟨3617280196121604172152353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38584322091963777836291765 3617280196121604172152353)
                    ·
                      refine ⟨2712960147091203129114265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617280196121604172152353 2712960147091203129114265)
                      ·
                        rfl

theorem cell23_5283471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5, 2].length) (baseStart_5283471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283471 prefixEnd_5283471 := by exact prefixLift 5283471
  have htrace : WordTrace (prefixWord ++ tailWord_5283471) baseStart_5283471 baseEnd_5283471 := by
    simpa [prefixWord, tailWord_5283471, baseEnd_5283471] using wordTrace_append hprefix tailTrace_5283471
  have hstable : (prefixWord ++ tailWord_5283471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283471).length < 2 ^ (prefixWord ++ tailWord_5283471).sum := by decide
  have hdescent : baseEnd_5283471 < baseStart_5283471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283488 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 1, 5, 2]
def baseStart_5283488 : Nat := 118140960795 + 5283488 * 2 ^ 59
def prefixEnd_5283488 : Nat := 4983230072969 + 3 ^ 40 * 5283488 * 2
def baseEnd_5283488 : Nat := 2712968876262329562601687

theorem tailTrace_5283488 : CollatzResearch.WordTrace tailWord_5283488 prefixEnd_5283488 2712968876262329562601687 := by
  unfold tailWord_5283488
  simp only [CollatzResearch.WordTrace]
  refine ⟨96352319341416399377961559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128469759121888532503948745 96352319341416399377961559)
  ·
    refine ⟨144528479012124599066942339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96352319341416399377961559 144528479012124599066942339)
    ·
      refine ⟨216792718518186898600413509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144528479012124599066942339 216792718518186898600413509)
      ·
        refine ⟨40648634722160043487577533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216792718518186898600413509 40648634722160043487577533)
        ·
          refine ⟨15243238020810016307841575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40648634722160043487577533 15243238020810016307841575)
          ·
            refine ⟨22864857031215024461762363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15243238020810016307841575 22864857031215024461762363)
            ·
              refine ⟨34297285546822536692643545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22864857031215024461762363 34297285546822536692643545)
              ·
                refine ⟨25722964160116902519482659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34297285546822536692643545 25722964160116902519482659)
                ·
                  refine ⟨38584446240175353779223989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25722964160116902519482659 38584446240175353779223989)
                  ·
                    refine ⟨3617291835016439416802249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38584446240175353779223989 3617291835016439416802249)
                    ·
                      refine ⟨2712968876262329562601687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617291835016439416802249 2712968876262329562601687)
                      ·
                        rfl

theorem cell23_5283488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_5283488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283488 prefixEnd_5283488 := by exact prefixLift 5283488
  have htrace : WordTrace (prefixWord ++ tailWord_5283488) baseStart_5283488 baseEnd_5283488 := by
    simpa [prefixWord, tailWord_5283488, baseEnd_5283488] using wordTrace_append hprefix tailTrace_5283488
  have hstable : (prefixWord ++ tailWord_5283488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283488).length < 2 ^ (prefixWord ++ tailWord_5283488).sum := by decide
  have hdescent : baseEnd_5283488 < baseStart_5283488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283528 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 2, 4]
def baseStart_5283528 : Nat := 118140960795 + 5283528 * 2 ^ 59
def prefixEnd_5283528 : Nat := 4983230072969 + 3 ^ 40 * 5283528 * 2
def baseEnd_5283528 : Nat := 904329805162836468700501

theorem tailTrace_5283528 : CollatzResearch.WordTrace tailWord_5283528 prefixEnd_5283528 904329805162836468700501 := by
  unfold tailWord_5283528
  simp only [CollatzResearch.WordTrace]
  refine ⟨96353048801343942793689619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128470731735125257058252825 96353048801343942793689619)
  ·
    refine ⟨144529573202015914190534429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96353048801343942793689619 144529573202015914190534429)
    ·
      refine ⟨54198589950755967821450411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144529573202015914190534429 54198589950755967821450411)
      ·
        refine ⟨81297884926133951732175617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54198589950755967821450411 81297884926133951732175617)
        ·
          refine ⟨60973413694600463799131713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81297884926133951732175617 60973413694600463799131713)
          ·
            refine ⟨45730060270950347849348785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60973413694600463799131713 45730060270950347849348785)
            ·
              refine ⟨34297545203212760887011589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45730060270950347849348785 34297545203212760887011589)
              ·
                refine ⟨6430789725602392666314673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34297545203212760887011589 6430789725602392666314673)
                ·
                  refine ⟨4823092294201794499736005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430789725602392666314673 4823092294201794499736005)
                  ·
                    refine ⟨904329805162836468700501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823092294201794499736005 904329805162836468700501)
                    ·
                      rfl

theorem cell23_5283528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_5283528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283528 prefixEnd_5283528 := by exact prefixLift 5283528
  have htrace : WordTrace (prefixWord ++ tailWord_5283528) baseStart_5283528 baseEnd_5283528 := by
    simpa [prefixWord, tailWord_5283528, baseEnd_5283528] using wordTrace_append hprefix tailTrace_5283528
  have hstable : (prefixWord ++ tailWord_5283528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283528).length < 2 ^ (prefixWord ++ tailWord_5283528).sum := by decide
  have hdescent : baseEnd_5283528 < baseStart_5283528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283538 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_5283538 : Nat := 118140960795 + 5283538 * 2 ^ 59
def prefixEnd_5283538 : Nat := 4983230072969 + 3 ^ 40 * 5283538 * 2
def baseEnd_5283538 : Nat := 2712994550295054366976457

theorem tailTrace_5283538 : CollatzResearch.WordTrace tailWord_5283538 prefixEnd_5283538 2712994550295054366976457 := by
  unfold tailWord_5283538
  simp only [CollatzResearch.WordTrace]
  refine ⟨48176615583162914323810817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128470974888434438196828845 48176615583162914323810817)
  ·
    refine ⟨36132461687372185742858113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48176615583162914323810817 36132461687372185742858113)
    ·
      refine ⟨27099346265529139307143585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36132461687372185742858113 27099346265529139307143585)
      ·
        refine ⟨20324509699146854480357689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27099346265529139307143585 20324509699146854480357689)
        ·
          refine ⟨15243382274360140860268267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20324509699146854480357689 15243382274360140860268267)
          ·
            refine ⟨22865073411540211290402401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15243382274360140860268267 22865073411540211290402401)
            ·
              refine ⟨17148805058655158467801801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22865073411540211290402401 17148805058655158467801801)
              ·
                refine ⟨12861603793991368850851351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17148805058655158467801801 12861603793991368850851351)
                ·
                  refine ⟨19292405690987053276277027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12861603793991368850851351 19292405690987053276277027)
                  ·
                    refine ⟨28938608536480579914415541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19292405690987053276277027 28938608536480579914415541)
                    ·
                      refine ⟨2712994550295054366976457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28938608536480579914415541 2712994550295054366976457)
                      ·
                        rfl

theorem cell23_5283538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_5283538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283538 prefixEnd_5283538 := by exact prefixLift 5283538
  have htrace : WordTrace (prefixWord ++ tailWord_5283538) baseStart_5283538 baseEnd_5283538 := by
    simpa [prefixWord, tailWord_5283538, baseEnd_5283538] using wordTrace_append hprefix tailTrace_5283538
  have hstable : (prefixWord ++ tailWord_5283538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283538).length < 2 ^ (prefixWord ++ tailWord_5283538).sum := by decide
  have hdescent : baseEnd_5283538 < baseStart_5283538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283545 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 2, 4]
def baseStart_5283545 : Nat := 118140960795 + 5283545 * 2 ^ 59
def prefixEnd_5283545 : Nat := 4983230072969 + 3 ^ 40 * 5283545 * 2
def baseEnd_5283545 : Nat := 904332714886545279862975

theorem tailTrace_5283545 : CollatzResearch.WordTrace tailWord_5283545 prefixEnd_5283545 904332714886545279862975 := by
  unfold tailWord_5283545
  simp only [CollatzResearch.WordTrace]
  refine ⟨192706717643626297490748089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128471145095750864993832059 192706717643626297490748089)
  ·
    refine ⟨144530038232719723118061067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192706717643626297490748089 144530038232719723118061067)
    ·
      refine ⟨216795057349079584677091601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144530038232719723118061067 216795057349079584677091601)
      ·
        refine ⟨162596293011809688507818701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216795057349079584677091601 162596293011809688507818701)
        ·
          refine ⟨60973609879428633190432013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162596293011809688507818701 60973609879428633190432013)
          ·
            refine ⟨22865103704785737446412005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60973609879428633190432013 22865103704785737446412005)
            ·
              refine ⟨4287206944647325771202251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22865103704785737446412005 4287206944647325771202251)
              ·
                refine ⟨6430810416970988656803377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287206944647325771202251 6430810416970988656803377)
                ·
                  refine ⟨4823107812728241492602533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430810416970988656803377 4823107812728241492602533)
                  ·
                    refine ⟨904332714886545279862975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823107812728241492602533 904332714886545279862975)
                    ·
                      rfl

theorem cell23_5283545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 2, 4].length) (baseStart_5283545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283545 prefixEnd_5283545 := by exact prefixLift 5283545
  have htrace : WordTrace (prefixWord ++ tailWord_5283545) baseStart_5283545 baseEnd_5283545 := by
    simpa [prefixWord, tailWord_5283545, baseEnd_5283545] using wordTrace_append hprefix tailTrace_5283545
  have hstable : (prefixWord ++ tailWord_5283545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283545).length < 2 ^ (prefixWord ++ tailWord_5283545).sum := by decide
  have hdescent : baseEnd_5283545 < baseStart_5283545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283549 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_5283549 : Nat := 118140960795 + 5283549 * 2 ^ 59
def prefixEnd_5283549 : Nat := 4983230072969 + 3 ^ 40 * 5283549 * 2
def baseEnd_5283549 : Nat := 904333399527417941312969

theorem tailTrace_5283549 : CollatzResearch.WordTrace tailWord_5283549 prefixEnd_5283549 904333399527417941312969 := by
  unfold tailWord_5283549
  simp only [CollatzResearch.WordTrace]
  refine ⟨192706863535611806173893701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128471242357074537449262467 192706863535611806173893701)
  ·
    refine ⟨36132536912927213657605069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192706863535611806173893701 36132536912927213657605069)
    ·
      refine ⟨13549701342347705121601901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36132536912927213657605069 13549701342347705121601901)
      ·
        refine ⟨5081138003380389420600713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13549701342347705121601901 5081138003380389420600713)
        ·
          refine ⟨3810853502535292065450535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5081138003380389420600713 3810853502535292065450535)
          ·
            refine ⟨5716280253802938098175803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810853502535292065450535 5716280253802938098175803)
            ·
              refine ⟨8574420380704407147263705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716280253802938098175803 8574420380704407147263705)
              ·
                refine ⟨6430815285528305360447779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8574420380704407147263705 6430815285528305360447779)
                ·
                  refine ⟨9646222928292458040671669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6430815285528305360447779 9646222928292458040671669)
                  ·
                    refine ⟨904333399527417941312969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9646222928292458040671669 904333399527417941312969)
                    ·
                      rfl

theorem cell23_5283549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_5283549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283549 prefixEnd_5283549 := by exact prefixLift 5283549
  have htrace : WordTrace (prefixWord ++ tailWord_5283549) baseStart_5283549 baseEnd_5283549 := by
    simpa [prefixWord, tailWord_5283549, baseEnd_5283549] using wordTrace_append hprefix tailTrace_5283549
  have hstable : (prefixWord ++ tailWord_5283549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283549).length < 2 ^ (prefixWord ++ tailWord_5283549).sum := by decide
  have hdescent : baseEnd_5283549 < baseStart_5283549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283555 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5283555 : Nat := 118140960795 + 5283555 * 2 ^ 59
def prefixEnd_5283555 : Nat := 4983230072969 + 3 ^ 40 * 5283555 * 2
def baseEnd_5283555 : Nat := 2713003279466180800463879

theorem tailTrace_5283555 : CollatzResearch.WordTrace tailWord_5283555 prefixEnd_5283555 2713003279466180800463879 := by
  unfold tailWord_5283555
  simp only [CollatzResearch.WordTrace]
  refine ⟨192707082373590069198612119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128471388249060046132408079 192707082373590069198612119)
  ·
    refine ⟨289060623560385103797918179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192707082373590069198612119 289060623560385103797918179)
    ·
      refine ⟨433590935340577655696877269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289060623560385103797918179 433590935340577655696877269)
      ·
        refine ⟨10162287547044788805395561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 433590935340577655696877269 10162287547044788805395561)
        ·
          refine ⟨7621715660283591604046671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10162287547044788805395561 7621715660283591604046671)
          ·
            refine ⟨11432573490425387406070007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7621715660283591604046671 11432573490425387406070007)
            ·
              refine ⟨17148860235638081109105011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11432573490425387406070007 17148860235638081109105011)
              ·
                refine ⟨25723290353457121663657517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17148860235638081109105011 25723290353457121663657517)
                ·
                  refine ⟨9646233882546420623871569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25723290353457121663657517 9646233882546420623871569)
                  ·
                    refine ⟨7234675411909815467903677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9646233882546420623871569 7234675411909815467903677)
                    ·
                      refine ⟨2713003279466180800463879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234675411909815467903677 2713003279466180800463879)
                      ·
                        rfl

theorem cell23_5283555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5283555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283555 prefixEnd_5283555 := by exact prefixLift 5283555
  have htrace : WordTrace (prefixWord ++ tailWord_5283555) baseStart_5283555 baseEnd_5283555 := by
    simpa [prefixWord, tailWord_5283555, baseEnd_5283555] using wordTrace_append hprefix tailTrace_5283555
  have hstable : (prefixWord ++ tailWord_5283555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283555).length < 2 ^ (prefixWord ++ tailWord_5283555).sum := by decide
  have hdescent : baseEnd_5283555 < baseStart_5283555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283568 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 4, 1, 3]
def baseStart_5283568 : Nat := 118140960795 + 5283568 * 2 ^ 59
def prefixEnd_5283568 : Nat := 4983230072969 + 3 ^ 40 * 5283568 * 2
def baseEnd_5283568 : Nat := 2713009954714689249601319

theorem tailTrace_5283568 : CollatzResearch.WordTrace tailWord_5283568 prefixEnd_5283568 2713009954714689249601319 := by
  unfold tailWord_5283568
  simp only [CollatzResearch.WordTrace]
  refine ⟨96353778261271486209417679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128471704348361981612556905 96353778261271486209417679)
  ·
    refine ⟨144530667391907229314126519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96353778261271486209417679 144530667391907229314126519)
    ·
      refine ⟨216796001087860843971189779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144530667391907229314126519 216796001087860843971189779)
      ·
        refine ⟨325194001631791265956784669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216796001087860843971189779 325194001631791265956784669)
        ·
          refine ⟨121947750611921724733794251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325194001631791265956784669 121947750611921724733794251)
          ·
            refine ⟨182921625917882587100691377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121947750611921724733794251 182921625917882587100691377)
            ·
              refine ⟨137191219438411940325518533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182921625917882587100691377 137191219438411940325518533)
              ·
                refine ⟨25723353644702238811034725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137191219438411940325518533 25723353644702238811034725)
                ·
                  refine ⟨4823128808381669777069011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25723353644702238811034725 4823128808381669777069011)
                  ·
                    refine ⟨7234693212572504665603517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4823128808381669777069011 7234693212572504665603517)
                    ·
                      refine ⟨2713009954714689249601319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234693212572504665603517 2713009954714689249601319)
                      ·
                        rfl

theorem cell23_5283568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_5283568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283568 prefixEnd_5283568 := by exact prefixLift 5283568
  have htrace : WordTrace (prefixWord ++ tailWord_5283568) baseStart_5283568 baseEnd_5283568 := by
    simpa [prefixWord, tailWord_5283568, baseEnd_5283568] using wordTrace_append hprefix tailTrace_5283568
  have hstable : (prefixWord ++ tailWord_5283568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283568).length < 2 ^ (prefixWord ++ tailWord_5283568).sum := by decide
  have hdescent : baseEnd_5283568 < baseStart_5283568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283572 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5283572 : Nat := 118140960795 + 5283572 * 2 ^ 59
def prefixEnd_5283572 : Nat := 4983230072969 + 3 ^ 40 * 5283572 * 2
def baseEnd_5283572 : Nat := 2713012008637307233951301

theorem tailTrace_5283572 : CollatzResearch.WordTrace tailWord_5283572 prefixEnd_5283572 2713012008637307233951301 := by
  unfold tailWord_5283572
  simp only [CollatzResearch.WordTrace]
  refine ⟨96353851207264240550990485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128471801609685654067987313 96353851207264240550990485)
  ·
    refine ⟨4516586775340511275827679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96353851207264240550990485 4516586775340511275827679)
    ·
      refine ⟨6774880163010766913741519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4516586775340511275827679 6774880163010766913741519)
      ·
        refine ⟨10162320244516150370612279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6774880163010766913741519 10162320244516150370612279)
        ·
          refine ⟨15243480366774225555918419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10162320244516150370612279 15243480366774225555918419)
          ·
            refine ⟨22865220550161338333877629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15243480366774225555918419 22865220550161338333877629)
            ·
              refine ⟨8574457706310501875204111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22865220550161338333877629 8574457706310501875204111)
              ·
                refine ⟨12861686559465752812806167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574457706310501875204111 12861686559465752812806167)
                ·
                  refine ⟨19292529839198629219209251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12861686559465752812806167 19292529839198629219209251)
                  ·
                    refine ⟨28938794758797943828813877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19292529839198629219209251 28938794758797943828813877)
                    ·
                      refine ⟨2713012008637307233951301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28938794758797943828813877 2713012008637307233951301)
                      ·
                        rfl

theorem cell23_5283572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5283572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283572 prefixEnd_5283572 := by exact prefixLift 5283572
  have htrace : WordTrace (prefixWord ++ tailWord_5283572) baseStart_5283572 baseEnd_5283572 := by
    simpa [prefixWord, tailWord_5283572, baseEnd_5283572] using wordTrace_append hprefix tailTrace_5283572
  have hstable : (prefixWord ++ tailWord_5283572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283572).length < 2 ^ (prefixWord ++ tailWord_5283572).sum := by decide
  have hdescent : baseEnd_5283572 < baseStart_5283572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283585 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_5283585 : Nat := 118140960795 + 5283585 * 2 ^ 59
def prefixEnd_5283585 : Nat := 4983230072969 + 3 ^ 40 * 5283585 * 2
def baseEnd_5283585 : Nat := 2713018683885815683088741

theorem tailTrace_5283585 : CollatzResearch.WordTrace tailWord_5283585 prefixEnd_5283585 2713018683885815683088741 := by
  unfold tailWord_5283585
  simp only [CollatzResearch.WordTrace]
  refine ⟨192708176563481384322204209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128472117708987589548136139 192708176563481384322204209)
  ·
    refine ⟨144531132422611038241653157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192708176563481384322204209 144531132422611038241653157)
    ·
      refine ⟨27099587329239569670309967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144531132422611038241653157 27099587329239569670309967)
      ·
        refine ⟨40649380993859354505464951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27099587329239569670309967 40649380993859354505464951)
        ·
          refine ⟨60974071490789031758197427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40649380993859354505464951 60974071490789031758197427)
          ·
            refine ⟨91461107236183547637296141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60974071490789031758197427 91461107236183547637296141)
            ·
              refine ⟨34297915213568830363986053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91461107236183547637296141 34297915213568830363986053)
              ·
                refine ⟨6430859102544155693247385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34297915213568830363986053 6430859102544155693247385)
                ·
                  refine ⟨4823144326908116769935539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6430859102544155693247385 4823144326908116769935539)
                  ·
                    refine ⟨7234716490362175154903309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4823144326908116769935539 7234716490362175154903309)
                    ·
                      refine ⟨2713018683885815683088741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234716490362175154903309 2713018683885815683088741)
                      ·
                        rfl

theorem cell23_5283585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_5283585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283585 prefixEnd_5283585 := by exact prefixLift 5283585
  have htrace : WordTrace (prefixWord ++ tailWord_5283585) baseStart_5283585 baseEnd_5283585 := by
    simpa [prefixWord, tailWord_5283585, baseEnd_5283585] using wordTrace_append hprefix tailTrace_5283585
  have hstable : (prefixWord ++ tailWord_5283585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283585).length < 2 ^ (prefixWord ++ tailWord_5283585).sum := by decide
  have hdescent : baseEnd_5283585 < baseStart_5283585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283602 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5283602 : Nat := 118140960795 + 5283602 * 2 ^ 59
def prefixEnd_5283602 : Nat := 4983230072969 + 3 ^ 40 * 5283602 * 2
def baseEnd_5283602 : Nat := 2713027413056942116576163

theorem tailTrace_5283602 : CollatzResearch.WordTrace tailWord_5283602 prefixEnd_5283602 2713027413056942116576163 := by
  unfold tailWord_5283602
  simp only [CollatzResearch.WordTrace]
  refine ⟨48177199151104949056393265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128472531069613197483715373 48177199151104949056393265)
  ·
    refine ⟨36132899363328711792294949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48177199151104949056393265 36132899363328711792294949)
    ·
      refine ⟨6774918630624133461055303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36132899363328711792294949 6774918630624133461055303)
      ·
        refine ⟨10162377945936200191582955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6774918630624133461055303 10162377945936200191582955)
        ·
          refine ⟨15243566918904300287374433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10162377945936200191582955 15243566918904300287374433)
          ·
            refine ⟨11432675189178225215530825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15243566918904300287374433 11432675189178225215530825)
            ·
              refine ⟨8574506391883668911648119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11432675189178225215530825 8574506391883668911648119)
              ·
                refine ⟨12861759587825503367472179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574506391883668911648119 12861759587825503367472179)
                ·
                  refine ⟨19292639381738255051208269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12861759587825503367472179 19292639381738255051208269)
                  ·
                    refine ⟨7234739768151845644203101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19292639381738255051208269 7234739768151845644203101)
                    ·
                      refine ⟨2713027413056942116576163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234739768151845644203101 2713027413056942116576163)
                      ·
                        rfl

theorem cell23_5283602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5283602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283602 prefixEnd_5283602 := by exact prefixLift 5283602
  have htrace : WordTrace (prefixWord ++ tailWord_5283602) baseStart_5283602 baseEnd_5283602 := by
    simpa [prefixWord, tailWord_5283602, baseEnd_5283602] using wordTrace_append hprefix tailTrace_5283602
  have hstable : (prefixWord ++ tailWord_5283602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283602).length < 2 ^ (prefixWord ++ tailWord_5283602).sum := by decide
  have hdescent : baseEnd_5283602 < baseStart_5283602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283642 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2]
def baseStart_5283642 : Nat := 118140960795 + 5283642 * 2 ^ 59
def prefixEnd_5283642 : Nat := 4983230072969 + 3 ^ 40 * 5283642 * 2
def baseEnd_5283642 : Nat := 2713047952283121960075979

theorem tailTrace_5283642 : CollatzResearch.WordTrace tailWord_5283642 prefixEnd_5283642 2713047952283121960075979 := by
  unfold tailWord_5283642
  simp only [CollatzResearch.WordTrace]
  refine ⟨48177563881068720764257295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128473503682849922038019453 48177563881068720764257295)
  ·
    refine ⟨72266345821603081146385943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48177563881068720764257295 72266345821603081146385943)
    ·
      refine ⟨108399518732404621719578915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72266345821603081146385943 108399518732404621719578915)
      ·
        refine ⟨162599278098606932579368373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108399518732404621719578915 162599278098606932579368373)
        ·
          refine ⟨15243682321744399929315785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 162599278098606932579368373 15243682321744399929315785)
          ·
            refine ⟨11432761741308299946986839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15243682321744399929315785 11432761741308299946986839)
            ·
              refine ⟨17149142611962449920480259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11432761741308299946986839 17149142611962449920480259)
              ·
                refine ⟨25723713917943674880720389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17149142611962449920480259 25723713917943674880720389)
                ·
                  refine ⟨4823196359614439040135073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25723713917943674880720389 4823196359614439040135073)
                  ·
                    refine ⟨3617397269710829280101305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4823196359614439040135073 3617397269710829280101305)
                    ·
                      refine ⟨2713047952283121960075979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617397269710829280101305 2713047952283121960075979)
                      ·
                        rfl

theorem cell23_5283642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_5283642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283642 prefixEnd_5283642 := by exact prefixLift 5283642
  have htrace : WordTrace (prefixWord ++ tailWord_5283642) baseStart_5283642 baseEnd_5283642 := by
    simpa [prefixWord, tailWord_5283642, baseEnd_5283642] using wordTrace_append hprefix tailTrace_5283642
  have hstable : (prefixWord ++ tailWord_5283642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283642).length < 2 ^ (prefixWord ++ tailWord_5283642).sum := by decide
  have hdescent : baseEnd_5283642 < baseStart_5283642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283658 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_5283658 : Nat := 118140960795 + 5283658 * 2 ^ 59
def prefixEnd_5283658 : Nat := 4983230072969 + 3 ^ 40 * 5283658 * 2
def baseEnd_5283658 : Nat := 2713056167973593897475905

theorem tailTrace_5283658 : CollatzResearch.WordTrace tailWord_5283658 prefixEnd_5283658 2713056167973593897475905 := by
  unfold tailWord_5283658
  simp only [CollatzResearch.WordTrace]
  refine ⟨48177709773054229447402907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128473892728144611859741085 48177709773054229447402907)
  ·
    refine ⟨72266564659581344171104361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48177709773054229447402907 72266564659581344171104361)
    ·
      refine ⟨54199923494686008128328271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72266564659581344171104361 54199923494686008128328271)
      ·
        refine ⟨81299885242029012192492407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54199923494686008128328271 81299885242029012192492407)
        ·
          refine ⟨121949827863043518288738611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81299885242029012192492407 121949827863043518288738611)
          ·
            refine ⟨182924741794565277433107917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121949827863043518288738611 182924741794565277433107917)
            ·
              refine ⟨68596778172961979037415469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182924741794565277433107917 68596778172961979037415469)
              ·
                refine ⟨25723791814860742139030801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68596778172961979037415469 25723791814860742139030801)
                ·
                  refine ⟨19292843861145556604273101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25723791814860742139030801 19292843861145556604273101)
                  ·
                    refine ⟨7234816447929583726602413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19292843861145556604273101 7234816447929583726602413)
                    ·
                      refine ⟨2713056167973593897475905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234816447929583726602413 2713056167973593897475905)
                      ·
                        rfl

theorem cell23_5283658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_5283658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283658 prefixEnd_5283658 := by exact prefixLift 5283658
  have htrace : WordTrace (prefixWord ++ tailWord_5283658) baseStart_5283658 baseEnd_5283658 := by
    simpa [prefixWord, tailWord_5283658, baseEnd_5283658] using wordTrace_append hprefix tailTrace_5283658
  have hstable : (prefixWord ++ tailWord_5283658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283658).length < 2 ^ (prefixWord ++ tailWord_5283658).sum := by decide
  have hdescent : baseEnd_5283658 < baseStart_5283658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283682 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 5]
def baseStart_5283682 : Nat := 118140960795 + 5283682 * 2 ^ 59
def prefixEnd_5283682 : Nat := 4983230072969 + 3 ^ 40 * 5283682 * 2
def baseEnd_5283682 : Nat := 301452054612144644841755

theorem tailTrace_5283682 : CollatzResearch.WordTrace tailWord_5283682 prefixEnd_5283682 301452054612144644841755 := by
  unfold tailWord_5283682
  simp only [CollatzResearch.WordTrace]
  refine ⟨48177928611032492472121325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128474476296086646592323533 48177928611032492472121325)
  ·
    refine ⟨18066723229137184677045497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48177928611032492472121325 18066723229137184677045497)
    ·
      refine ⟨13550042421852888507784123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18066723229137184677045497 13550042421852888507784123)
      ·
        refine ⟨20325063632779332761676185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13550042421852888507784123 20325063632779332761676185)
        ·
          refine ⟨15243797724584499571257139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20325063632779332761676185 15243797724584499571257139)
          ·
            refine ⟨22865696586876749356885709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15243797724584499571257139 22865696586876749356885709)
            ·
              refine ⟨8574636220078781008832141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22865696586876749356885709 8574636220078781008832141)
              ·
                refine ⟨3215488582529542878312053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8574636220078781008832141 3215488582529542878312053)
                ·
                  refine ⟨301452054612144644841755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3215488582529542878312053 301452054612144644841755)
                  ·
                    rfl

theorem cell23_5283682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_5283682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283682 prefixEnd_5283682 := by exact prefixLift 5283682
  have htrace : WordTrace (prefixWord ++ tailWord_5283682) baseStart_5283682 baseEnd_5283682 := by
    simpa [prefixWord, tailWord_5283682, baseEnd_5283682] using wordTrace_append hprefix tailTrace_5283682
  have hstable : (prefixWord ++ tailWord_5283682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283682).length < 2 ^ (prefixWord ++ tailWord_5283682).sum := by decide
  have hdescent : baseEnd_5283682 < baseStart_5283682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283688 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5283688 : Nat := 118140960795 + 5283688 * 2 ^ 59
def prefixEnd_5283688 : Nat := 4983230072969 + 3 ^ 40 * 5283688 * 2
def baseEnd_5283688 : Nat := 2713071572393228780100767

theorem tailTrace_5283688 : CollatzResearch.WordTrace tailWord_5283688 prefixEnd_5283688 2713071572393228780100767 := by
  unfold tailWord_5283688
  simp only [CollatzResearch.WordTrace]
  refine ⟨96355966641054116456601859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128474622188072155275469145 96355966641054116456601859)
  ·
    refine ⟨144533949961581174684902789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96355966641054116456601859 144533949961581174684902789)
    ·
      refine ⟨27100115617796470253419273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144533949961581174684902789 27100115617796470253419273)
      ·
        refine ⟨20325086713347352690064455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27100115617796470253419273 20325086713347352690064455)
        ·
          refine ⟨30487630070021029035096683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20325086713347352690064455 30487630070021029035096683)
          ·
            refine ⟨45731445105031543552645025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30487630070021029035096683 45731445105031543552645025)
            ·
              refine ⟨34298583828773657664483769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45731445105031543552645025 34298583828773657664483769)
              ·
                refine ⟨25723937871580243248362827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34298583828773657664483769 25723937871580243248362827)
                ·
                  refine ⟨38585906807370364872544241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25723937871580243248362827 38585906807370364872544241)
                  ·
                    refine ⟨28939430105527773654408181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38585906807370364872544241 28939430105527773654408181)
                    ·
                      refine ⟨2713071572393228780100767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28939430105527773654408181 2713071572393228780100767)
                      ·
                        rfl

theorem cell23_5283688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5283688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283688 prefixEnd_5283688 := by exact prefixLift 5283688
  have htrace : WordTrace (prefixWord ++ tailWord_5283688) baseStart_5283688 baseEnd_5283688 := by
    simpa [prefixWord, tailWord_5283688, baseEnd_5283688] using wordTrace_append hprefix tailTrace_5283688
  have hstable : (prefixWord ++ tailWord_5283688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283688).length < 2 ^ (prefixWord ++ tailWord_5283688).sum := by decide
  have hdescent : baseEnd_5283688 < baseStart_5283688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283732 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_5283732 : Nat := 118140960795 + 5283732 * 2 ^ 59
def prefixEnd_5283732 : Nat := 4983230072969 + 3 ^ 40 * 5283732 * 2
def baseEnd_5283732 : Nat := 2713094165542026607950565

theorem tailTrace_5283732 : CollatzResearch.WordTrace tailWord_5283732 prefixEnd_5283732 2713094165542026607950565 := by
  unfold tailWord_5283732
  simp only [CollatzResearch.WordTrace]
  refine ⟨96356769046974414213902725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128475692062632552285203633 96356769046974414213902725)
  ·
    refine ⟨18066894196307702665106761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96356769046974414213902725 18066894196307702665106761)
    ·
      refine ⟨13550170647230776998830071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18066894196307702665106761 13550170647230776998830071)
      ·
        refine ⟨20325255970846165498245107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13550170647230776998830071 20325255970846165498245107)
        ·
          refine ⟨30487883956269248247367661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20325255970846165498245107 30487883956269248247367661)
          ·
            refine ⟨11432956483600968092762873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30487883956269248247367661 11432956483600968092762873)
            ·
              refine ⟨8574717362700726069572155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11432956483600968092762873 8574717362700726069572155)
              ·
                refine ⟨12862076044051089104358233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574717362700726069572155 12862076044051089104358233)
                ·
                  refine ⟨9646557033038316828268675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12862076044051089104358233 9646557033038316828268675)
                  ·
                    refine ⟨14469835549557475242403013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9646557033038316828268675 14469835549557475242403013)
                    ·
                      refine ⟨2713094165542026607950565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14469835549557475242403013 2713094165542026607950565)
                      ·
                        rfl

theorem cell23_5283732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_5283732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283732 prefixEnd_5283732 := by exact prefixLift 5283732
  have htrace : WordTrace (prefixWord ++ tailWord_5283732) baseStart_5283732 baseEnd_5283732 := by
    simpa [prefixWord, tailWord_5283732, baseEnd_5283732] using wordTrace_append hprefix tailTrace_5283732
  have hstable : (prefixWord ++ tailWord_5283732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283732).length < 2 ^ (prefixWord ++ tailWord_5283732).sum := by decide
  have hdescent : baseEnd_5283732 < baseStart_5283732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283735 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_5283735 : Nat := 118140960795 + 5283735 * 2 ^ 59
def prefixEnd_5283735 : Nat := 4983230072969 + 3 ^ 40 * 5283735 * 2
def baseEnd_5283735 : Nat := 2713095705983990096213051

theorem tailTrace_5283735 : CollatzResearch.WordTrace tailWord_5283735 prefixEnd_5283735 2713095705983990096213051 := by
  unfold tailWord_5283735
  simp only [CollatzResearch.WordTrace]
  refine ⟨192713647512937959940164659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128475765008625306626776439 192713647512937959940164659)
  ·
    refine ⟨289070471269406939910246989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192713647512937959940164659 289070471269406939910246989)
    ·
      refine ⟨108401426726027602466342621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289070471269406939910246989 108401426726027602466342621)
      ·
        refine ⟨40650535022260350924878483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108401426726027602466342621 40650535022260350924878483)
        ·
          refine ⟨60975802533390526387317725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40650535022260350924878483 60975802533390526387317725)
          ·
            refine ⟨22865925950021447395244147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60975802533390526387317725 22865925950021447395244147)
            ·
              refine ⟨34298888925032171092866221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22865925950021447395244147 34298888925032171092866221)
              ·
                refine ⟨12862083346887064159824833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34298888925032171092866221 12862083346887064159824833)
                ·
                  refine ⟨9646562510165298119868625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12862083346887064159824833 9646562510165298119868625)
                  ·
                    refine ⟨7234921882623973589901469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9646562510165298119868625 7234921882623973589901469)
                    ·
                      refine ⟨2713095705983990096213051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7234921882623973589901469 2713095705983990096213051)
                      ·
                        rfl

theorem cell23_5283735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_5283735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283735 prefixEnd_5283735 := by exact prefixLift 5283735
  have htrace : WordTrace (prefixWord ++ tailWord_5283735) baseStart_5283735 baseEnd_5283735 := by
    simpa [prefixWord, tailWord_5283735, baseEnd_5283735] using wordTrace_append hprefix tailTrace_5283735
  have hstable : (prefixWord ++ tailWord_5283735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283735).length < 2 ^ (prefixWord ++ tailWord_5283735).sum := by decide
  have hdescent : baseEnd_5283735 < baseStart_5283735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283768 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_5283768 : Nat := 118140960795 + 5283768 * 2 ^ 59
def prefixEnd_5283768 : Nat := 4983230072969 + 3 ^ 40 * 5283768 * 2
def baseEnd_5283768 : Nat := 904370883615196155700133

theorem tailTrace_5283768 : CollatzResearch.WordTrace tailWord_5283768 prefixEnd_5283768 904370883615196155700133 := by
  unfold tailWord_5283768
  simp only [CollatzResearch.WordTrace]
  refine ⟨96357425560909203288057979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128476567414545604384077305 96357425560909203288057979)
  ·
    refine ⟨144536138341363804932086969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96357425560909203288057979 144536138341363804932086969)
    ·
      refine ⟨108402103756022853699065227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144536138341363804932086969 108402103756022853699065227)
      ·
        refine ⟨162603155634034280548597841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108402103756022853699065227 162603155634034280548597841)
        ·
          refine ⟨121952366725525710411448381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162603155634034280548597841 121952366725525710411448381)
          ·
            refine ⟨45732137522072141404293143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121952366725525710411448381 45732137522072141404293143)
            ·
              refine ⟨68598206283108212106439715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45732137522072141404293143 68598206283108212106439715)
              ·
                refine ⟨102897309424662318159659573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68598206283108212106439715 102897309424662318159659573)
                ·
                  refine ⟨9646622758562092327468085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102897309424662318159659573 9646622758562092327468085)
                  ·
                    refine ⟨904370883615196155700133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9646622758562092327468085 904370883615196155700133)
                    ·
                      rfl

theorem cell23_5283768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_5283768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283768 prefixEnd_5283768 := by exact prefixLift 5283768
  have htrace : WordTrace (prefixWord ++ tailWord_5283768) baseStart_5283768 baseEnd_5283768 := by
    simpa [prefixWord, tailWord_5283768, baseEnd_5283768] using wordTrace_append hprefix tailTrace_5283768
  have hstable : (prefixWord ++ tailWord_5283768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283768).length < 2 ^ (prefixWord ++ tailWord_5283768).sum := by decide
  have hdescent : baseEnd_5283768 < baseStart_5283768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283775 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 1, 5, 2]
def baseStart_5283775 : Nat := 118140960795 + 5283775 * 2 ^ 59
def prefixEnd_5283775 : Nat := 4983230072969 + 3 ^ 40 * 5283775 * 2
def baseEnd_5283775 : Nat := 2713116245210169939712867

theorem tailTrace_5283775 : CollatzResearch.WordTrace tailWord_5283775 prefixEnd_5283775 2713116245210169939712867 := by
  unfold tailWord_5283775
  simp only [CollatzResearch.WordTrace]
  refine ⟨192715106432793046771620779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128476737621862031181080519 192715106432793046771620779)
  ·
    refine ⟨289072659649189570157431169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192715106432793046771620779 289072659649189570157431169)
    ·
      refine ⟨216804494736892177618073377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289072659649189570157431169 216804494736892177618073377)
      ·
        refine ⟨162603371052669133213555033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216804494736892177618073377 162603371052669133213555033)
        ·
          refine ⟨121952528289501849910166275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162603371052669133213555033 121952528289501849910166275)
          ·
            refine ⟨182928792434252774865249413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121952528289501849910166275 182928792434252774865249413)
            ·
              refine ⟨34299148581422395287234265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182928792434252774865249413 34299148581422395287234265)
              ·
                refine ⟨25724361436066796465425699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34299148581422395287234265 25724361436066796465425699)
                ·
                  refine ⟨38586542154100194698138549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25724361436066796465425699 38586542154100194698138549)
                  ·
                    refine ⟨3617488326946893252950489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38586542154100194698138549 3617488326946893252950489)
                    ·
                      refine ⟨2713116245210169939712867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617488326946893252950489 2713116245210169939712867)
                      ·
                        rfl

theorem cell23_5283775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5, 2].length) (baseStart_5283775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283775 prefixEnd_5283775 := by exact prefixLift 5283775
  have htrace : WordTrace (prefixWord ++ tailWord_5283775) baseStart_5283775 baseEnd_5283775 := by
    simpa [prefixWord, tailWord_5283775, baseEnd_5283775] using wordTrace_append hprefix tailTrace_5283775
  have hstable : (prefixWord ++ tailWord_5283775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283775).length < 2 ^ (prefixWord ++ tailWord_5283775).sum := by decide
  have hdescent : baseEnd_5283775 < baseStart_5283775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283792 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 2, 3, 2]
def baseStart_5283792 : Nat := 118140960795 + 5283792 * 2 ^ 59
def prefixEnd_5283792 : Nat := 4983230072969 + 3 ^ 40 * 5283792 * 2
def baseEnd_5283792 : Nat := 2713124974381296373200289

theorem tailTrace_5283792 : CollatzResearch.WordTrace tailWord_5283792 prefixEnd_5283792 2713124974381296373200289 := by
  unfold tailWord_5283792
  simp only [CollatzResearch.WordTrace]
  refine ⟨96357863236865729337494815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128477150982487639116659753 96357863236865729337494815)
  ·
    refine ⟨144536794855298594006242223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96357863236865729337494815 144536794855298594006242223)
    ·
      refine ⟨216805192282947891009363335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144536794855298594006242223 216805192282947891009363335)
      ·
        refine ⟨325207788424421836514045003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216805192282947891009363335 325207788424421836514045003)
        ·
          refine ⟨487811682636632754771067505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325207788424421836514045003 487811682636632754771067505)
          ·
            refine ⟨365858761977474566078300629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487811682636632754771067505 365858761977474566078300629)
            ·
              refine ⟨8574814733847060142460171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 365858761977474566078300629 8574814733847060142460171)
              ·
                refine ⟨12862222100770590213690257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574814733847060142460171 12862222100770590213690257)
                ·
                  refine ⟨9646666575577942660267693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12862222100770590213690257 9646666575577942660267693)
                  ·
                    refine ⟨3617499965841728497600385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9646666575577942660267693 3617499965841728497600385)
                    ·
                      refine ⟨2713124974381296373200289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617499965841728497600385 2713124974381296373200289)
                      ·
                        rfl

theorem cell23_5283792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 3, 2].length) (baseStart_5283792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283792 prefixEnd_5283792 := by exact prefixLift 5283792
  have htrace : WordTrace (prefixWord ++ tailWord_5283792) baseStart_5283792 baseEnd_5283792 := by
    simpa [prefixWord, tailWord_5283792, baseEnd_5283792] using wordTrace_append hprefix tailTrace_5283792
  have hstable : (prefixWord ++ tailWord_5283792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283792).length < 2 ^ (prefixWord ++ tailWord_5283792).sum := by decide
  have hdescent : baseEnd_5283792 < baseStart_5283792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283799 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 1, 1, 3]
def baseStart_5283799 : Nat := 118140960795 + 5283799 * 2 ^ 59
def prefixEnd_5283799 : Nat := 4983230072969 + 3 ^ 40 * 5283799 * 2
def baseEnd_5283799 : Nat := 2713128568745877845812757

theorem tailTrace_5283799 : CollatzResearch.WordTrace tailWord_5283799 prefixEnd_5283799 2713128568745877845812757 := by
  unfold tailWord_5283799
  simp only [CollatzResearch.WordTrace]
  refine ⟨192715981784706098870494451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128477321189804065913662967 192715981784706098870494451)
  ·
    refine ⟨289073972677059148305741677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192715981784706098870494451 289073972677059148305741677)
    ·
      refine ⟨108402739753897180614653129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289073972677059148305741677 108402739753897180614653129)
      ·
        refine ⟨81302054815422885460989847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108402739753897180614653129 81302054815422885460989847)
        ·
          refine ⟨121953082223134328191484771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81302054815422885460989847 121953082223134328191484771)
          ·
            refine ⟨182929623334701492287227157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121953082223134328191484771 182929623334701492287227157)
            ·
              refine ⟨8574826093814132450963773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182929623334701492287227157 8574826093814132450963773)
              ·
                refine ⟨3215559785180299669111415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8574826093814132450963773 3215559785180299669111415)
                ·
                  refine ⟨4823339677770449503667123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215559785180299669111415 4823339677770449503667123)
                  ·
                    refine ⟨7235009516655674255500685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4823339677770449503667123 7235009516655674255500685)
                    ·
                      refine ⟨2713128568745877845812757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7235009516655674255500685 2713128568745877845812757)
                      ·
                        rfl

theorem cell23_5283799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_5283799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283799 prefixEnd_5283799 := by exact prefixLift 5283799
  have htrace : WordTrace (prefixWord ++ tailWord_5283799) baseStart_5283799 baseEnd_5283799 := by
    simpa [prefixWord, tailWord_5283799, baseEnd_5283799] using wordTrace_append hprefix tailTrace_5283799
  have hstable : (prefixWord ++ tailWord_5283799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283799).length < 2 ^ (prefixWord ++ tailWord_5283799).sum := by decide
  have hdescent : baseEnd_5283799 < baseStart_5283799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283802 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 1, 5]
def baseStart_5283802 : Nat := 118140960795 + 5283802 * 2 ^ 59
def prefixEnd_5283802 : Nat := 4983230072969 + 3 ^ 40 * 5283802 * 2
def baseEnd_5283802 : Nat := 904376703062613778025081

theorem tailTrace_5283802 : CollatzResearch.WordTrace tailWord_5283802 prefixEnd_5283802 904376703062613778025081 := by
  unfold tailWord_5283802
  simp only [CollatzResearch.WordTrace]
  refine ⟨48179022800923807595713415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128477394135796820255235773 48179022800923807595713415)
  ·
    refine ⟨72268534201385711393570123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48179022800923807595713415 72268534201385711393570123)
    ·
      refine ⟨108402801302078567090355185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72268534201385711393570123 108402801302078567090355185)
      ·
        refine ⟨81302100976558925317766389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108402801302078567090355185 81302100976558925317766389)
        ·
          refine ⟨7622071966552399248540599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81302100976558925317766389 7622071966552399248540599)
          ·
            refine ⟨11433107949828598872810899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7622071966552399248540599 11433107949828598872810899)
            ·
              refine ⟨17149661924742898309216349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11433107949828598872810899 17149661924742898309216349)
              ·
                refine ⟨6431123221778586865956131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17149661924742898309216349 6431123221778586865956131)
                ·
                  refine ⟨9646684832667880298934197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6431123221778586865956131 9646684832667880298934197)
                  ·
                    refine ⟨904376703062613778025081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9646684832667880298934197 904376703062613778025081)
                    ·
                      rfl

theorem cell23_5283802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_5283802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283802 prefixEnd_5283802 := by exact prefixLift 5283802
  have htrace : WordTrace (prefixWord ++ tailWord_5283802) baseStart_5283802 baseEnd_5283802 := by
    simpa [prefixWord, tailWord_5283802, baseEnd_5283802] using wordTrace_append hprefix tailTrace_5283802
  have hstable : (prefixWord ++ tailWord_5283802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283802).length < 2 ^ (prefixWord ++ tailWord_5283802).sum := by decide
  have hdescent : baseEnd_5283802 < baseStart_5283802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283808 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_5283808 : Nat := 118140960795 + 5283808 * 2 ^ 59
def prefixEnd_5283808 : Nat := 4983230072969 + 3 ^ 40 * 5283808 * 2
def baseEnd_5283808 : Nat := 2713133190071768310600215

theorem tailTrace_5283808 : CollatzResearch.WordTrace tailWord_5283808 prefixEnd_5283808 2713133190071768310600215 := by
  unfold tailWord_5283808
  simp only [CollatzResearch.WordTrace]
  refine ⟨96358155020836746703786039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128477540027782328938381385 96358155020836746703786039)
  ·
    refine ⟨144537232531255120055679059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96358155020836746703786039 144537232531255120055679059)
    ·
      refine ⟨216805848796882680083518589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144537232531255120055679059 216805848796882680083518589)
      ·
        refine ⟨81302193298831005031319471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216805848796882680083518589 81302193298831005031319471)
        ·
          refine ⟨121953289948246507546979207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81302193298831005031319471 121953289948246507546979207)
          ·
            refine ⟨182929934922369761320468811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121953289948246507546979207 182929934922369761320468811)
            ·
              refine ⟨274394902383554641980703217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182929934922369761320468811 274394902383554641980703217)
              ·
                refine ⟨205796176787665981485527413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274394902383554641980703217 205796176787665981485527413)
                ·
                  refine ⟨19293391573843685764268195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205796176787665981485527413 19293391573843685764268195)
                  ·
                    refine ⟨28940087360765528646402293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19293391573843685764268195 28940087360765528646402293)
                    ·
                      refine ⟨2713133190071768310600215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28940087360765528646402293 2713133190071768310600215)
                      ·
                        rfl

theorem cell23_5283808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_5283808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283808 prefixEnd_5283808 := by exact prefixLift 5283808
  have htrace : WordTrace (prefixWord ++ tailWord_5283808) baseStart_5283808 baseEnd_5283808 := by
    simpa [prefixWord, tailWord_5283808, baseEnd_5283808] using wordTrace_append hprefix tailTrace_5283808
  have hstable : (prefixWord ++ tailWord_5283808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283808).length < 2 ^ (prefixWord ++ tailWord_5283808).sum := by decide
  have hdescent : baseEnd_5283808 < baseStart_5283808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283835 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 4]
def baseStart_5283835 : Nat := 118140960795 + 5283835 * 2 ^ 59
def prefixEnd_5283835 : Nat := 4983230072969 + 3 ^ 40 * 5283835 * 2
def baseEnd_5283835 : Nat := 2713147054049439704962591

theorem tailTrace_5283835 : CollatzResearch.WordTrace tailWord_5283835 prefixEnd_5283835 2713147054049439704962591 := by
  unfold tailWord_5283835
  simp only [CollatzResearch.WordTrace]
  refine ⟨192717294812575677018804959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128478196541717118012536639 192717294812575677018804959)
  ·
    refine ⟨289075942218863515528207439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192717294812575677018804959 289075942218863515528207439)
    ·
      refine ⟨433613913328295273292311159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289075942218863515528207439 433613913328295273292311159)
      ·
        refine ⟨650420869992442909938466739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433613913328295273292311159 650420869992442909938466739)
        ·
          refine ⟨975631304988664364907700109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650420869992442909938466739 975631304988664364907700109)
          ·
            refine ⟨365861739370749136840387541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 975631304988664364907700109 365861739370749136840387541)
            ·
              refine ⟨8574884516501932894696583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 365861739370749136840387541 8574884516501932894696583)
              ·
                refine ⟨12862326774752899342044875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574884516501932894696583 12862326774752899342044875)
                ·
                  refine ⟨19293490162129349013067313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12862326774752899342044875 19293490162129349013067313)
                  ·
                    refine ⟨14470117621597011759800485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19293490162129349013067313 14470117621597011759800485)
                    ·
                      refine ⟨2713147054049439704962591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14470117621597011759800485 2713147054049439704962591)
                      ·
                        rfl

theorem cell23_5283835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 4].length) (baseStart_5283835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283835 prefixEnd_5283835 := by exact prefixLift 5283835
  have htrace : WordTrace (prefixWord ++ tailWord_5283835) baseStart_5283835 baseEnd_5283835 := by
    simpa [prefixWord, tailWord_5283835, baseEnd_5283835] using wordTrace_append hprefix tailTrace_5283835
  have hstable : (prefixWord ++ tailWord_5283835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283835).length < 2 ^ (prefixWord ++ tailWord_5283835).sum := by decide
  have hdescent : baseEnd_5283835 < baseStart_5283835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283845 : List Nat := [1, 3, 1, 1, 2, 4, 4, 7]
def baseStart_5283845 : Nat := 118140960795 + 5283845 * 2 ^ 59
def prefixEnd_5283845 : Nat := 4983230072969 + 3 ^ 40 * 5283845 * 2
def baseEnd_5283845 : Nat := 100487118105777209845835

theorem tailTrace_5283845 : CollatzResearch.WordTrace tailWord_5283845 prefixEnd_5283845 100487118105777209845835 := by
  unfold tailWord_5283845
  simp only [CollatzResearch.WordTrace]
  refine ⟨192717659542539448726668989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128478439695026299151112659 192717659542539448726668989)
  ·
    refine ⟨72269122328452293272500871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192717659542539448726668989 72269122328452293272500871)
    ·
      refine ⟨108403683492678439908751307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72269122328452293272500871 108403683492678439908751307)
      ·
        refine ⟨162605525239017659863126961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108403683492678439908751307 162605525239017659863126961)
        ·
          refine ⟨121954143929263244897345221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162605525239017659863126961 121954143929263244897345221)
          ·
            refine ⟨22866401986736858418252229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121954143929263244897345221 22866401986736858418252229)
            ·
              refine ⟨4287450372513160953422293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22866401986736858418252229 4287450372513160953422293)
              ·
                refine ⟨100487118105777209845835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4287450372513160953422293 100487118105777209845835)
                ·
                  rfl

theorem cell23_5283845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 7].length) (baseStart_5283845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283845 prefixEnd_5283845 := by exact prefixLift 5283845
  have htrace : WordTrace (prefixWord ++ tailWord_5283845) baseStart_5283845 baseEnd_5283845 := by
    simpa [prefixWord, tailWord_5283845, baseEnd_5283845] using wordTrace_append hprefix tailTrace_5283845
  have hstable : (prefixWord ++ tailWord_5283845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283845).length < 2 ^ (prefixWord ++ tailWord_5283845).sum := by decide
  have hdescent : baseEnd_5283845 < baseStart_5283845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283873 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_5283873 : Nat := 118140960795 + 5283873 * 2 ^ 59
def prefixEnd_5283873 : Nat := 4983230072969 + 3 ^ 40 * 5283873 * 2
def baseEnd_5283873 : Nat := 2713166566314310556287417

theorem tailTrace_5283873 : CollatzResearch.WordTrace tailWord_5283873 prefixEnd_5283873 2713166566314310556287417 := by
  unfold tailWord_5283873
  simp only [CollatzResearch.WordTrace]
  refine ⟨192718680786438009508688273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128479120524292006339125515 192718680786438009508688273)
  ·
    refine ⟨144539010589828507131516205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192718680786438009508688273 144539010589828507131516205)
    ·
      refine ⟨54202128971185690174318577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144539010589828507131516205 54202128971185690174318577)
      ·
        refine ⟨40651596728389267630738933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54202128971185690174318577 40651596728389267630738933)
        ·
          refine ⟨3811087193286493840381775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40651596728389267630738933 3811087193286493840381775)
          ·
            refine ⟨5716630789929740760572663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811087193286493840381775 5716630789929740760572663)
            ·
              refine ⟨8574946184894611140858995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716630789929740760572663 8574946184894611140858995)
              ·
                refine ⟨12862419277341916711288493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8574946184894611140858995 12862419277341916711288493)
                ·
                  refine ⟨4823407229003218766733185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12862419277341916711288493 4823407229003218766733185)
                  ·
                    refine ⟨3617555421752414075049889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4823407229003218766733185 3617555421752414075049889)
                    ·
                      refine ⟨2713166566314310556287417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617555421752414075049889 2713166566314310556287417)
                      ·
                        rfl

theorem cell23_5283873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_5283873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283873 prefixEnd_5283873 := by exact prefixLift 5283873
  have htrace : WordTrace (prefixWord ++ tailWord_5283873) baseStart_5283873 baseEnd_5283873 := by
    simpa [prefixWord, tailWord_5283873, baseEnd_5283873] using wordTrace_append hprefix tailTrace_5283873
  have hstable : (prefixWord ++ tailWord_5283873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283873).length < 2 ^ (prefixWord ++ tailWord_5283873).sum := by decide
  have hdescent : baseEnd_5283873 < baseStart_5283873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283889 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_5283889 : Nat := 118140960795 + 5283889 * 2 ^ 59
def prefixEnd_5283889 : Nat := 4983230072969 + 3 ^ 40 * 5283889 * 2
def baseEnd_5283889 : Nat := 2713174782004782493687343

theorem tailTrace_5283889 : CollatzResearch.WordTrace tailWord_5283889 prefixEnd_5283889 2713174782004782493687343 := by
  unfold tailWord_5283889
  simp only [CollatzResearch.WordTrace]
  refine ⟨192719264354380044241270721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128479509569586696160847147 192719264354380044241270721)
  ·
    refine ⟨144539448265785033180953041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192719264354380044241270721 144539448265785033180953041)
    ·
      refine ⟨108404586199338774885714781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144539448265785033180953041 108404586199338774885714781)
      ·
        refine ⟨40651719824752040582143043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108404586199338774885714781 40651719824752040582143043)
        ·
          refine ⟨60977579737128060873214565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40651719824752040582143043 60977579737128060873214565)
          ·
            refine ⟨11433296200711511413727731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60977579737128060873214565 11433296200711511413727731)
            ·
              refine ⟨17149944301067267120591597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11433296200711511413727731 17149944301067267120591597)
              ·
                refine ⟨6431229112900225170221849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17149944301067267120591597 6431229112900225170221849)
                ·
                  refine ⟨4823421834675168877666387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6431229112900225170221849 4823421834675168877666387)
                  ·
                    refine ⟨7235132752012753316499581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4823421834675168877666387 7235132752012753316499581)
                    ·
                      refine ⟨2713174782004782493687343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7235132752012753316499581 2713174782004782493687343)
                      ·
                        rfl

theorem cell23_5283889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_5283889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283889 prefixEnd_5283889 := by exact prefixLift 5283889
  have htrace : WordTrace (prefixWord ++ tailWord_5283889) baseStart_5283889 baseEnd_5283889 := by
    simpa [prefixWord, tailWord_5283889, baseEnd_5283889] using wordTrace_append hprefix tailTrace_5283889
  have hstable : (prefixWord ++ tailWord_5283889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283889).length < 2 ^ (prefixWord ++ tailWord_5283889).sum := by decide
  have hdescent : baseEnd_5283889 < baseStart_5283889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283932 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_5283932 : Nat := 118140960795 + 5283932 * 2 ^ 59
def prefixEnd_5283932 : Nat := 4983230072969 + 3 ^ 40 * 5283932 * 2
def baseEnd_5283932 : Nat := 2713196861672925825449645

theorem tailTrace_5283932 : CollatzResearch.WordTrace tailWord_5283932 prefixEnd_5283932 2713196861672925825449645 := by
  unfold tailWord_5283932
  simp only [CollatzResearch.WordTrace]
  refine ⟨96360416346612131292543025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128480555128816175056724033 96360416346612131292543025)
  ·
    refine ⟨72270312259959098469407269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96360416346612131292543025 72270312259959098469407269)
    ·
      refine ⟨13550683548742330963013863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72270312259959098469407269 13550683548742330963013863)
      ·
        refine ⟨20326025323113496444520795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13550683548742330963013863 20326025323113496444520795)
        ·
          refine ⟨30489037984670244666781193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20326025323113496444520795 30489037984670244666781193)
          ·
            refine ⟨22866778488502683500085895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30489037984670244666781193 22866778488502683500085895)
            ·
              refine ⟨34300167732754025250128843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22866778488502683500085895 34300167732754025250128843)
              ·
                refine ⟨51450251599131037875193265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34300167732754025250128843 51450251599131037875193265)
                ·
                  refine ⟨38587688699348278406394949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51450251599131037875193265 38587688699348278406394949)
                  ·
                    refine ⟨7235191631127802201199053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38587688699348278406394949 7235191631127802201199053)
                    ·
                      refine ⟨2713196861672925825449645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7235191631127802201199053 2713196861672925825449645)
                      ·
                        rfl

theorem cell23_5283932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_5283932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283932 prefixEnd_5283932 := by exact prefixLift 5283932
  have htrace : WordTrace (prefixWord ++ tailWord_5283932) baseStart_5283932 baseEnd_5283932 := by
    simpa [prefixWord, tailWord_5283932, baseEnd_5283932] using wordTrace_append hprefix tailTrace_5283932
  have hstable : (prefixWord ++ tailWord_5283932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283932).length < 2 ^ (prefixWord ++ tailWord_5283932).sum := by decide
  have hdescent : baseEnd_5283932 < baseStart_5283932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283946 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_5283946 : Nat := 118140960795 + 5283946 * 2 ^ 59
def prefixEnd_5283946 : Nat := 4983230072969 + 3 ^ 40 * 5283946 * 2
def baseEnd_5283946 : Nat := 2713204050402088770674581

theorem tailTrace_5283946 : CollatzResearch.WordTrace tailWord_5283946 prefixEnd_5283946 2713204050402088770674581 := by
  unfold tailWord_5283946
  simp only [CollatzResearch.WordTrace]
  refine ⟨48180335828793385744023923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128480895543449028650730461 48180335828793385744023923)
  ·
    refine ⟨72270503743190078616035885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48180335828793385744023923 72270503743190078616035885)
    ·
      refine ⟨27101438903696279481013457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72270503743190078616035885 27101438903696279481013457)
      ·
        refine ⟨20326079177772209610760093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27101438903696279481013457 20326079177772209610760093)
        ·
          refine ⟨7622279691664578604035035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20326079177772209610760093 7622279691664578604035035)
          ·
            refine ⟨11433419537496867906052553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7622279691664578604035035 11433419537496867906052553)
            ·
              refine ⟨8575064653122650929539415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11433419537496867906052553 8575064653122650929539415)
              ·
                refine ⟨12862596979683976394309123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8575064653122650929539415 12862596979683976394309123)
                ·
                  refine ⟨19293895469525964591463685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12862596979683976394309123 19293895469525964591463685)
                  ·
                    refine ⟨3617605400536118360899441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19293895469525964591463685 3617605400536118360899441)
                    ·
                      refine ⟨2713204050402088770674581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617605400536118360899441 2713204050402088770674581)
                      ·
                        rfl

theorem cell23_5283946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_5283946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283946 prefixEnd_5283946 := by exact prefixLift 5283946
  have htrace : WordTrace (prefixWord ++ tailWord_5283946) baseStart_5283946 baseEnd_5283946 := by
    simpa [prefixWord, tailWord_5283946, baseEnd_5283946] using wordTrace_append hprefix tailTrace_5283946
  have hstable : (prefixWord ++ tailWord_5283946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283946).length < 2 ^ (prefixWord ++ tailWord_5283946).sum := by decide
  have hdescent : baseEnd_5283946 < baseStart_5283946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5283975 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_5283975 : Nat := 118140960795 + 5283975 * 2 ^ 59
def prefixEnd_5283975 : Nat := 4983230072969 + 3 ^ 40 * 5283975 * 2
def baseEnd_5283975 : Nat := 2713218941341069157211947

theorem tailTrace_5283975 : CollatzResearch.WordTrace tailWord_5283975 prefixEnd_5283975 2713218941341069157211947 := by
  unfold tailWord_5283975
  simp only [CollatzResearch.WordTrace]
  refine ⟨192722401032068480928901379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128481600688045653952600919 192722401032068480928901379)
  ·
    refine ⟨289083601548102721393352069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192722401032068480928901379 289083601548102721393352069)
    ·
      refine ⟨54203175290269260261253513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289083601548102721393352069 54203175290269260261253513)
      ·
        refine ⟨40652381467701945195940135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54203175290269260261253513 40652381467701945195940135)
        ·
          refine ⟨60978572201552917793910203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40652381467701945195940135 60978572201552917793910203)
          ·
            refine ⟨91467858302329376690865305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60978572201552917793910203 91467858302329376690865305)
            ·
              refine ⟨68600893726747032518148979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91467858302329376690865305 68600893726747032518148979)
              ·
                refine ⟨102901340590120548777223469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68600893726747032518148979 102901340590120548777223469)
                ·
                  refine ⟨38588002721295205791458801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102901340590120548777223469 38588002721295205791458801)
                  ·
                    refine ⟨28941002040971404343594101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38588002721295205791458801 28941002040971404343594101)
                    ·
                      refine ⟨2713218941341069157211947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28941002040971404343594101 2713218941341069157211947)
                      ·
                        rfl

theorem cell23_5283975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_5283975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5283975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5283975 prefixEnd_5283975 := by exact prefixLift 5283975
  have htrace : WordTrace (prefixWord ++ tailWord_5283975) baseStart_5283975 baseEnd_5283975 := by
    simpa [prefixWord, tailWord_5283975, baseEnd_5283975] using wordTrace_append hprefix tailTrace_5283975
  have hstable : (prefixWord ++ tailWord_5283975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5283975).length < 2 ^ (prefixWord ++ tailWord_5283975).sum := by decide
  have hdescent : baseEnd_5283975 < baseStart_5283975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5283975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284015 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_5284015 : Nat := 118140960795 + 5284015 * 2 ^ 59
def prefixEnd_5284015 : Nat := 4983230072969 + 3 ^ 40 * 5284015 * 2
def baseEnd_5284015 : Nat := 2713239480567249000711763

theorem tailTrace_5284015 : CollatzResearch.WordTrace tailWord_5284015 prefixEnd_5284015 2713239480567249000711763 := by
  unfold tailWord_5284015
  simp only [CollatzResearch.WordTrace]
  refine ⟨192723859951923567760357499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128482573301282378506904999 192723859951923567760357499)
  ·
    refine ⟨289085789927885351640536249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192723859951923567760357499 289085789927885351640536249)
    ·
      refine ⟨216814342445914013730402187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289085789927885351640536249 216814342445914013730402187)
      ·
        refine ⟨325221513668871020595603281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216814342445914013730402187 325221513668871020595603281)
        ·
          refine ⟨243916135251653265446702461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325221513668871020595603281 243916135251653265446702461)
          ·
            refine ⟨91468550719369974542513423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243916135251653265446702461 91468550719369974542513423)
            ·
              refine ⟨137202826079054961813770135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91468550719369974542513423 137202826079054961813770135)
              ·
                refine ⟨205804239118582442720655203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137202826079054961813770135 205804239118582442720655203)
                ·
                  refine ⟨308706358677873664080982805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205804239118582442720655203 308706358677873664080982805)
                  ·
                    refine ⟨14470610563025328003796069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 308706358677873664080982805 14470610563025328003796069)
                    ·
                      refine ⟨2713239480567249000711763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14470610563025328003796069 2713239480567249000711763)
                      ·
                        rfl

theorem cell23_5284015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_5284015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284015 prefixEnd_5284015 := by exact prefixLift 5284015
  have htrace : WordTrace (prefixWord ++ tailWord_5284015) baseStart_5284015 baseEnd_5284015 := by
    simpa [prefixWord, tailWord_5284015, baseEnd_5284015] using wordTrace_append hprefix tailTrace_5284015
  have hstable : (prefixWord ++ tailWord_5284015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284015).length < 2 ^ (prefixWord ++ tailWord_5284015).sum := by decide
  have hdescent : baseEnd_5284015 < baseStart_5284015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284025 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 10]
def baseStart_5284025 : Nat := 118140960795 + 5284025 * 2 ^ 59
def prefixEnd_5284025 : Nat := 4983230072969 + 3 ^ 40 * 5284025 * 2
def baseEnd_5284025 : Nat := 301471623930421551287413

theorem tailTrace_5284025 : CollatzResearch.WordTrace tailWord_5284025 prefixEnd_5284025 301471623930421551287413 := by
  unfold tailWord_5284025
  simp only [CollatzResearch.WordTrace]
  refine ⟨192724224681887339468221529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128482816454591559645481019 192724224681887339468221529)
  ·
    refine ⟨144543168511415504601166147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192724224681887339468221529 144543168511415504601166147)
    ·
      refine ⟨216814752767123256901749221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144543168511415504601166147 216814752767123256901749221)
      ·
        refine ⟨40652766143835610669077979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 216814752767123256901749221 40652766143835610669077979)
        ·
          refine ⟨60979149215753416003616969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40652766143835610669077979 60979149215753416003616969)
          ·
            refine ⟨45734361911815062002712727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60979149215753416003616969 45734361911815062002712727)
            ·
              refine ⟨68601542867722593004069091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45734361911815062002712727 68601542867722593004069091)
              ·
                refine ⟨102902314301583889506103637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68601542867722593004069091 102902314301583889506103637)
                ·
                  refine ⟨301471623930421551287413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 102902314301583889506103637 301471623930421551287413)
                  ·
                    rfl

theorem cell23_5284025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_5284025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284025 prefixEnd_5284025 := by exact prefixLift 5284025
  have htrace : WordTrace (prefixWord ++ tailWord_5284025) baseStart_5284025 baseEnd_5284025 := by
    simpa [prefixWord, tailWord_5284025, baseEnd_5284025] using wordTrace_append hprefix tailTrace_5284025
  have hstable : (prefixWord ++ tailWord_5284025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284025).length < 2 ^ (prefixWord ++ tailWord_5284025).sum := by decide
  have hdescent : baseEnd_5284025 < baseStart_5284025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284042 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 6]
def baseStart_5284042 : Nat := 118140960795 + 5284042 * 2 ^ 59
def prefixEnd_5284042 : Nat := 4983230072969 + 3 ^ 40 * 5284042 * 2
def baseEnd_5284042 : Nat := 301472593838324488341571

theorem tailTrace_5284042 : CollatzResearch.WordTrace tailWord_5284042 prefixEnd_5284042 301472593838324488341571 := by
  unfold tailWord_5284042
  simp only [CollatzResearch.WordTrace]
  refine ⟨48181211180706437842897595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128483229815217167581060253 48181211180706437842897595)
  ·
    refine ⟨72271816771059656764346393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48181211180706437842897595 72271816771059656764346393)
    ·
      refine ⟨54203862578294742573259795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72271816771059656764346393 54203862578294742573259795)
      ·
        refine ⟨81305793867442113859889693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54203862578294742573259795 81305793867442113859889693)
        ·
          refine ⟨30489672700290792697458635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81305793867442113859889693 30489672700290792697458635)
          ·
            refine ⟨45734509050436189046187953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30489672700290792697458635 45734509050436189046187953)
            ·
              refine ⟨34300881787827141784640965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45734509050436189046187953 34300881787827141784640965)
              ·
                refine ⟨6431415335217589084620181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34300881787827141784640965 6431415335217589084620181)
                ·
                  refine ⟨301472593838324488341571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6431415335217589084620181 301472593838324488341571)
                  ·
                    rfl

theorem cell23_5284042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 6].length) (baseStart_5284042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284042 prefixEnd_5284042 := by exact prefixLift 5284042
  have htrace : WordTrace (prefixWord ++ tailWord_5284042) baseStart_5284042 baseEnd_5284042 := by
    simpa [prefixWord, tailWord_5284042, baseEnd_5284042] using wordTrace_append hprefix tailTrace_5284042
  have hstable : (prefixWord ++ tailWord_5284042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284042).length < 2 ^ (prefixWord ++ tailWord_5284042).sum := by decide
  have hdescent : baseEnd_5284042 < baseStart_5284042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284046 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_5284046 : Nat := 118140960795 + 5284046 * 2 ^ 59
def prefixEnd_5284046 : Nat := 4983230072969 + 3 ^ 40 * 5284046 * 2
def baseEnd_5284046 : Nat := 904418466155846126474707

theorem tailTrace_5284046 : CollatzResearch.WordTrace tailWord_5284046 prefixEnd_5284046 904418466155846126474707 := by
  unfold tailWord_5284046
  simp only [CollatzResearch.WordTrace]
  refine ⟨24090623826851407506841999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128483327076540840036490661 24090623826851407506841999)
  ·
    refine ⟨36135935740277111260262999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24090623826851407506841999 36135935740277111260262999)
    ·
      refine ⟨54203903610415666890394499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36135935740277111260262999 54203903610415666890394499)
      ·
        refine ⟨81305855415623500335591749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54203903610415666890394499 81305855415623500335591749)
        ·
          refine ⟨15244847890429406312923453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81305855415623500335591749 15244847890429406312923453)
          ·
            refine ⟨5716817958911027367346295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15244847890429406312923453 5716817958911027367346295)
            ·
              refine ⟨8575226938366541051019443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716817958911027367346295 8575226938366541051019443)
              ·
                refine ⟨12862840407549811576529165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8575226938366541051019443 12862840407549811576529165)
                ·
                  refine ⟨4823565152831179341198437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12862840407549811576529165 4823565152831179341198437)
                  ·
                    refine ⟨904418466155846126474707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823565152831179341198437 904418466155846126474707)
                    ·
                      rfl

theorem cell23_5284046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_5284046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284046 prefixEnd_5284046 := by exact prefixLift 5284046
  have htrace : WordTrace (prefixWord ++ tailWord_5284046) baseStart_5284046 baseEnd_5284046 := by
    simpa [prefixWord, tailWord_5284046, baseEnd_5284046] using wordTrace_append hprefix tailTrace_5284046
  have hstable : (prefixWord ++ tailWord_5284046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284046).length < 2 ^ (prefixWord ++ tailWord_5284046).sum := by decide
  have hdescent : baseEnd_5284046 < baseStart_5284046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284055 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 2, 9]
def baseStart_5284055 : Nat := 118140960795 + 5284055 * 2 ^ 59
def prefixEnd_5284055 : Nat := 4983230072969 + 3 ^ 40 * 5284055 * 2
def baseEnd_5284055 : Nat := 904420006597809614737193

theorem tailTrace_5284055 : CollatzResearch.WordTrace tailWord_5284055 prefixEnd_5284055 904420006597809614737193 := by
  unfold tailWord_5284055
  simp only [CollatzResearch.WordTrace]
  refine ⟨192725318871778654591813619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128483545914519103061209079 192725318871778654591813619)
  ·
    refine ⟨289087978307667981887720429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192725318871778654591813619 289087978307667981887720429)
    ·
      refine ⟨108407991865375493207895161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289087978307667981887720429 108407991865375493207895161)
      ·
        refine ⟨81305993899031619905921371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108407991865375493207895161 81305993899031619905921371)
        ·
          refine ⟨121958990848547429858882057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81305993899031619905921371 121958990848547429858882057)
          ·
            refine ⟨91469243136410572394161543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121958990848547429858882057 91469243136410572394161543)
            ·
              refine ⟨137203864704615858591242315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91469243136410572394161543 137203864704615858591242315)
              ·
                refine ⟨205805797056923787886863473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137203864704615858591242315 205805797056923787886863473)
                ·
                  refine ⟨154354347792692840915147605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205805797056923787886863473 154354347792692840915147605)
                  ·
                    refine ⟨904420006597809614737193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 154354347792692840915147605 904420006597809614737193)
                    ·
                      rfl

theorem cell23_5284055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_5284055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284055 prefixEnd_5284055 := by exact prefixLift 5284055
  have htrace : WordTrace (prefixWord ++ tailWord_5284055) baseStart_5284055 baseEnd_5284055 := by
    simpa [prefixWord, tailWord_5284055, baseEnd_5284055] using wordTrace_append hprefix tailTrace_5284055
  have hstable : (prefixWord ++ tailWord_5284055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284055).length < 2 ^ (prefixWord ++ tailWord_5284055).sum := by decide
  have hdescent : baseEnd_5284055 < baseStart_5284055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284119 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 1, 6]
def baseStart_5284119 : Nat := 118140960795 + 5284119 * 2 ^ 59
def prefixEnd_5284119 : Nat := 4983230072969 + 3 ^ 40 * 5284119 * 2
def baseEnd_5284119 : Nat := 904430960851772197937095

theorem tailTrace_5284119 : CollatzResearch.WordTrace tailWord_5284119 prefixEnd_5284119 904430960851772197937095 := by
  unfold tailWord_5284119
  simp only [CollatzResearch.WordTrace]
  refine ⟨192727653143546793522143411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128485102095697862348095607 192727653143546793522143411)
  ·
    refine ⟨289091479715320190283215117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192727653143546793522143411 289091479715320190283215117)
    ·
      refine ⟨108409304893245071356205669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289091479715320190283215117 108409304893245071356205669)
      ·
        refine ⟨20326744667483450879288563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108409304893245071356205669 20326744667483450879288563)
        ·
          refine ⟨30490117001225176318932845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20326744667483450879288563 30490117001225176318932845)
          ·
            refine ⟨11433793875459441119599817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30490117001225176318932845 11433793875459441119599817)
            ·
              refine ⟨8575345406594580839699863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11433793875459441119599817 8575345406594580839699863)
              ·
                refine ⟨12863018109891871259549795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8575345406594580839699863 12863018109891871259549795)
                ·
                  refine ⟨19294527164837806889324693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12863018109891871259549795 19294527164837806889324693)
                  ·
                    refine ⟨904430960851772197937095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19294527164837806889324693 904430960851772197937095)
                    ·
                      rfl

theorem cell23_5284119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_5284119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284119 prefixEnd_5284119 := by exact prefixLift 5284119
  have htrace : WordTrace (prefixWord ++ tailWord_5284119) baseStart_5284119 baseEnd_5284119 := by
    simpa [prefixWord, tailWord_5284119, baseEnd_5284119] using wordTrace_append hprefix tailTrace_5284119
  have hstable : (prefixWord ++ tailWord_5284119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284119).length < 2 ^ (prefixWord ++ tailWord_5284119).sum := by decide
  have hdescent : baseEnd_5284119 < baseStart_5284119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284129 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_5284129 : Nat := 118140960795 + 5284129 * 2 ^ 59
def prefixEnd_5284129 : Nat := 4983230072969 + 3 ^ 40 * 5284129 * 2
def baseEnd_5284129 : Nat := 2713298017361861554686239

theorem tailTrace_5284129 : CollatzResearch.WordTrace tailWord_5284129 prefixEnd_5284129 2713298017361861554686239 := by
  unfold tailWord_5284129
  simp only [CollatzResearch.WordTrace]
  refine ⟨192728017873510565230007441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128485345249007043486671627 192728017873510565230007441)
  ·
    refine ⟨144546013405132923922505581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192728017873510565230007441 144546013405132923922505581)
    ·
      refine ⟨54204755026924846470939593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144546013405132923922505581 54204755026924846470939593)
      ·
        refine ⟨40653566270193634853204695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54204755026924846470939593 40653566270193634853204695)
        ·
          refine ⟨60980349405290452279807043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40653566270193634853204695 60980349405290452279807043)
          ·
            refine ⟨91470524107935678419710565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60980349405290452279807043 91470524107935678419710565)
            ·
              refine ⟨17150723270237939703695731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91470524107935678419710565 17150723270237939703695731)
              ·
                refine ⟨25726084905356909555543597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17150723270237939703695731 25726084905356909555543597)
                ·
                  refine ⟨9647281839508841083328849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25726084905356909555543597 9647281839508841083328849)
                  ·
                    refine ⟨7235461379631630812496637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9647281839508841083328849 7235461379631630812496637)
                    ·
                      refine ⟨2713298017361861554686239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7235461379631630812496637 2713298017361861554686239)
                      ·
                        rfl

theorem cell23_5284129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_5284129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284129 prefixEnd_5284129 := by exact prefixLift 5284129
  have htrace : WordTrace (prefixWord ++ tailWord_5284129) baseStart_5284129 baseEnd_5284129 := by
    simpa [prefixWord, tailWord_5284129, baseEnd_5284129] using wordTrace_append hprefix tailTrace_5284129
  have hstable : (prefixWord ++ tailWord_5284129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284129).length < 2 ^ (prefixWord ++ tailWord_5284129).sum := by decide
  have hdescent : baseEnd_5284129 < baseStart_5284129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284143 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 1, 2, 2]
def baseStart_5284143 : Nat := 118140960795 + 5284143 * 2 ^ 59
def prefixEnd_5284143 : Nat := 4983230072969 + 3 ^ 40 * 5284143 * 2
def baseEnd_5284143 : Nat := 2713305206091024499911175

theorem tailTrace_5284143 : CollatzResearch.WordTrace tailWord_5284143 prefixEnd_5284143 2713305206091024499911175 := by
  unfold tailWord_5284143
  simp only [CollatzResearch.WordTrace]
  refine ⟨192728528495459845621017083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128485685663639897080678055 192728528495459845621017083)
  ·
    refine ⟨289092792743189768431525625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192728528495459845621017083 289092792743189768431525625)
    ·
      refine ⟨216819594557392326323644219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289092792743189768431525625 216819594557392326323644219)
      ·
        refine ⟨325229391836088489485466329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216819594557392326323644219 325229391836088489485466329)
        ·
          refine ⟨243922043877066367114099747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325229391836088489485466329 243922043877066367114099747)
          ·
            refine ⟨365883065815599550671149621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243922043877066367114099747 365883065815599550671149621)
            ·
              refine ⟨34301537420212457875420277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 365883065815599550671149621 34301537420212457875420277)
              ·
                refine ⟨3215769133144917925820651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34301537420212457875420277 3215769133144917925820651)
                ·
                  refine ⟨4823653699717376888730977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215769133144917925820651 4823653699717376888730977)
                  ·
                    refine ⟨3617740274788032666548233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4823653699717376888730977 3617740274788032666548233)
                    ·
                      refine ⟨2713305206091024499911175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3617740274788032666548233 2713305206091024499911175)
                      ·
                        rfl

theorem cell23_5284143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 2, 2].length) (baseStart_5284143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284143 prefixEnd_5284143 := by exact prefixLift 5284143
  have htrace : WordTrace (prefixWord ++ tailWord_5284143) baseStart_5284143 baseEnd_5284143 := by
    simpa [prefixWord, tailWord_5284143, baseEnd_5284143] using wordTrace_append hprefix tailTrace_5284143
  have hstable : (prefixWord ++ tailWord_5284143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284143).length < 2 ^ (prefixWord ++ tailWord_5284143).sum := by decide
  have hdescent : baseEnd_5284143 < baseStart_5284143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284153 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 2, 4]
def baseStart_5284153 : Nat := 118140960795 + 5284153 * 2 ^ 59
def prefixEnd_5284153 : Nat := 4983230072969 + 3 ^ 40 * 5284153 * 2
def baseEnd_5284153 : Nat := 904436780299189820262043

theorem tailTrace_5284153 : CollatzResearch.WordTrace tailWord_5284153 prefixEnd_5284153 904436780299189820262043 := by
  unfold tailWord_5284153
  simp only [CollatzResearch.WordTrace]
  refine ⟨192728893225423617328881113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128485928816949078219254075 192728893225423617328881113)
  ·
    refine ⟨144546669919067712996660835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192728893225423617328881113 144546669919067712996660835)
    ·
      refine ⟨216820004878601569494991253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144546669919067712996660835 216820004878601569494991253)
      ·
        refine ⟨10163437728684448570077715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 216820004878601569494991253 10163437728684448570077715)
        ·
          refine ⟨15245156593026672855116573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10163437728684448570077715 15245156593026672855116573)
          ·
            refine ⟨5716933722385002320668715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15245156593026672855116573 5716933722385002320668715)
            ·
              refine ⟨8575400583577503481003073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716933722385002320668715 8575400583577503481003073)
              ·
                refine ⟨6431550437683127610752305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8575400583577503481003073 6431550437683127610752305)
                ·
                  refine ⟨4823662828262345708064229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6431550437683127610752305 4823662828262345708064229)
                  ·
                    refine ⟨904436780299189820262043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823662828262345708064229 904436780299189820262043)
                    ·
                      rfl

theorem cell23_5284153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_5284153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284153 prefixEnd_5284153 := by exact prefixLift 5284153
  have htrace : WordTrace (prefixWord ++ tailWord_5284153) baseStart_5284153 baseEnd_5284153 := by
    simpa [prefixWord, tailWord_5284153, baseEnd_5284153] using wordTrace_append hprefix tailTrace_5284153
  have hstable : (prefixWord ++ tailWord_5284153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284153).length < 2 ^ (prefixWord ++ tailWord_5284153).sum := by decide
  have hdescent : baseEnd_5284153 < baseStart_5284153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284176 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3]
def baseStart_5284176 : Nat := 118140960795 + 5284176 * 2 ^ 59
def prefixEnd_5284176 : Nat := 4983230072969 + 3 ^ 40 * 5284176 * 2
def baseEnd_5284176 : Nat := 2713322150952622870798523

theorem tailTrace_5284176 : CollatzResearch.WordTrace tailWord_5284176 prefixEnd_5284176 2713322150952622870798523 := by
  unfold tailWord_5284176
  simp only [CollatzResearch.WordTrace]
  refine ⟨96364866052170146128484191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128486488069560194837978921 96364866052170146128484191)
  ·
    refine ⟨144547299078255219192726287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96364866052170146128484191 144547299078255219192726287)
    ·
      refine ⟨216820948617382828789089431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144547299078255219192726287 216820948617382828789089431)
      ·
        refine ⟨325231422926074243183634147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216820948617382828789089431 325231422926074243183634147)
        ·
          refine ⟨487847134389111364775451221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325231422926074243183634147 487847134389111364775451221)
          ·
            refine ⟨5716958606122398805962319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 487847134389111364775451221 5716958606122398805962319)
            ·
              refine ⟨8575437909183598208943479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5716958606122398805962319 8575437909183598208943479)
              ·
                refine ⟨12863156863775397313415219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8575437909183598208943479 12863156863775397313415219)
                ·
                  refine ⟨19294735295663095970122829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12863156863775397313415219 19294735295663095970122829)
                  ·
                    refine ⟨7235525735873660988796061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19294735295663095970122829 7235525735873660988796061)
                    ·
                      refine ⟨2713322150952622870798523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7235525735873660988796061 2713322150952622870798523)
                      ·
                        rfl

theorem cell23_5284176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_5284176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284176 prefixEnd_5284176 := by exact prefixLift 5284176
  have htrace : WordTrace (prefixWord ++ tailWord_5284176) baseStart_5284176 baseEnd_5284176 := by
    simpa [prefixWord, tailWord_5284176, baseEnd_5284176] using wordTrace_append hprefix tailTrace_5284176
  have hstable : (prefixWord ++ tailWord_5284176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284176).length < 2 ^ (prefixWord ++ tailWord_5284176).sum := by decide
  have hdescent : baseEnd_5284176 < baseStart_5284176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284227 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 2, 1, 3]
def baseStart_5284227 : Nat := 118140960795 + 5284227 * 2 ^ 59
def prefixEnd_5284227 : Nat := 4983230072969 + 3 ^ 40 * 5284227 * 2
def baseEnd_5284227 : Nat := 2713348338466002171260789

theorem tailTrace_5284227 : CollatzResearch.WordTrace tailWord_5284227 prefixEnd_5284227 2713348338466002171260789 := by
  unfold tailWord_5284227
  simp only [CollatzResearch.WordTrace]
  refine ⟨192731592227155527967074935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128487728151437018644716623 192731592227155527967074935)
  ·
    refine ⟨289097388340733291950612403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192731592227155527967074935 289097388340733291950612403)
    ·
      refine ⟨433646082511099937925918605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289097388340733291950612403 433646082511099937925918605)
      ·
        refine ⟨162617280941662476722219477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433646082511099937925918605 162617280941662476722219477)
        ·
          refine ⟨3811342522070214298177019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 162617280941662476722219477 3811342522070214298177019)
          ·
            refine ⟨5717013783105321447265529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811342522070214298177019 5717013783105321447265529)
            ·
              refine ⟨4287760337328991085449147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5717013783105321447265529 4287760337328991085449147)
              ·
                refine ⟨6431640505993486628173721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287760337328991085449147 6431640505993486628173721)
                ·
                  refine ⟨4823730379495114971130291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6431640505993486628173721 4823730379495114971130291)
                  ·
                    refine ⟨7235595569242672456695437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4823730379495114971130291 7235595569242672456695437)
                    ·
                      refine ⟨2713348338466002171260789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7235595569242672456695437 2713348338466002171260789)
                      ·
                        rfl

theorem cell23_5284227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_5284227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284227 prefixEnd_5284227 := by exact prefixLift 5284227
  have htrace : WordTrace (prefixWord ++ tailWord_5284227) baseStart_5284227 baseEnd_5284227 := by
    simpa [prefixWord, tailWord_5284227, baseEnd_5284227] using wordTrace_append hprefix tailTrace_5284227
  have hstable : (prefixWord ++ tailWord_5284227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284227).length < 2 ^ (prefixWord ++ tailWord_5284227).sum := by decide
  have hdescent : baseEnd_5284227 < baseStart_5284227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284273 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 5]
def baseStart_5284273 : Nat := 118140960795 + 5284273 * 2 ^ 59
def prefixEnd_5284273 : Nat := 4983230072969 + 3 ^ 40 * 5284273 * 2
def baseEnd_5284273 : Nat := 301485773175123221253953

theorem tailTrace_5284273 : CollatzResearch.WordTrace tailWord_5284273 prefixEnd_5284273 301485773175123221253953 := by
  unfold tailWord_5284273
  simp only [CollatzResearch.WordTrace]
  refine ⟨192733269984988877823249473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128488846656659251882166315 192733269984988877823249473)
  ·
    refine ⟨144549952488741658367437105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192733269984988877823249473 144549952488741658367437105)
    ·
      refine ⟨108412464366556243775577829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144549952488741658367437105 108412464366556243775577829)
      ·
        refine ⟨20327337068729295707920843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108412464366556243775577829 20327337068729295707920843)
        ·
          refine ⟨30491005603093943561881265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20327337068729295707920843 30491005603093943561881265)
          ·
            refine ⟨22868254202320457671410949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30491005603093943561881265 22868254202320457671410949)
            ·
              refine ⟨4287797662935085813389553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22868254202320457671410949 4287797662935085813389553)
              ·
                refine ⟨3215848247201314360042165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287797662935085813389553 3215848247201314360042165)
                ·
                  refine ⟨301485773175123221253953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3215848247201314360042165 301485773175123221253953)
                  ·
                    rfl

theorem cell23_5284273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 5].length) (baseStart_5284273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284273 prefixEnd_5284273 := by exact prefixLift 5284273
  have htrace : WordTrace (prefixWord ++ tailWord_5284273) baseStart_5284273 baseEnd_5284273 := by
    simpa [prefixWord, tailWord_5284273, baseEnd_5284273] using wordTrace_append hprefix tailTrace_5284273
  have hstable : (prefixWord ++ tailWord_5284273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284273).length < 2 ^ (prefixWord ++ tailWord_5284273).sum := by decide
  have hdescent : baseEnd_5284273 < baseStart_5284273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284279 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_5284279 : Nat := 118140960795 + 5284279 * 2 ^ 59
def prefixEnd_5284279 : Nat := 4983230072969 + 3 ^ 40 * 5284279 * 2
def baseEnd_5284279 : Nat := 2713375039460035967810549

theorem tailTrace_5284279 : CollatzResearch.WordTrace tailWord_5284279 prefixEnd_5284279 2713375039460035967810549 := by
  unfold tailWord_5284279
  simp only [CollatzResearch.WordTrace]
  refine ⟨192733488822967140847967891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128488992548644760565311927 192733488822967140847967891)
  ·
    refine ⟨289100233234450711271951837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192733488822967140847967891 289100233234450711271951837)
    ·
      refine ⟨108412587462919016726981939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 289100233234450711271951837 108412587462919016726981939)
      ·
        refine ⟨162618881194378525090472909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108412587462919016726981939 162618881194378525090472909)
        ·
          refine ⟨60982080447891946908927341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162618881194378525090472909 60982080447891946908927341)
          ·
            refine ⟨22868280167959480090847753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60982080447891946908927341 22868280167959480090847753)
            ·
              refine ⟨17151210125969610068135815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22868280167959480090847753 17151210125969610068135815)
              ·
                refine ⟨25726815188954415102203723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17151210125969610068135815 25726815188954415102203723)
                ·
                  refine ⟨38590222783431622653305585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25726815188954415102203723 38590222783431622653305585)
                  ·
                    refine ⟨28942667087573716989979189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38590222783431622653305585 28942667087573716989979189)
                    ·
                      refine ⟨2713375039460035967810549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28942667087573716989979189 2713375039460035967810549)
                      ·
                        rfl

theorem cell23_5284279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_5284279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284279 prefixEnd_5284279 := by exact prefixLift 5284279
  have htrace : WordTrace (prefixWord ++ tailWord_5284279) baseStart_5284279 baseEnd_5284279 := by
    simpa [prefixWord, tailWord_5284279, baseEnd_5284279] using wordTrace_append hprefix tailTrace_5284279
  have hstable : (prefixWord ++ tailWord_5284279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284279).length < 2 ^ (prefixWord ++ tailWord_5284279).sum := by decide
  have hdescent : baseEnd_5284279 < baseStart_5284279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284319 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_5284319 : Nat := 118140960795 + 5284319 * 2 ^ 59
def prefixEnd_5284319 : Nat := 4983230072969 + 3 ^ 40 * 5284319 * 2
def baseEnd_5284319 : Nat := 2713395578686215811310365

theorem tailTrace_5284319 : CollatzResearch.WordTrace tailWord_5284319 prefixEnd_5284319 2713395578686215811310365 := by
  unfold tailWord_5284319
  simp only [CollatzResearch.WordTrace]
  refine ⟨192734947742822227679424011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128489965161881485119616007 192734947742822227679424011)
  ·
    refine ⟨289102421614233341519136017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192734947742822227679424011 289102421614233341519136017)
    ·
      refine ⟨216826816210675006139352013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289102421614233341519136017 216826816210675006139352013)
      ·
        refine ⟨81310056079003127302257005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216826816210675006139352013 81310056079003127302257005)
        ·
          refine ⟨30491271029626172738346377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81310056079003127302257005 30491271029626172738346377)
          ·
            refine ⟨22868453272219629553759783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30491271029626172738346377 22868453272219629553759783)
            ·
              refine ⟨34302679908329444330639675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22868453272219629553759783 34302679908329444330639675)
              ·
                refine ⟨51454019862494166495959513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34302679908329444330639675 51454019862494166495959513)
                ·
                  refine ⟨38590514896870624871969635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51454019862494166495959513 38590514896870624871969635)
                  ·
                    refine ⟨57885772345305937307954453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38590514896870624871969635 57885772345305937307954453)
                    ·
                      refine ⟨2713395578686215811310365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57885772345305937307954453 2713395578686215811310365)
                      ·
                        rfl

theorem cell23_5284319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_5284319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284319 prefixEnd_5284319 := by exact prefixLift 5284319
  have htrace : WordTrace (prefixWord ++ tailWord_5284319) baseStart_5284319 baseEnd_5284319 := by
    simpa [prefixWord, tailWord_5284319, baseEnd_5284319] using wordTrace_append hprefix tailTrace_5284319
  have hstable : (prefixWord ++ tailWord_5284319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284319).length < 2 ^ (prefixWord ++ tailWord_5284319).sum := by decide
  have hdescent : baseEnd_5284319 < baseStart_5284319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284329 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 6]
def baseStart_5284329 : Nat := 118140960795 + 5284329 * 2 ^ 59
def prefixEnd_5284329 : Nat := 4983230072969 + 3 ^ 40 * 5284329 * 2
def baseEnd_5284329 : Nat := 301488968165862308020591

theorem tailTrace_5284329 : CollatzResearch.WordTrace tailWord_5284329 prefixEnd_5284329 301488968165862308020591 := by
  unfold tailWord_5284329
  simp only [CollatzResearch.WordTrace]
  refine ⟨192735312472785999387288041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128490208315190666258192027 192735312472785999387288041)
  ·
    refine ⟨144551484354589499540466031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192735312472785999387288041 144551484354589499540466031)
    ·
      refine ⟨216827226531884249310699047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144551484354589499540466031 216827226531884249310699047)
      ·
        refine ⟨325240839797826373966048571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216827226531884249310699047 325240839797826373966048571)
        ·
          refine ⟨487861259696739560949072857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325240839797826373966048571 487861259696739560949072857)
          ·
            refine ⟨365895944772554670711804643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487861259696739560949072857 365895944772554670711804643)
            ·
              refine ⟨548843917158832006067706965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365895944772554670711804643 548843917158832006067706965)
              ·
                refine ⟨6431764654205062571105941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 548843917158832006067706965 6431764654205062571105941)
                ·
                  refine ⟨301488968165862308020591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6431764654205062571105941 301488968165862308020591)
                  ·
                    rfl

theorem cell23_5284329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_5284329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284329 prefixEnd_5284329 := by exact prefixLift 5284329
  have htrace : WordTrace (prefixWord ++ tailWord_5284329) baseStart_5284329 baseEnd_5284329 := by
    simpa [prefixWord, tailWord_5284329, baseEnd_5284329] using wordTrace_append hprefix tailTrace_5284329
  have hstable : (prefixWord ++ tailWord_5284329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284329).length < 2 ^ (prefixWord ++ tailWord_5284329).sum := by decide
  have hdescent : baseEnd_5284329 < baseStart_5284329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284333 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_5284333 : Nat := 118140960795 + 5284333 * 2 ^ 59
def prefixEnd_5284333 : Nat := 4983230072969 + 3 ^ 40 * 5284333 * 2
def baseEnd_5284333 : Nat := 904467589138459585511767

theorem tailTrace_5284333 : CollatzResearch.WordTrace tailWord_5284333 prefixEnd_5284333 904467589138459585511767 := by
  unfold tailWord_5284333
  simp only [CollatzResearch.WordTrace]
  refine ⟨192735458364771508070433653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128490305576514338713622435 192735458364771508070433653)
  ·
    refine ⟨18068949221697328881603155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192735458364771508070433653 18068949221697328881603155)
    ·
      refine ⟨27103423832545993322404733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18068949221697328881603155 27103423832545993322404733)
      ·
        refine ⟨10163783937204747495901775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27103423832545993322404733 10163783937204747495901775)
        ·
          refine ⟨15245675905807121243852663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10163783937204747495901775 15245675905807121243852663)
          ·
            refine ⟨22868513858710681865778995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15245675905807121243852663 22868513858710681865778995)
            ·
              refine ⟨34302770788066022798668493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22868513858710681865778995 34302770788066022798668493)
              ·
                refine ⟨12863539045524758549500685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34302770788066022798668493 12863539045524758549500685)
                ·
                  refine ⟨4823827142071784456062757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12863539045524758549500685 4823827142071784456062757)
                  ·
                    refine ⟨904467589138459585511767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4823827142071784456062757 904467589138459585511767)
                    ·
                      rfl

theorem cell23_5284333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_5284333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284333 prefixEnd_5284333 := by exact prefixLift 5284333
  have htrace : WordTrace (prefixWord ++ tailWord_5284333) baseStart_5284333 baseEnd_5284333 := by
    simpa [prefixWord, tailWord_5284333, baseEnd_5284333] using wordTrace_append hprefix tailTrace_5284333
  have hstable : (prefixWord ++ tailWord_5284333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284333).length < 2 ^ (prefixWord ++ tailWord_5284333).sum := by decide
  have hdescent : baseEnd_5284333 < baseStart_5284333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284349 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_5284349 : Nat := 118140960795 + 5284349 * 2 ^ 59
def prefixEnd_5284349 : Nat := 4983230072969 + 3 ^ 40 * 5284349 * 2
def baseEnd_5284349 : Nat := 2713410983105850693935227

theorem tailTrace_5284349 : CollatzResearch.WordTrace tailWord_5284349 prefixEnd_5284349 2713410983105850693935227 := by
  unfold tailWord_5284349
  simp only [CollatzResearch.WordTrace]
  refine ⟨192736041932713542803016101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128490694621809028535344067 192736041932713542803016101)
  ·
    refine ⟨36138007862383789275565519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192736041932713542803016101 36138007862383789275565519)
    ·
      refine ⟨54207011793575683913348279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36138007862383789275565519 54207011793575683913348279)
      ·
        refine ⟨81310517690363525870022419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54207011793575683913348279 81310517690363525870022419)
        ·
          refine ⟨121965776535545288805033629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81310517690363525870022419 121965776535545288805033629)
          ·
            refine ⟨45737166200829483301887611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121965776535545288805033629 45737166200829483301887611)
            ·
              refine ⟨68605749301244224952831417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45737166200829483301887611 68605749301244224952831417)
              ·
                refine ⟨51454311975933168714623563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68605749301244224952831417 51454311975933168714623563)
                ·
                  refine ⟨77181467963899753071935345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51454311975933168714623563 77181467963899753071935345)
                  ·
                    refine ⟨57886100972924814803951509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77181467963899753071935345 57886100972924814803951509)
                    ·
                      refine ⟨2713410983105850693935227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57886100972924814803951509 2713410983105850693935227)
                      ·
                        rfl

theorem cell23_5284349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_5284349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284349 prefixEnd_5284349 := by exact prefixLift 5284349
  have htrace : WordTrace (prefixWord ++ tailWord_5284349) baseStart_5284349 baseEnd_5284349 := by
    simpa [prefixWord, tailWord_5284349, baseEnd_5284349] using wordTrace_append hprefix tailTrace_5284349
  have hstable : (prefixWord ++ tailWord_5284349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284349).length < 2 ^ (prefixWord ++ tailWord_5284349).sum := by decide
  have hdescent : baseEnd_5284349 < baseStart_5284349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284397 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 6]
def baseStart_5284397 : Nat := 118140960795 + 5284397 * 2 ^ 59
def prefixEnd_5284397 : Nat := 4983230072969 + 3 ^ 40 * 5284397 * 2
def baseEnd_5284397 : Nat := 301492847797474056237223

theorem tailTrace_5284397 : CollatzResearch.WordTrace tailWord_5284397 prefixEnd_5284397 301492847797474056237223 := by
  unfold tailWord_5284397
  simp only [CollatzResearch.WordTrace]
  refine ⟨192737792636539647000763445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128491861757693098000508963 192737792636539647000763445)
  ·
    refine ⟨18069168059675591906321573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 192737792636539647000763445 18069168059675591906321573)
    ·
      refine ⟨3387969011189173482435295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18069168059675591906321573 3387969011189173482435295)
      ·
        refine ⟨5081953516783760223652943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3387969011189173482435295 5081953516783760223652943)
        ·
          refine ⟨7622930275175640335479415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081953516783760223652943 7622930275175640335479415)
          ·
            refine ⟨11434395412763460503219123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7622930275175640335479415 11434395412763460503219123)
            ·
              refine ⟨17151593119145190754828685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11434395412763460503219123 17151593119145190754828685)
              ·
                refine ⟨6431847419679446533060757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17151593119145190754828685 6431847419679446533060757)
                ·
                  refine ⟨301492847797474056237223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6431847419679446533060757 301492847797474056237223)
                  ·
                    rfl

theorem cell23_5284397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_5284397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284397 prefixEnd_5284397 := by exact prefixLift 5284397
  have htrace : WordTrace (prefixWord ++ tailWord_5284397) baseStart_5284397 baseEnd_5284397 := by
    simpa [prefixWord, tailWord_5284397, baseEnd_5284397] using wordTrace_append hprefix tailTrace_5284397
  have hstable : (prefixWord ++ tailWord_5284397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284397).length < 2 ^ (prefixWord ++ tailWord_5284397).sum := by decide
  have hdescent : baseEnd_5284397 < baseStart_5284397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284413 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_5284413 : Nat := 118140960795 + 5284413 * 2 ^ 59
def prefixEnd_5284413 : Nat := 4983230072969 + 3 ^ 40 * 5284413 * 2
def baseEnd_5284413 : Nat := 2713443845867738443534933

theorem tailTrace_5284413 : CollatzResearch.WordTrace tailWord_5284413 prefixEnd_5284413 2713443845867738443534933 := by
  unfold tailWord_5284413
  simp only [CollatzResearch.WordTrace]
  refine ⟨192738376204481681733345893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128492250802987787822230595 192738376204481681733345893)
  ·
    refine ⟨36138445538340315325002355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192738376204481681733345893 36138445538340315325002355)
    ·
      refine ⟨54207668307510472987503533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36138445538340315325002355 54207668307510472987503533)
      ·
        refine ⟨20327875615316427370313825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54207668307510472987503533 20327875615316427370313825)
        ·
          refine ⟨15245906711487320527735369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20327875615316427370313825 15245906711487320527735369)
          ·
            refine ⟨11434430033615490395801527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15245906711487320527735369 11434430033615490395801527)
            ·
              refine ⟨17151645050423235593702291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11434430033615490395801527 17151645050423235593702291)
              ·
                refine ⟨25727467575634853390553437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17151645050423235593702291 25727467575634853390553437)
                ·
                  refine ⟨9647800340863070021457539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25727467575634853390553437 9647800340863070021457539)
                  ·
                    refine ⟨14471700511294605032186309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9647800340863070021457539 14471700511294605032186309)
                    ·
                      refine ⟨2713443845867738443534933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14471700511294605032186309 2713443845867738443534933)
                      ·
                        rfl

theorem cell23_5284413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_5284413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284413 prefixEnd_5284413 := by exact prefixLift 5284413
  have htrace : WordTrace (prefixWord ++ tailWord_5284413) baseStart_5284413 baseEnd_5284413 := by
    simpa [prefixWord, tailWord_5284413, baseEnd_5284413] using wordTrace_append hprefix tailTrace_5284413
  have hstable : (prefixWord ++ tailWord_5284413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284413).length < 2 ^ (prefixWord ++ tailWord_5284413).sum := by decide
  have hdescent : baseEnd_5284413 < baseStart_5284413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284426 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_5284426 : Nat := 118140960795 + 5284426 * 2 ^ 59
def prefixEnd_5284426 : Nat := 4983230072969 + 3 ^ 40 * 5284426 * 2
def baseEnd_5284426 : Nat := 2713450521116246892672373

theorem tailTrace_5284426 : CollatzResearch.WordTrace tailWord_5284426 prefixEnd_5284426 2713450521116246892672373 := by
  unfold tailWord_5284426
  simp only [CollatzResearch.WordTrace]
  refine ⟨48184712588358646238392283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128492566902289723302379421 48184712588358646238392283)
  ·
    refine ⟨72277068882537969357588425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48184712588358646238392283 72277068882537969357588425)
    ·
      refine ⟨54207801661903477018191319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72277068882537969357588425 54207801661903477018191319)
      ·
        refine ⟨81311702492855215527286979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54207801661903477018191319 81311702492855215527286979)
        ·
          refine ⟨121967553739282823290930469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81311702492855215527286979 121967553739282823290930469)
          ·
            refine ⟨22868916326115529367049463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121967553739282823290930469 22868916326115529367049463)
            ·
              refine ⟨34303374489173294050574195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22868916326115529367049463 34303374489173294050574195)
              ·
                refine ⟨51455061733759941075861293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34303374489173294050574195 51455061733759941075861293)
                ·
                  refine ⟨19295648150159977903447985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51455061733759941075861293 19295648150159977903447985)
                  ·
                    refine ⟨14471736112619983427585989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19295648150159977903447985 14471736112619983427585989)
                    ·
                      refine ⟨2713450521116246892672373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14471736112619983427585989 2713450521116246892672373)
                      ·
                        rfl

theorem cell23_5284426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_5284426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284426 prefixEnd_5284426 := by exact prefixLift 5284426
  have htrace : WordTrace (prefixWord ++ tailWord_5284426) baseStart_5284426 baseEnd_5284426 := by
    simpa [prefixWord, tailWord_5284426, baseEnd_5284426] using wordTrace_append hprefix tailTrace_5284426
  have hstable : (prefixWord ++ tailWord_5284426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284426).length < 2 ^ (prefixWord ++ tailWord_5284426).sum := by decide
  have hdescent : baseEnd_5284426 < baseStart_5284426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284433 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_5284433 : Nat := 118140960795 + 5284433 * 2 ^ 59
def prefixEnd_5284433 : Nat := 4983230072969 + 3 ^ 40 * 5284433 * 2
def baseEnd_5284433 : Nat := 2713454115480828365284841

theorem tailTrace_5284433 : CollatzResearch.WordTrace tailWord_5284433 prefixEnd_5284433 2713454115480828365284841 := by
  unfold tailWord_5284433
  simp only [CollatzResearch.WordTrace]
  refine ⟨192739105664409225149073953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128492737109606150099382635 192739105664409225149073953)
  ·
    refine ⟨144554329248306918861805465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192739105664409225149073953 144554329248306918861805465)
    ·
      refine ⟨108415746936230189146354099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144554329248306918861805465 108415746936230189146354099)
      ·
        refine ⟨162623620404345283719531149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108415746936230189146354099 162623620404345283719531149)
        ·
          refine ⟨60983857651629481394824181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162623620404345283719531149 60983857651629481394824181)
          ·
            refine ⟨5717236654840263880764767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60983857651629481394824181 5717236654840263880764767)
            ·
              refine ⟨8575854982260395821147151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717236654840263880764767 8575854982260395821147151)
              ·
                refine ⟨12863782473390593731720727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8575854982260395821147151 12863782473390593731720727)
                ·
                  refine ⟨19295673710085890597581091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12863782473390593731720727 19295673710085890597581091)
                  ·
                    refine ⟨28943510565128835896371637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19295673710085890597581091 28943510565128835896371637)
                    ·
                      refine ⟨2713454115480828365284841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28943510565128835896371637 2713454115480828365284841)
                      ·
                        rfl

theorem cell23_5284433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_5284433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284433 prefixEnd_5284433 := by exact prefixLift 5284433
  have htrace : WordTrace (prefixWord ++ tailWord_5284433) baseStart_5284433 baseEnd_5284433 := by
    simpa [prefixWord, tailWord_5284433, baseEnd_5284433] using wordTrace_append hprefix tailTrace_5284433
  have hstable : (prefixWord ++ tailWord_5284433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284433).length < 2 ^ (prefixWord ++ tailWord_5284433).sum := by decide
  have hdescent : baseEnd_5284433 < baseStart_5284433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284453 : List Nat := [1, 3, 1, 3, 4, 2, 1, 8]
def baseStart_5284453 : Nat := 118140960795 + 5284453 * 2 ^ 59
def prefixEnd_5284453 : Nat := 4983230072969 + 3 ^ 40 * 5284453 * 2
def baseEnd_5284453 : Nat := 100498680929404381001287

theorem tailTrace_5284453 : CollatzResearch.WordTrace tailWord_5284453 prefixEnd_5284453 100498680929404381001287 := by
  unfold tailWord_5284453
  simp only [CollatzResearch.WordTrace]
  refine ⟨192739835124336768564802013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128493223416224512376534675 192739835124336768564802013)
  ·
    refine ⟨72277438171626288211800755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192739835124336768564802013 72277438171626288211800755)
    ·
      refine ⟨108416157257439432317701133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72277438171626288211800755 108416157257439432317701133)
      ·
        refine ⟨40656058971539787119137925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108416157257439432317701133 40656058971539787119137925)
        ·
          refine ⟨7623011057163710084838361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40656058971539787119137925 7623011057163710084838361)
          ·
            refine ⟨5717258292872782563628771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7623011057163710084838361 5717258292872782563628771)
            ·
              refine ⟨8575887439309173845443157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717258292872782563628771 8575887439309173845443157)
              ·
                refine ⟨100498680929404381001287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8575887439309173845443157 100498680929404381001287)
                ·
                  rfl

theorem cell23_5284453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 8].length) (baseStart_5284453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284453 prefixEnd_5284453 := by exact prefixLift 5284453
  have htrace : WordTrace (prefixWord ++ tailWord_5284453) baseStart_5284453 baseEnd_5284453 := by
    simpa [prefixWord, tailWord_5284453, baseEnd_5284453] using wordTrace_append hprefix tailTrace_5284453
  have hstable : (prefixWord ++ tailWord_5284453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284453).length < 2 ^ (prefixWord ++ tailWord_5284453).sum := by decide
  have hdescent : baseEnd_5284453 < baseStart_5284453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284470 : List Nat := [5, 1, 1, 2, 3, 1, 3, 7]
def baseStart_5284470 : Nat := 118140960795 + 5284470 * 2 ^ 59
def prefixEnd_5284470 : Nat := 4983230072969 + 3 ^ 40 * 5284470 * 2
def baseEnd_5284470 : Nat := 100499004232038693352673

theorem tailTrace_5284470 : CollatzResearch.WordTrace tailWord_5284470 prefixEnd_5284470 100499004232038693352673 := by
  unfold tailWord_5284470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046278447829698779260679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128493636776850120312113909 12046278447829698779260679)
  ·
    refine ⟨18069417671744548168891019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12046278447829698779260679 18069417671744548168891019)
    ·
      refine ⟨27104126507616822253336529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18069417671744548168891019 27104126507616822253336529)
      ·
        refine ⟨20328094880712616690002397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27104126507616822253336529 20328094880712616690002397)
        ·
          refine ⟨7623035580267231258750899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20328094880712616690002397 7623035580267231258750899)
          ·
            refine ⟨11434553370400846888126349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623035580267231258750899 11434553370400846888126349)
            ·
              refine ⟨4287957513900317583047381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11434553370400846888126349 4287957513900317583047381)
              ·
                refine ⟨100499004232038693352673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4287957513900317583047381 100499004232038693352673)
                ·
                  rfl

theorem cell23_5284470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_5284470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284470 prefixEnd_5284470 := by exact prefixLift 5284470
  have htrace : WordTrace (prefixWord ++ tailWord_5284470) baseStart_5284470 baseEnd_5284470 := by
    simpa [prefixWord, tailWord_5284470, baseEnd_5284470] using wordTrace_append hprefix tailTrace_5284470
  have hstable : (prefixWord ++ tailWord_5284470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284470).length < 2 ^ (prefixWord ++ tailWord_5284470).sum := by decide
  have hdescent : baseEnd_5284470 < baseStart_5284470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284590 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_5284590 : Nat := 118140960795 + 5284590 * 2 ^ 59
def prefixEnd_5284590 : Nat := 4983230072969 + 3 ^ 40 * 5284590 * 2
def baseEnd_5284590 : Nat := 904511577314528083673873

theorem tailTrace_5284590 : CollatzResearch.WordTrace tailWord_5284590 prefixEnd_5284590 904511577314528083673873 := by
  unfold tailWord_5284590
  simp only [CollatzResearch.WordTrace]
  refine ⟨24093103990605055120317403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128496554616560293975026149 24093103990605055120317403)
  ·
    refine ⟨36139655985907582680476105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24093103990605055120317403 36139655985907582680476105)
    ·
      refine ⟨27104741989430687010357079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36139655985907582680476105 27104741989430687010357079)
      ·
        refine ⟨40657112984146030515535619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27104741989430687010357079 40657112984146030515535619)
        ·
          refine ⟨60985669476219045773303429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40657112984146030515535619 60985669476219045773303429)
          ·
            refine ⟨11434813026791071082494393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60985669476219045773303429 11434813026791071082494393)
            ·
              refine ⟨8576109770093303311870795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11434813026791071082494393 8576109770093303311870795)
              ·
                refine ⟨12864164655139954967806193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8576109770093303311870795 12864164655139954967806193)
                ·
                  refine ⟨9648123491354966225854645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12864164655139954967806193 9648123491354966225854645)
                  ·
                    refine ⟨904511577314528083673873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9648123491354966225854645 904511577314528083673873)
                    ·
                      rfl

theorem cell23_5284590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_5284590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284590 prefixEnd_5284590 := by exact prefixLift 5284590
  have htrace : WordTrace (prefixWord ++ tailWord_5284590) baseStart_5284590 baseEnd_5284590 := by
    simpa [prefixWord, tailWord_5284590, baseEnd_5284590] using wordTrace_append hprefix tailTrace_5284590
  have hstable : (prefixWord ++ tailWord_5284590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284590).length < 2 ^ (prefixWord ++ tailWord_5284590).sum := by decide
  have hdescent : baseEnd_5284590 < baseStart_5284590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284644 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_5284644 : Nat := 118140960795 + 5284644 * 2 ^ 59
def prefixEnd_5284644 : Nat := 4983230072969 + 3 ^ 40 * 5284644 * 2
def baseEnd_5284644 : Nat := 2713562459898927039746371

theorem tailTrace_5284644 : CollatzResearch.WordTrace tailWord_5284644 prefixEnd_5284644 2713562459898927039746371 := by
  unfold tailWord_5284644
  simp only [CollatzResearch.WordTrace]
  refine ⟨96373400733322404092502493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128497867644429872123336657 96373400733322404092502493)
  ·
    refine ⟨36140025274995901534688435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96373400733322404092502493 36140025274995901534688435)
    ·
      refine ⟨54210037912493852302032653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36140025274995901534688435 54210037912493852302032653)
      ·
        refine ⟨20328764217185194613262245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54210037912493852302032653 20328764217185194613262245)
        ·
          refine ⟨3811643290722223989986671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20328764217185194613262245 3811643290722223989986671)
          ·
            refine ⟨5717464936083335984980007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811643290722223989986671 5717464936083335984980007)
            ·
              refine ⟨8576197404125003977470011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717464936083335984980007 8576197404125003977470011)
              ·
                refine ⟨12864296106187505966205017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8576197404125003977470011 12864296106187505966205017)
                ·
                  refine ⟨9648222079640629474653763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12864296106187505966205017 9648222079640629474653763)
                  ·
                    refine ⟨14472333119460944211980645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9648222079640629474653763 14472333119460944211980645)
                    ·
                      refine ⟨2713562459898927039746371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14472333119460944211980645 2713562459898927039746371)
                      ·
                        rfl

theorem cell23_5284644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_5284644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284644 prefixEnd_5284644 := by exact prefixLift 5284644
  have htrace : WordTrace (prefixWord ++ tailWord_5284644) baseStart_5284644 baseEnd_5284644 := by
    simpa [prefixWord, tailWord_5284644, baseEnd_5284644] using wordTrace_append hprefix tailTrace_5284644
  have hstable : (prefixWord ++ tailWord_5284644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284644).length < 2 ^ (prefixWord ++ tailWord_5284644).sum := by decide
  have hdescent : baseEnd_5284644 < baseStart_5284644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284654 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5284654 : Nat := 118140960795 + 5284654 * 2 ^ 59
def prefixEnd_5284654 : Nat := 4983230072969 + 3 ^ 40 * 5284654 * 2
def baseEnd_5284654 : Nat := 904522531568490666873775

theorem tailTrace_5284654 : CollatzResearch.WordTrace tailWord_5284654 prefixEnd_5284654 904522531568490666873775 := by
  unfold tailWord_5284654
  simp only [CollatzResearch.WordTrace]
  refine ⟨24093395774576072486608627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128498110797739053261912677 24093395774576072486608627)
  ·
    refine ⟨36140093661864108729912941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24093395774576072486608627 36140093661864108729912941)
    ·
      refine ⟨13552535123199040773717353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36140093661864108729912941 13552535123199040773717353)
      ·
        refine ⟨10164401342399280580288015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13552535123199040773717353 10164401342399280580288015)
        ·
          refine ⟨15246602013598920870432023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10164401342399280580288015 15246602013598920870432023)
          ·
            refine ⟨22869903020398381305648035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15246602013598920870432023 22869903020398381305648035)
            ·
              refine ⟨34304854530597571958472053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22869903020398381305648035 34304854530597571958472053)
              ·
                refine ⟨3216080112243522371106755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34304854530597571958472053 3216080112243522371106755)
                ·
                  refine ⟨4824120168365283556660133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216080112243522371106755 4824120168365283556660133)
                  ·
                    refine ⟨904522531568490666873775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824120168365283556660133 904522531568490666873775)
                    ·
                      rfl

theorem cell23_5284654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5284654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284654 prefixEnd_5284654 := by exact prefixLift 5284654
  have htrace : WordTrace (prefixWord ++ tailWord_5284654) baseStart_5284654 baseEnd_5284654 := by
    simpa [prefixWord, tailWord_5284654, baseEnd_5284654] using wordTrace_append hprefix tailTrace_5284654
  have hstable : (prefixWord ++ tailWord_5284654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284654).length < 2 ^ (prefixWord ++ tailWord_5284654).sum := by decide
  have hdescent : baseEnd_5284654 < baseStart_5284654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284703 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_5284703 : Nat := 118140960795 + 5284703 * 2 ^ 59
def prefixEnd_5284703 : Nat := 4983230072969 + 3 ^ 40 * 5284703 * 2
def baseEnd_5284703 : Nat := 2713592755257542308908599

theorem tailTrace_5284703 : CollatzResearch.WordTrace tailWord_5284703 prefixEnd_5284703 2713592755257542308908599 := by
  unfold tailWord_5284703
  simp only [CollatzResearch.WordTrace]
  refine ⟨192748953373431061261402763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128499302248954040840935175 192748953373431061261402763)
  ·
    refine ⟨289123430060146591892104145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192748953373431061261402763 289123430060146591892104145)
    ·
      refine ⟨216842572545109943919078109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289123430060146591892104145 216842572545109943919078109)
      ·
        refine ⟨81315964704416228969654291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216842572545109943919078109 81315964704416228969654291)
        ·
          refine ⟨121973947056624343454481437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81315964704416228969654291 121973947056624343454481437)
          ·
            refine ⟨45740230146234128795430539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121973947056624343454481437 45740230146234128795430539)
            ·
              refine ⟨68610345219351193193145809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45740230146234128795430539 68610345219351193193145809)
              ·
                refine ⟨51457758914513394894859357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68610345219351193193145809 51457758914513394894859357)
                ·
                  refine ⟨19296659592942523085572259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51457758914513394894859357 19296659592942523085572259)
                  ·
                    refine ⟨28944989389413784628358389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19296659592942523085572259 28944989389413784628358389)
                    ·
                      refine ⟨2713592755257542308908599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28944989389413784628358389 2713592755257542308908599)
                      ·
                        rfl

theorem cell23_5284703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_5284703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284703 prefixEnd_5284703 := by exact prefixLift 5284703
  have htrace : WordTrace (prefixWord ++ tailWord_5284703) baseStart_5284703 baseEnd_5284703 := by
    simpa [prefixWord, tailWord_5284703, baseEnd_5284703] using wordTrace_append hprefix tailTrace_5284703
  have hstable : (prefixWord ++ tailWord_5284703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284703).length < 2 ^ (prefixWord ++ tailWord_5284703).sum := by decide
  have hdescent : baseEnd_5284703 < baseStart_5284703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284711 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_5284711 : Nat := 118140960795 + 5284711 * 2 ^ 59
def prefixEnd_5284711 : Nat := 4983230072969 + 3 ^ 40 * 5284711 * 2
def baseEnd_5284711 : Nat := 2713596863102778277608563

theorem tailTrace_5284711 : CollatzResearch.WordTrace tailWord_5284711 prefixEnd_5284711 2713596863102778277608563 := by
  unfold tailWord_5284711
  simp only [CollatzResearch.WordTrace]
  refine ⟨192749245157402078627693987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128499496771601385751795991 192749245157402078627693987)
  ·
    refine ⟨289123867736103117941540981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192749245157402078627693987 289123867736103117941540981)
    ·
      refine ⟨27105362600259667307019467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 289123867736103117941540981 27105362600259667307019467)
      ·
        refine ⟨40658043900389500960529201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27105362600259667307019467 40658043900389500960529201)
        ·
          refine ⟨30493532925292125720396901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40658043900389500960529201 30493532925292125720396901)
          ·
            refine ⟨5717537423492273572574419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30493532925292125720396901 5717537423492273572574419)
            ·
              refine ⟨8576306135238410358861629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717537423492273572574419 8576306135238410358861629)
              ·
                refine ⟨3216114800714403884573111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8576306135238410358861629 3216114800714403884573111)
                ·
                  refine ⟨4824172201071605826859667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216114800714403884573111 4824172201071605826859667)
                  ·
                    refine ⟨7236258301607408740289501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4824172201071605826859667 7236258301607408740289501)
                    ·
                      refine ⟨2713596863102778277608563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236258301607408740289501 2713596863102778277608563)
                      ·
                        rfl

theorem cell23_5284711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_5284711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284711 prefixEnd_5284711 := by exact prefixLift 5284711
  have htrace : WordTrace (prefixWord ++ tailWord_5284711) baseStart_5284711 baseEnd_5284711 := by
    simpa [prefixWord, tailWord_5284711, baseEnd_5284711] using wordTrace_append hprefix tailTrace_5284711
  have hstable : (prefixWord ++ tailWord_5284711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284711).length < 2 ^ (prefixWord ++ tailWord_5284711).sum := by decide
  have hdescent : baseEnd_5284711 < baseStart_5284711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284744 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 2, 4]
def baseStart_5284744 : Nat := 118140960795 + 5284744 * 2 ^ 59
def prefixEnd_5284744 : Nat := 4983230072969 + 3 ^ 40 * 5284744 * 2
def baseEnd_5284744 : Nat := 904537935988125549498637

theorem tailTrace_5284744 : CollatzResearch.WordTrace tailWord_5284744 prefixEnd_5284744 904537935988125549498637 := by
  unfold tailWord_5284744
  simp only [CollatzResearch.WordTrace]
  refine ⟨96375224383141262631822643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128500299177521683509096857 96375224383141262631822643)
  ·
    refine ⟨144562836574711893947733965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96375224383141262631822643 144562836574711893947733965)
    ·
      refine ⟨54211063715516960230400237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144562836574711893947733965 54211063715516960230400237)
      ·
        refine ⟨20329148893318860086400089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54211063715516960230400237 20329148893318860086400089)
        ·
          refine ⟨15246861669989145064800067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20329148893318860086400089 15246861669989145064800067)
          ·
            refine ⟨22870292504983717597200101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15246861669989145064800067 22870292504983717597200101)
            ·
              refine ⟨4288179844684447049475019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22870292504983717597200101 4288179844684447049475019)
              ·
                refine ⟨6432269767026670574212529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288179844684447049475019 6432269767026670574212529)
                ·
                  refine ⟨4824202325270002930659397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6432269767026670574212529 4824202325270002930659397)
                  ·
                    refine ⟨904537935988125549498637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824202325270002930659397 904537935988125549498637)
                    ·
                      rfl

theorem cell23_5284744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_5284744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284744 prefixEnd_5284744 := by exact prefixLift 5284744
  have htrace : WordTrace (prefixWord ++ tailWord_5284744) baseStart_5284744 baseEnd_5284744 := by
    simpa [prefixWord, tailWord_5284744, baseEnd_5284744] using wordTrace_append hprefix tailTrace_5284744
  have hstable : (prefixWord ++ tailWord_5284744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284744).length < 2 ^ (prefixWord ++ tailWord_5284744).sum := by decide
  have hdescent : baseEnd_5284744 < baseStart_5284744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284754 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5284754 : Nat := 118140960795 + 5284754 * 2 ^ 59
def prefixEnd_5284754 : Nat := 4983230072969 + 3 ^ 40 * 5284754 * 2
def baseEnd_5284754 : Nat := 2713618942770921609370865

theorem tailTrace_5284754 : CollatzResearch.WordTrace tailWord_5284754 prefixEnd_5284754 2713618942770921609370865 := by
  unfold tailWord_5284754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48187703374061574242877329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128500542330830864647672877 48187703374061574242877329)
  ·
    refine ⟨36140777530546180682157997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48187703374061574242877329 36140777530546180682157997)
    ·
      refine ⟨13552791573954817755809249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36140777530546180682157997 13552791573954817755809249)
      ·
        refine ⟨10164593680466113316856937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13552791573954817755809249 10164593680466113316856937)
        ·
          refine ⟨7623445260349584987642703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10164593680466113316856937 7623445260349584987642703)
          ·
            refine ⟨11435167890524377481464055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623445260349584987642703 11435167890524377481464055)
            ·
              refine ⟨17152751835786566222196083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435167890524377481464055 17152751835786566222196083)
              ·
                refine ⟨25729127753679849333294125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17152751835786566222196083 25729127753679849333294125)
                ·
                  refine ⟨9648422907629943499985297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25729127753679849333294125 9648422907629943499985297)
                  ·
                    refine ⟨7236317180722457624988973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9648422907629943499985297 7236317180722457624988973)
                    ·
                      refine ⟨2713618942770921609370865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236317180722457624988973 2713618942770921609370865)
                      ·
                        rfl

theorem cell23_5284754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5284754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284754 prefixEnd_5284754 := by exact prefixLift 5284754
  have htrace : WordTrace (prefixWord ++ tailWord_5284754) baseStart_5284754 baseEnd_5284754 := by
    simpa [prefixWord, tailWord_5284754, baseEnd_5284754] using wordTrace_append hprefix tailTrace_5284754
  have hstable : (prefixWord ++ tailWord_5284754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284754).length < 2 ^ (prefixWord ++ tailWord_5284754).sum := by decide
  have hdescent : baseEnd_5284754 < baseStart_5284754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284767 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5284767 : Nat := 118140960795 + 5284767 * 2 ^ 59
def prefixEnd_5284767 : Nat := 4983230072969 + 3 ^ 40 * 5284767 * 2
def baseEnd_5284767 : Nat := 2713625618019430058508305

theorem tailTrace_5284767 : CollatzResearch.WordTrace tailWord_5284767 prefixEnd_5284767 2713625618019430058508305 := by
  unfold tailWord_5284767
  simp only [CollatzResearch.WordTrace]
  refine ⟨192751287645199200191732555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128500858430132800127821703 192751287645199200191732555)
  ·
    refine ⟨289126931467798800287598833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192751287645199200191732555 289126931467798800287598833)
    ·
      refine ⟨216845198600849100215699125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289126931467798800287598833 216845198600849100215699125)
      ·
        refine ⟨20329237368829603145221793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 216845198600849100215699125 20329237368829603145221793)
        ·
          refine ⟨15246928026622202358916345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20329237368829603145221793 15246928026622202358916345)
          ·
            refine ⟨11435196019966651769187259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15246928026622202358916345 11435196019966651769187259)
            ·
              refine ⟨17152794029949977653780889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435196019966651769187259 17152794029949977653780889)
              ·
                refine ⟨12864595522462483240335667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17152794029949977653780889 12864595522462483240335667)
                ·
                  refine ⟨19296893283693724860503501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12864595522462483240335667 19296893283693724860503501)
                  ·
                    refine ⟨7236334981385146822688813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19296893283693724860503501 7236334981385146822688813)
                    ·
                      refine ⟨2713625618019430058508305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236334981385146822688813 2713625618019430058508305)
                      ·
                        rfl

theorem cell23_5284767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5284767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284767 prefixEnd_5284767 := by exact prefixLift 5284767
  have htrace : WordTrace (prefixWord ++ tailWord_5284767) baseStart_5284767 baseEnd_5284767 := by
    simpa [prefixWord, tailWord_5284767, baseEnd_5284767] using wordTrace_append hprefix tailTrace_5284767
  have hstable : (prefixWord ++ tailWord_5284767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284767).length < 2 ^ (prefixWord ++ tailWord_5284767).sum := by decide
  have hdescent : baseEnd_5284767 < baseStart_5284767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284785 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 1, 2, 2]
def baseStart_5284785 : Nat := 118140960795 + 5284785 * 2 ^ 59
def prefixEnd_5284785 : Nat := 4983230072969 + 3 ^ 40 * 5284785 * 2
def baseEnd_5284785 : Nat := 2713634860671210988083223

theorem tailTrace_5284785 : CollatzResearch.WordTrace tailWord_5284785 prefixEnd_5284785 2713634860671210988083223 := by
  unfold tailWord_5284785
  simp only [CollatzResearch.WordTrace]
  refine ⟨192751944159133989265887809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128501296106089326177258539 192751944159133989265887809)
  ·
    refine ⟨144563958119350491949415857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192751944159133989265887809 144563958119350491949415857)
    ·
      refine ⟨108422968589512868962061893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144563958119350491949415857 108422968589512868962061893)
      ·
        refine ⟨20329306610533662930386605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108422968589512868962061893 20329306610533662930386605)
        ·
          refine ⟨7623489978950123598894977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20329306610533662930386605 7623489978950123598894977)
          ·
            refine ⟨5717617484212592699171233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7623489978950123598894977 5717617484212592699171233)
            ·
              refine ⟨4288213113159444524378425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5717617484212592699171233 4288213113159444524378425)
              ·
                refine ⟨3216159834869583393283819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4288213113159444524378425 3216159834869583393283819)
                ·
                  refine ⟨4824239752304375089925729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216159834869583393283819 4824239752304375089925729)
                  ·
                    refine ⟨3618179814228281317444297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4824239752304375089925729 3618179814228281317444297)
                    ·
                      refine ⟨2713634860671210988083223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618179814228281317444297 2713634860671210988083223)
                      ·
                        rfl

theorem cell23_5284785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_5284785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284785 prefixEnd_5284785 := by exact prefixLift 5284785
  have htrace : WordTrace (prefixWord ++ tailWord_5284785) baseStart_5284785 baseEnd_5284785 := by
    simpa [prefixWord, tailWord_5284785, baseEnd_5284785] using wordTrace_append hprefix tailTrace_5284785
  have hstable : (prefixWord ++ tailWord_5284785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284785).length < 2 ^ (prefixWord ++ tailWord_5284785).sum := by decide
  have hdescent : baseEnd_5284785 < baseStart_5284785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284800 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_5284800 : Nat := 118140960795 + 5284800 * 2 ^ 59
def prefixEnd_5284800 : Nat := 4983230072969 + 3 ^ 40 * 5284800 * 2
def baseEnd_5284800 : Nat := 904547520960342809798551

theorem tailTrace_5284800 : CollatzResearch.WordTrace tailWord_5284800 prefixEnd_5284800 904547520960342809798551 := by
  unfold tailWord_5284800
  simp only [CollatzResearch.WordTrace]
  refine ⟨96376245627039823413841927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128501660836053097885122569 96376245627039823413841927)
  ·
    refine ⟨144564368440559735120762891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96376245627039823413841927 144564368440559735120762891)
    ·
      refine ⟨216846552660839602681144337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144564368440559735120762891 216846552660839602681144337)
      ·
        refine ⟨162634914495629702010858253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216846552660839602681144337 162634914495629702010858253)
        ·
          refine ⟨60988092935861138254071845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162634914495629702010858253 60988092935861138254071845)
          ·
            refine ⟨11435267425473963422638471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60988092935861138254071845 11435267425473963422638471)
            ·
              refine ⟨17152901138210945133957707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435267425473963422638471 17152901138210945133957707)
              ·
                refine ⟨25729351707316417700936561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17152901138210945133957707 25729351707316417700936561)
                ·
                  refine ⟨19297013780487313275702421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25729351707316417700936561 19297013780487313275702421)
                  ·
                    refine ⟨904547520960342809798551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19297013780487313275702421 904547520960342809798551)
                    ·
                      rfl

theorem cell23_5284800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_5284800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284800 prefixEnd_5284800 := by exact prefixLift 5284800
  have htrace : WordTrace (prefixWord ++ tailWord_5284800) baseStart_5284800 baseEnd_5284800 := by
    simpa [prefixWord, tailWord_5284800, baseEnd_5284800] using wordTrace_append hprefix tailTrace_5284800
  have hstable : (prefixWord ++ tailWord_5284800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284800).length < 2 ^ (prefixWord ++ tailWord_5284800).sum := by decide
  have hdescent : baseEnd_5284800 < baseStart_5284800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284803 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_5284803 : Nat := 118140960795 + 5284803 * 2 ^ 59
def prefixEnd_5284803 : Nat := 4983230072969 + 3 ^ 40 * 5284803 * 2
def baseEnd_5284803 : Nat := 2713644103322991917658139

theorem tailTrace_5284803 : CollatzResearch.WordTrace tailWord_5284803 prefixEnd_5284803 2713644103322991917658139 := by
  unfold tailWord_5284803
  simp only [CollatzResearch.WordTrace]
  refine ⟨192752600673068778340043063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128501733782045852226695375 192752600673068778340043063)
  ·
    refine ⟨289128901009603167510064595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192752600673068778340043063 289128901009603167510064595)
    ·
      refine ⟨433693351514404751265096893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289128901009603167510064595 433693351514404751265096893)
      ·
        refine ⟨162635006817901781724411335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433693351514404751265096893 162635006817901781724411335)
        ·
          refine ⟨243952510226852672586617003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162635006817901781724411335 243952510226852672586617003)
          ·
            refine ⟨365928765340279008879925505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243952510226852672586617003 365928765340279008879925505)
            ·
              refine ⟨274446574005209256659944129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365928765340279008879925505 274446574005209256659944129)
              ·
                refine ⟨205834930503906942494958097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274446574005209256659944129 205834930503906942494958097)
                ·
                  refine ⟨154376197877930206871218573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205834930503906942494958097 154376197877930206871218573)
                  ·
                    refine ⟨57891074204223827576706965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154376197877930206871218573 57891074204223827576706965)
                    ·
                      refine ⟨2713644103322991917658139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57891074204223827576706965 2713644103322991917658139)
                      ·
                        rfl

theorem cell23_5284803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_5284803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284803 prefixEnd_5284803 := by exact prefixLift 5284803
  have htrace : WordTrace (prefixWord ++ tailWord_5284803) baseStart_5284803 baseEnd_5284803 := by
    simpa [prefixWord, tailWord_5284803, baseEnd_5284803] using wordTrace_append hprefix tailTrace_5284803
  have hstable : (prefixWord ++ tailWord_5284803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284803).length < 2 ^ (prefixWord ++ tailWord_5284803).sum := by decide
  have hdescent : baseEnd_5284803 < baseStart_5284803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284807 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_5284807 : Nat := 118140960795 + 5284807 * 2 ^ 59
def prefixEnd_5284807 : Nat := 4983230072969 + 3 ^ 40 * 5284807 * 2
def baseEnd_5284807 : Nat := 2713646157245609902008121

theorem tailTrace_5284807 : CollatzResearch.WordTrace tailWord_5284807 prefixEnd_5284807 2713646157245609902008121 := by
  unfold tailWord_5284807
  simp only [CollatzResearch.WordTrace]
  refine ⟨192752746565054287023188675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128501831043369524682125783 192752746565054287023188675)
  ·
    refine ⟨289129119847581430534783013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192752746565054287023188675 289129119847581430534783013)
    ·
      refine ⟨54211709971421518225271815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 289129119847581430534783013 54211709971421518225271815)
      ·
        refine ⟨81317564957132277337907723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54211709971421518225271815 81317564957132277337907723)
        ·
          refine ⟨121976347435698416006861585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81317564957132277337907723 121976347435698416006861585)
          ·
            refine ⟨91482260576773812005146189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121976347435698416006861585 91482260576773812005146189)
            ·
              refine ⟨34305847716290179501929821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91482260576773812005146189 34305847716290179501929821)
              ·
                refine ⟨12864692893608817313223683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34305847716290179501929821 12864692893608817313223683)
                ·
                  refine ⟨19297039340413225969835525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12864692893608817313223683 19297039340413225969835525)
                  ·
                    refine ⟨3618194876327479869344161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19297039340413225969835525 3618194876327479869344161)
                    ·
                      refine ⟨2713646157245609902008121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618194876327479869344161 2713646157245609902008121)
                      ·
                        rfl

theorem cell23_5284807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_5284807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284807 prefixEnd_5284807 := by exact prefixLift 5284807
  have htrace : WordTrace (prefixWord ++ tailWord_5284807) baseStart_5284807 baseEnd_5284807 := by
    simpa [prefixWord, tailWord_5284807, baseEnd_5284807] using wordTrace_append hprefix tailTrace_5284807
  have hstable : (prefixWord ++ tailWord_5284807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284807).length < 2 ^ (prefixWord ++ tailWord_5284807).sum := by decide
  have hdescent : baseEnd_5284807 < baseStart_5284807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284810 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_5284810 : Nat := 118140960795 + 5284810 * 2 ^ 59
def prefixEnd_5284810 : Nat := 4983230072969 + 3 ^ 40 * 5284810 * 2
def baseEnd_5284810 : Nat := 2713647697687573390270607

theorem tailTrace_5284810 : CollatzResearch.WordTrace tailWord_5284810 prefixEnd_5284810 2713647697687573390270607 := by
  unfold tailWord_5284810
  simp only [CollatzResearch.WordTrace]
  refine ⟨48188213996010854633886971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128501903989362279023698589 48188213996010854633886971)
  ·
    refine ⟨72282320994016281950830457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48188213996010854633886971 72282320994016281950830457)
    ·
      refine ⟨54211740745512211463122843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72282320994016281950830457 54211740745512211463122843)
      ·
        refine ⟨81317611118268317194684265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54211740745512211463122843 81317611118268317194684265)
        ·
          refine ⟨60988208338701237896013199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81317611118268317194684265 60988208338701237896013199)
          ·
            refine ⟨91482312508051856844019799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60988208338701237896013199 91482312508051856844019799)
            ·
              refine ⟨137223468762077785266029699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91482312508051856844019799 137223468762077785266029699)
              ·
                refine ⟨205835203143116677899044549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137223468762077785266029699 205835203143116677899044549)
                ·
                  refine ⟨38594100589334377106070853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 205835203143116677899044549 38594100589334377106070853)
                  ·
                    refine ⟨7236393860500195707388285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38594100589334377106070853 7236393860500195707388285)
                    ·
                      refine ⟨2713647697687573390270607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236393860500195707388285 2713647697687573390270607)
                      ·
                        rfl

theorem cell23_5284810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_5284810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284810 prefixEnd_5284810 := by exact prefixLift 5284810
  have htrace : WordTrace (prefixWord ++ tailWord_5284810) baseStart_5284810 baseEnd_5284810 := by
    simpa [prefixWord, tailWord_5284810, baseEnd_5284810] using wordTrace_append hprefix tailTrace_5284810
  have hstable : (prefixWord ++ tailWord_5284810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284810).length < 2 ^ (prefixWord ++ tailWord_5284810).sum := by decide
  have hdescent : baseEnd_5284810 < baseStart_5284810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284847 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 5]
def baseStart_5284847 : Nat := 118140960795 + 5284847 * 2 ^ 59
def prefixEnd_5284847 : Nat := 4983230072969 + 3 ^ 40 * 5284847 * 2
def baseEnd_5284847 : Nat := 301518521830198860611993

theorem tailTrace_5284847 : CollatzResearch.WordTrace tailWord_5284847 prefixEnd_5284847 301518521830198860611993 := by
  unfold tailWord_5284847
  simp only [CollatzResearch.WordTrace]
  refine ⟨192754205484909373854644795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128502803656606249236429863 192754205484909373854644795)
  ·
    refine ⟨289131308227364060781967193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192754205484909373854644795 289131308227364060781967193)
    ·
      refine ⟨216848481170523045586475395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289131308227364060781967193 216848481170523045586475395)
      ·
        refine ⟨325272721755784568379713093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216848481170523045586475395 325272721755784568379713093)
        ·
          refine ⟨60988635329209606571196205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325272721755784568379713093 60988635329209606571196205)
          ·
            refine ⟨22870738248453602464198577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60988635329209606571196205 22870738248453602464198577)
            ·
              refine ⟨17153053686340201848148933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22870738248453602464198577 17153053686340201848148933)
              ·
                refine ⟨3216197566188787846527925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17153053686340201848148933 3216197566188787846527925)
                ·
                  refine ⟨301518521830198860611993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3216197566188787846527925 301518521830198860611993)
                  ·
                    rfl

theorem cell23_5284847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 5].length) (baseStart_5284847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284847 prefixEnd_5284847 := by exact prefixLift 5284847
  have htrace : WordTrace (prefixWord ++ tailWord_5284847) baseStart_5284847 baseEnd_5284847 := by
    simpa [prefixWord, tailWord_5284847, baseEnd_5284847] using wordTrace_append hprefix tailTrace_5284847
  have hstable : (prefixWord ++ tailWord_5284847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284847).length < 2 ^ (prefixWord ++ tailWord_5284847).sum := by decide
  have hdescent : baseEnd_5284847 < baseStart_5284847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284852 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5284852 : Nat := 118140960795 + 5284852 * 2 ^ 59
def prefixEnd_5284852 : Nat := 4983230072969 + 3 ^ 40 * 5284852 * 2
def baseEnd_5284852 : Nat := 2713669263875062225945415

theorem tailTrace_5284852 : CollatzResearch.WordTrace tailWord_5284852 prefixEnd_5284852 2713669263875062225945415 := by
  unfold tailWord_5284852
  simp only [CollatzResearch.WordTrace]
  refine ⟨96377193924945629854288405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128502925233260839805717873 96377193924945629854288405)
  ·
    refine ⟨4517680965231826399419769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96377193924945629854288405 4517680965231826399419769)
    ·
      refine ⟨3388260723923869799564827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4517680965231826399419769 3388260723923869799564827)
      ·
        refine ⟨5082391085885804699347241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3388260723923869799564827 5082391085885804699347241)
        ·
          refine ⟨3811793314414353524510431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5082391085885804699347241 3811793314414353524510431)
          ·
            refine ⟨5717689971621530286765647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811793314414353524510431 5717689971621530286765647)
            ·
              refine ⟨8576534957432295430148471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717689971621530286765647 8576534957432295430148471)
              ·
                refine ⟨12864802436148443145222707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8576534957432295430148471 12864802436148443145222707)
                ·
                  refine ⟨19297203654222664717834061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12864802436148443145222707 19297203654222664717834061)
                  ·
                    refine ⟨7236451370333499269187773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19297203654222664717834061 7236451370333499269187773)
                    ·
                      refine ⟨2713669263875062225945415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236451370333499269187773 2713669263875062225945415)
                      ·
                        rfl

theorem cell23_5284852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5284852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284852 prefixEnd_5284852 := by exact prefixLift 5284852
  have htrace : WordTrace (prefixWord ++ tailWord_5284852) baseStart_5284852 baseEnd_5284852 := by
    simpa [prefixWord, tailWord_5284852, baseEnd_5284852] using wordTrace_append hprefix tailTrace_5284852
  have hstable : (prefixWord ++ tailWord_5284852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284852).length < 2 ^ (prefixWord ++ tailWord_5284852).sum := by decide
  have hdescent : baseEnd_5284852 < baseStart_5284852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284860 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_5284860 : Nat := 118140960795 + 5284860 * 2 ^ 59
def prefixEnd_5284860 : Nat := 4983230072969 + 3 ^ 40 * 5284860 * 2
def baseEnd_5284860 : Nat := 904557790573432731548459

theorem tailTrace_5284860 : CollatzResearch.WordTrace tailWord_5284860 prefixEnd_5284860 904557790573432731548459 := by
  unfold tailWord_5284860
  simp only [CollatzResearch.WordTrace]
  refine ⟨96377339816931138537434017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128503119755908184716578689 96377339816931138537434017)
  ·
    refine ⟨72283004862698353903075513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96377339816931138537434017 72283004862698353903075513)
    ·
      refine ⟨54212253647023765427306635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72283004862698353903075513 54212253647023765427306635)
      ·
        refine ⟨81318380470535648140959953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54212253647023765427306635 81318380470535648140959953)
        ·
          refine ⟨60988785352901736105719965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81318380470535648140959953 60988785352901736105719965)
          ·
            refine ⟨22870794507338151039644987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60988785352901736105719965 22870794507338151039644987)
            ·
              refine ⟨34306191761007226559467481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22870794507338151039644987 34306191761007226559467481)
              ·
                refine ⟨25729643820755419919600611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34306191761007226559467481 25729643820755419919600611)
                ·
                  refine ⟨38594465731133129879400917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25729643820755419919600611 38594465731133129879400917)
                  ·
                    refine ⟨904557790573432731548459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38594465731133129879400917 904557790573432731548459)
                    ·
                      rfl

theorem cell23_5284860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_5284860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284860 prefixEnd_5284860 := by exact prefixLift 5284860
  have htrace : WordTrace (prefixWord ++ tailWord_5284860) baseStart_5284860 baseEnd_5284860 := by
    simpa [prefixWord, tailWord_5284860, baseEnd_5284860] using wordTrace_append hprefix tailTrace_5284860
  have hstable : (prefixWord ++ tailWord_5284860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284860).length < 2 ^ (prefixWord ++ tailWord_5284860).sum := by decide
  have hdescent : baseEnd_5284860 < baseStart_5284860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284897 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_5284897 : Nat := 118140960795 + 5284897 * 2 ^ 59
def prefixEnd_5284897 : Nat := 4983230072969 + 3 ^ 40 * 5284897 * 2
def baseEnd_5284897 : Nat := 2713692370504514549882707

theorem tailTrace_5284897 : CollatzResearch.WordTrace tailWord_5284897 prefixEnd_5284897 2713692370504514549882707 := by
  unfold tailWord_5284897
  simp only [CollatzResearch.WordTrace]
  refine ⟨192756029134728232393964945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128504019423152154929309963 192756029134728232393964945)
  ·
    refine ⟨144567021851046174295473709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192756029134728232393964945 144567021851046174295473709)
    ·
      refine ⟨54212633194142315360802641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144567021851046174295473709 54212633194142315360802641)
      ·
        refine ⟨40659474895606736520601981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54212633194142315360802641 40659474895606736520601981)
        ·
          refine ⟨15247303085852526195225743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40659474895606736520601981 15247303085852526195225743)
          ·
            refine ⟨22870954628778789292838615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15247303085852526195225743 22870954628778789292838615)
            ·
              refine ⟨34306431943168183939257923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22870954628778789292838615 34306431943168183939257923)
              ·
                refine ⟨51459647914752275908886885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34306431943168183939257923 51459647914752275908886885)
                ·
                  refine ⟨9648683984016051732916291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51459647914752275908886885 9648683984016051732916291)
                  ·
                    refine ⟨14473025976024077599374437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9648683984016051732916291 14473025976024077599374437)
                    ·
                      refine ⟨2713692370504514549882707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14473025976024077599374437 2713692370504514549882707)
                      ·
                        rfl

theorem cell23_5284897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_5284897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284897 prefixEnd_5284897 := by exact prefixLift 5284897
  have htrace : WordTrace (prefixWord ++ tailWord_5284897) baseStart_5284897 baseEnd_5284897 := by
    simpa [prefixWord, tailWord_5284897, baseEnd_5284897] using wordTrace_append hprefix tailTrace_5284897
  have hstable : (prefixWord ++ tailWord_5284897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284897).length < 2 ^ (prefixWord ++ tailWord_5284897).sum := by decide
  have hdescent : baseEnd_5284897 < baseStart_5284897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284917 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_5284917 : Nat := 118140960795 + 5284917 * 2 ^ 59
def prefixEnd_5284917 : Nat := 4983230072969 + 3 ^ 40 * 5284917 * 2
def baseEnd_5284917 : Nat := 2713702640117604471632615

theorem tailTrace_5284917 : CollatzResearch.WordTrace tailWord_5284917 prefixEnd_5284917 2713702640117604471632615 := by
  unfold tailWord_5284917
  simp only [CollatzResearch.WordTrace]
  refine ⟨192756758594655775809693005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128504505729770517206462003 192756758594655775809693005)
  ·
    refine ⟨72283784472995915928634877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192756758594655775809693005 72283784472995915928634877)
    ·
      refine ⟨27106419177373468473238079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72283784472995915928634877 27106419177373468473238079)
      ·
        refine ⟨40659628766060202709857119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27106419177373468473238079 40659628766060202709857119)
        ·
          refine ⟨60989443149090304064785679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40659628766060202709857119 60989443149090304064785679)
          ·
            refine ⟨91484164723635456097178519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60989443149090304064785679 91484164723635456097178519)
            ·
              refine ⟨137226247085453184145767779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91484164723635456097178519 137226247085453184145767779)
              ·
                refine ⟨205839370628179776218651669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137226247085453184145767779 205839370628179776218651669)
                ·
                  refine ⟨9648720498195927010249297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 205839370628179776218651669 9648720498195927010249297)
                  ·
                    refine ⟨7236540373646945257686973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9648720498195927010249297 7236540373646945257686973)
                    ·
                      refine ⟨2713702640117604471632615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236540373646945257686973 2713702640117604471632615)
                      ·
                        rfl

theorem cell23_5284917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_5284917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284917 prefixEnd_5284917 := by exact prefixLift 5284917
  have htrace : WordTrace (prefixWord ++ tailWord_5284917) baseStart_5284917 baseEnd_5284917 := by
    simpa [prefixWord, tailWord_5284917, baseEnd_5284917] using wordTrace_append hprefix tailTrace_5284917
  have hstable : (prefixWord ++ tailWord_5284917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284917).length < 2 ^ (prefixWord ++ tailWord_5284917).sum := by decide
  have hdescent : baseEnd_5284917 < baseStart_5284917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284940 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5284940 : Nat := 118140960795 + 5284940 * 2 ^ 59
def prefixEnd_5284940 : Nat := 4983230072969 + 3 ^ 40 * 5284940 * 2
def baseEnd_5284940 : Nat := 2713714450172657881645009

theorem tailTrace_5284940 : CollatzResearch.WordTrace tailWord_5284940 prefixEnd_5284940 2713714450172657881645009 := by
  unfold tailWord_5284940
  simp only [CollatzResearch.WordTrace]
  refine ⟨96378798736786225368890137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128505064982381633825186849 96378798736786225368890137)
  ·
    refine ⟨72284099052589669026667603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96378798736786225368890137 72284099052589669026667603)
    ·
      refine ⟨108426148578884503540001405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72284099052589669026667603 108426148578884503540001405)
      ·
        refine ⟨40659805717081688827500527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108426148578884503540001405 40659805717081688827500527)
        ·
          refine ⟨60989708575622533241250791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40659805717081688827500527 60989708575622533241250791)
          ·
            refine ⟨91484562863433799861876187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60989708575622533241250791 91484562863433799861876187)
            ·
              refine ⟨137226844295150699792814281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91484562863433799861876187 137226844295150699792814281)
              ·
                refine ⟨102920133221363024844610711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137226844295150699792814281 102920133221363024844610711)
                ·
                  refine ⟨154380199832044537266916067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102920133221363024844610711 154380199832044537266916067)
                  ·
                    refine ⟨231570299748066805900374101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154380199832044537266916067 231570299748066805900374101)
                    ·
                      refine ⟨2713714450172657881645009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 231570299748066805900374101 2713714450172657881645009)
                      ·
                        rfl

theorem cell23_5284940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5284940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284940 prefixEnd_5284940 := by exact prefixLift 5284940
  have htrace : WordTrace (prefixWord ++ tailWord_5284940) baseStart_5284940 baseEnd_5284940 := by
    simpa [prefixWord, tailWord_5284940, baseEnd_5284940] using wordTrace_append hprefix tailTrace_5284940
  have hstable : (prefixWord ++ tailWord_5284940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284940).length < 2 ^ (prefixWord ++ tailWord_5284940).sum := by decide
  have hdescent : baseEnd_5284940 < baseStart_5284940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284964 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_5284964 : Nat := 118140960795 + 5284964 * 2 ^ 59
def prefixEnd_5284964 : Nat := 4983230072969 + 3 ^ 40 * 5284964 * 2
def baseEnd_5284964 : Nat := 2713726773708365787744899

theorem tailTrace_5284964 : CollatzResearch.WordTrace tailWord_5284964 prefixEnd_5284964 2713726773708365787744899 := by
  unfold tailWord_5284964
  simp only [CollatzResearch.WordTrace]
  refine ⟨96379236412742751418326973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128505648550323668557769297 96379236412742751418326973)
  ·
    refine ⟨36142213654778531781872615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96379236412742751418326973 36142213654778531781872615)
    ·
      refine ⟨54213320482167797672808923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36142213654778531781872615 54213320482167797672808923)
      ·
        refine ⟨81319980723251696509213385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54213320482167797672808923 81319980723251696509213385)
        ·
          refine ⟨60989985542438772381910039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81319980723251696509213385 60989985542438772381910039)
          ·
            refine ⟨91484978313658158572865059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60989985542438772381910039 91484978313658158572865059)
            ·
              refine ⟨137227467470487237859297589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91484978313658158572865059 137227467470487237859297589)
              ·
                refine ⟨12865075075358178549309149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137227467470487237859297589 12865075075358178549309149)
                ·
                  refine ⟨4824403153259316955990931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12865075075358178549309149 4824403153259316955990931)
                  ·
                    refine ⟨7236604729888975433986397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4824403153259316955990931 7236604729888975433986397)
                    ·
                      refine ⟨2713726773708365787744899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236604729888975433986397 2713726773708365787744899)
                      ·
                        rfl

theorem cell23_5284964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_5284964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284964 prefixEnd_5284964 := by exact prefixLift 5284964
  have htrace : WordTrace (prefixWord ++ tailWord_5284964) baseStart_5284964 baseEnd_5284964 := by
    simpa [prefixWord, tailWord_5284964, baseEnd_5284964] using wordTrace_append hprefix tailTrace_5284964
  have hstable : (prefixWord ++ tailWord_5284964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284964).length < 2 ^ (prefixWord ++ tailWord_5284964).sum := by decide
  have hdescent : baseEnd_5284964 < baseStart_5284964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5284967 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 3, 5]
def baseStart_5284967 : Nat := 118140960795 + 5284967 * 2 ^ 59
def prefixEnd_5284967 : Nat := 4983230072969 + 3 ^ 40 * 5284967 * 2
def baseEnd_5284967 : Nat := 904576104716776425335795

theorem tailTrace_5284967 : CollatzResearch.WordTrace tailWord_5284967 prefixEnd_5284967 904576104716776425335795 := by
  unfold tailWord_5284967
  simp only [CollatzResearch.WordTrace]
  refine ⟨192758582244474634349013155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128505721496316422899342103 192758582244474634349013155)
  ·
    refine ⟨289137873366711951523519733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192758582244474634349013155 289137873366711951523519733)
    ·
      refine ⟨27106675628129245455329975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 289137873366711951523519733 27106675628129245455329975)
      ·
        refine ⟨40660013442193868182994963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27106675628129245455329975 40660013442193868182994963)
        ·
          refine ⟨60990020163290802274492445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40660013442193868182994963 60990020163290802274492445)
          ·
            refine ⟨22871257561234050852934667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60990020163290802274492445 22871257561234050852934667)
            ·
              refine ⟨34306886341851076279402001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22871257561234050852934667 34306886341851076279402001)
              ·
                refine ⟨25730164756388307209551501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34306886341851076279402001 25730164756388307209551501)
                ·
                  refine ⟨9648811783645615203581813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25730164756388307209551501 9648811783645615203581813)
                  ·
                    refine ⟨904576104716776425335795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9648811783645615203581813 904576104716776425335795)
                    ·
                      rfl

theorem cell23_5284967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_5284967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5284967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5284967 prefixEnd_5284967 := by exact prefixLift 5284967
  have htrace : WordTrace (prefixWord ++ tailWord_5284967) baseStart_5284967 baseEnd_5284967 := by
    simpa [prefixWord, tailWord_5284967, baseEnd_5284967] using wordTrace_append hprefix tailTrace_5284967
  have hstable : (prefixWord ++ tailWord_5284967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5284967).length < 2 ^ (prefixWord ++ tailWord_5284967).sum := by decide
  have hdescent : baseEnd_5284967 < baseStart_5284967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5284967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285001 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 1, 5]
def baseStart_5285001 : Nat := 118140960795 + 5285001 * 2 ^ 59
def prefixEnd_5285001 : Nat := 4983230072969 + 3 ^ 40 * 5285001 * 2
def baseEnd_5285001 : Nat := 904581924164194047660743

theorem tailTrace_5285001 : CollatzResearch.WordTrace tailWord_5285001 prefixEnd_5285001 904581924164194047660743 := by
  unfold tailWord_5285001
  simp only [CollatzResearch.WordTrace]
  refine ⟨192759822326351458155750857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128506548217567638770500571 192759822326351458155750857)
  ·
    refine ⟨144569866744763593616813143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192759822326351458155750857 144569866744763593616813143)
    ·
      refine ⟨216854800117145390425219715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144569866744763593616813143 216854800117145390425219715)
      ·
        refine ⟨325282200175718085637829573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216854800117145390425219715 325282200175718085637829573)
        ·
          refine ⟨60990412532947141057093045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325282200175718085637829573 60990412532947141057093045)
          ·
            refine ⟨5717851174963794474102473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60990412532947141057093045 5717851174963794474102473)
            ·
              refine ⟨4288388381222845855576855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5717851174963794474102473 4288388381222845855576855)
              ·
                refine ⟨6432582571834268783365283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288388381222845855576855 6432582571834268783365283)
                ·
                  refine ⟨9648873857751403175047925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432582571834268783365283 9648873857751403175047925)
                  ·
                    refine ⟨904581924164194047660743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9648873857751403175047925 904581924164194047660743)
                    ·
                      rfl

theorem cell23_5285001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 1, 5].length) (baseStart_5285001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285001 prefixEnd_5285001 := by exact prefixLift 5285001
  have htrace : WordTrace (prefixWord ++ tailWord_5285001) baseStart_5285001 baseEnd_5285001 := by
    simpa [prefixWord, tailWord_5285001, baseEnd_5285001] using wordTrace_append hprefix tailTrace_5285001
  have hstable : (prefixWord ++ tailWord_5285001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285001).length < 2 ^ (prefixWord ++ tailWord_5285001).sum := by decide
  have hdescent : baseEnd_5285001 < baseStart_5285001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285031 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 1, 6]
def baseStart_5285031 : Nat := 118140960795 + 5285031 * 2 ^ 59
def prefixEnd_5285031 : Nat := 4983230072969 + 3 ^ 40 * 5285031 * 2
def baseEnd_5285031 : Nat := 904587058970739008535697

theorem tailTrace_5285031 : CollatzResearch.WordTrace tailWord_5285031 prefixEnd_5285031 904587058970739008535697 := by
  unfold tailWord_5285031
  simp only [CollatzResearch.WordTrace]
  refine ⟨192760916516242773279342947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128507277677495182186228631 192760916516242773279342947)
  ·
    refine ⟨289141374774364159919014421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192760916516242773279342947 289141374774364159919014421)
    ·
      refine ⟨13553501942548319996203801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 289141374774364159919014421 13553501942548319996203801)
      ·
        refine ⟨10165126456911239997152851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13553501942548319996203801 10165126456911239997152851)
        ·
          refine ⟨15247689685366859995729277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10165126456911239997152851 15247689685366859995729277)
          ·
            refine ⟨5717883632012572498398479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15247689685366859995729277 5717883632012572498398479)
            ·
              refine ⟨8576825448018858747597719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717883632012572498398479 8576825448018858747597719)
              ·
                refine ⟨12865238172028288121396579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8576825448018858747597719 12865238172028288121396579)
                ·
                  refine ⟨19297857258042432182094869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12865238172028288121396579 19297857258042432182094869)
                  ·
                    refine ⟨904587058970739008535697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19297857258042432182094869 904587058970739008535697)
                    ·
                      rfl

theorem cell23_5285031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_5285031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285031 prefixEnd_5285031 := by exact prefixLift 5285031
  have htrace : WordTrace (prefixWord ++ tailWord_5285031) baseStart_5285031 baseEnd_5285031 := by
    simpa [prefixWord, tailWord_5285031, baseEnd_5285031] using wordTrace_append hprefix tailTrace_5285031
  have hstable : (prefixWord ++ tailWord_5285031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285031).length < 2 ^ (prefixWord ++ tailWord_5285031).sum := by decide
  have hdescent : baseEnd_5285031 < baseStart_5285031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285041 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5285041 : Nat := 118140960795 + 5285041 * 2 ^ 59
def prefixEnd_5285041 : Nat := 4983230072969 + 3 ^ 40 * 5285041 * 2
def baseEnd_5285041 : Nat := 2713766311718761986482045

theorem tailTrace_5285041 : CollatzResearch.WordTrace tailWord_5285041 prefixEnd_5285041 2713766311718761986482045 := by
  unfold tailWord_5285041
  simp only [CollatzResearch.WordTrace]
  refine ⟨192761281246206544987206977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128507520830804363324804651 192761281246206544987206977)
  ·
    refine ⟨144570960934654908740405233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192761281246206544987206977 144570960934654908740405233)
    ·
      refine ⟨108428220700991181555303925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144570960934654908740405233 108428220700991181555303925)
      ·
        refine ⟨10165145690717923270809743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108428220700991181555303925 10165145690717923270809743)
        ·
          refine ⟨15247718536076884906214615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10165145690717923270809743 15247718536076884906214615)
          ·
            refine ⟨22871577804115327359321923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15247718536076884906214615 22871577804115327359321923)
            ·
              refine ⟨34307366706172991038982885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22871577804115327359321923 34307366706172991038982885)
              ·
                refine ⟨6432631257407435819809291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34307366706172991038982885 6432631257407435819809291)
                ·
                  refine ⟨9648946886111153729713937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432631257407435819809291 9648946886111153729713937)
                  ·
                    refine ⟨7236710164583365297285453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9648946886111153729713937 7236710164583365297285453)
                    ·
                      refine ⟨2713766311718761986482045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236710164583365297285453 2713766311718761986482045)
                      ·
                        rfl

theorem cell23_5285041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5285041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285041 prefixEnd_5285041 := by exact prefixLift 5285041
  have htrace : WordTrace (prefixWord ++ tailWord_5285041) baseStart_5285041 baseEnd_5285041 := by
    simpa [prefixWord, tailWord_5285041, baseEnd_5285041] using wordTrace_append hprefix tailTrace_5285041
  have hstable : (prefixWord ++ tailWord_5285041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285041).length < 2 ^ (prefixWord ++ tailWord_5285041).sum := by decide
  have hdescent : baseEnd_5285041 < baseStart_5285041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285087 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 2, 6]
def baseStart_5285087 : Nat := 118140960795 + 5285087 * 2 ^ 59
def prefixEnd_5285087 : Nat := 4983230072969 + 3 ^ 40 * 5285087 * 2
def baseEnd_5285087 : Nat := 904596643942956268835611

theorem tailTrace_5285087 : CollatzResearch.WordTrace tailWord_5285087 prefixEnd_5285087 904596643942956268835611 := by
  unfold tailWord_5285087
  simp only [CollatzResearch.WordTrace]
  refine ⟨192762959004039894843381515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128508639336026596562254343 192762959004039894843381515)
  ·
    refine ⟨289144438506059842265072273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192762959004039894843381515 289144438506059842265072273)
    ·
      refine ⟨216858328879544881698804205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289144438506059842265072273 216858328879544881698804205)
      ·
        refine ⟨81321873329829330637051577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216858328879544881698804205 81321873329829330637051577)
        ·
          refine ⟨60991404997371997977788683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81321873329829330637051577 60991404997371997977788683)
          ·
            refine ⟨91487107496057996966683025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60991404997371997977788683 91487107496057996966683025)
            ·
              refine ⟨68615330622043497725012269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91487107496057996966683025 68615330622043497725012269)
              ·
                refine ⟨25730748983266311646879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68615330622043497725012269 25730748983266311646879601)
                ·
                  refine ⟨19298061737449733735159701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25730748983266311646879601 19298061737449733735159701)
                  ·
                    refine ⟨904596643942956268835611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19298061737449733735159701 904596643942956268835611)
                    ·
                      rfl

theorem cell23_5285087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_5285087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285087 prefixEnd_5285087 := by exact prefixLift 5285087
  have htrace : WordTrace (prefixWord ++ tailWord_5285087) baseStart_5285087 baseEnd_5285087 := by
    simpa [prefixWord, tailWord_5285087, baseEnd_5285087] using wordTrace_append hprefix tailTrace_5285087
  have hstable : (prefixWord ++ tailWord_5285087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285087).length < 2 ^ (prefixWord ++ tailWord_5285087).sum := by decide
  have hdescent : baseEnd_5285087 < baseStart_5285087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285088 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 2, 1, 3]
def baseStart_5285088 : Nat := 118140960795 + 5285088 * 2 ^ 59
def prefixEnd_5285088 : Nat := 4983230072969 + 3 ^ 40 * 5285088 * 2
def baseEnd_5285088 : Nat := 2713790445309523302594329

theorem tailTrace_5285088 : CollatzResearch.WordTrace tailWord_5285088 prefixEnd_5285088 2713790445309523302594329 := by
  unfold tailWord_5285088
  simp only [CollatzResearch.WordTrace]
  refine ⟨96381497738518136007083959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128508663651357514676111945 96381497738518136007083959)
  ·
    refine ⟨144572246607777204010625939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96381497738518136007083959 144572246607777204010625939)
    ·
      refine ⟨216858369911665806015938909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144572246607777204010625939 216858369911665806015938909)
      ·
        refine ⟨81321888716874677255977091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216858369911665806015938909 81321888716874677255977091)
        ·
          refine ⟨121982833075312015883965637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81321888716874677255977091 121982833075312015883965637)
          ·
            refine ⟨22871781201621002978243557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121982833075312015883965637 22871781201621002978243557)
            ·
              refine ⟨4288458975303938058420667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22871781201621002978243557 4288458975303938058420667)
              ·
                refine ⟨6432688462955907087631001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288458975303938058420667 6432688462955907087631001)
                ·
                  refine ⟨4824516347216930315723251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6432688462955907087631001 4824516347216930315723251)
                  ·
                    refine ⟨7236774520825395473584877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4824516347216930315723251 7236774520825395473584877)
                    ·
                      refine ⟨2713790445309523302594329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236774520825395473584877 2713790445309523302594329)
                      ·
                        rfl

theorem cell23_5285088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_5285088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285088 prefixEnd_5285088 := by exact prefixLift 5285088
  have htrace : WordTrace (prefixWord ++ tailWord_5285088) baseStart_5285088 baseEnd_5285088 := by
    simpa [prefixWord, tailWord_5285088, baseEnd_5285088] using wordTrace_append hprefix tailTrace_5285088
  have hstable : (prefixWord ++ tailWord_5285088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285088).length < 2 ^ (prefixWord ++ tailWord_5285088).sum := by decide
  have hdescent : baseEnd_5285088 < baseStart_5285088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285098 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_5285098 : Nat := 118140960795 + 5285098 * 2 ^ 59
def prefixEnd_5285098 : Nat := 4983230072969 + 3 ^ 40 * 5285098 * 2
def baseEnd_5285098 : Nat := 2713795580116068263469283

theorem tailTrace_5285098 : CollatzResearch.WordTrace tailWord_5285098 prefixEnd_5285098 2713795580116068263469283 := by
  unfold tailWord_5285098
  simp only [CollatzResearch.WordTrace]
  refine ⟨48190840051750010930507987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128508906804666695814687965 48190840051750010930507987)
  ·
    refine ⟨72286260077625016395761981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48190840051750010930507987 72286260077625016395761981)
    ·
      refine ⟨27107347529109381148410743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72286260077625016395761981 27107347529109381148410743)
      ·
        refine ⟨40661021293664071722616115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27107347529109381148410743 40661021293664071722616115)
        ·
          refine ⟨60991531940496107583924173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40661021293664071722616115 60991531940496107583924173)
          ·
            refine ⟨22871824477686040343971565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60991531940496107583924173 22871824477686040343971565)
            ·
              refine ⟨8576934179132265128989337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22871824477686040343971565 8576934179132265128989337)
              ·
                refine ⟨6432700634349198846742003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8576934179132265128989337 6432700634349198846742003)
                ·
                  refine ⟨9649050951523798270113005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432700634349198846742003 9649050951523798270113005)
                  ·
                    refine ⟨3618394106821424351292377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9649050951523798270113005 3618394106821424351292377)
                    ·
                      refine ⟨2713795580116068263469283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618394106821424351292377 2713795580116068263469283)
                      ·
                        rfl

theorem cell23_5285098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_5285098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285098 prefixEnd_5285098 := by exact prefixLift 5285098
  have htrace : WordTrace (prefixWord ++ tailWord_5285098) baseStart_5285098 baseEnd_5285098 := by
    simpa [prefixWord, tailWord_5285098, baseEnd_5285098] using wordTrace_append hprefix tailTrace_5285098
  have hstable : (prefixWord ++ tailWord_5285098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285098).length < 2 ^ (prefixWord ++ tailWord_5285098).sum := by decide
  have hdescent : baseEnd_5285098 < baseStart_5285098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285138 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5285138 : Nat := 118140960795 + 5285138 * 2 ^ 59
def prefixEnd_5285138 : Nat := 4983230072969 + 3 ^ 40 * 5285138 * 2
def baseEnd_5285138 : Nat := 904605373114082702323033

theorem tailTrace_5285138 : CollatzResearch.WordTrace tailWord_5285138 prefixEnd_5285138 904605373114082702323033 := by
  unfold tailWord_5285138
  simp only [CollatzResearch.WordTrace]
  refine ⟨48191204781713782638372017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128509879417903420368992045 48191204781713782638372017)
  ·
    refine ⟨36143403586285336978779013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48191204781713782638372017 36143403586285336978779013)
    ·
      refine ⟨6776888172428500683521065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36143403586285336978779013 6776888172428500683521065)
      ·
        refine ⟨5082666129321375512640799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6776888172428500683521065 5082666129321375512640799)
        ·
          refine ⟨7623999193982063268961199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5082666129321375512640799 7623999193982063268961199)
          ·
            refine ⟨11435998790973094903441799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7623999193982063268961199 11435998790973094903441799)
            ·
              refine ⟨17153998186459642355162699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11435998790973094903441799 17153998186459642355162699)
              ·
                refine ⟨25730997279689463532744049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17153998186459642355162699 25730997279689463532744049)
                ·
                  refine ⟨19298247959767097649558037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25730997279689463532744049 19298247959767097649558037)
                  ·
                    refine ⟨904605373114082702323033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19298247959767097649558037 904605373114082702323033)
                    ·
                      rfl

theorem cell23_5285138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5285138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285138 prefixEnd_5285138 := by exact prefixLift 5285138
  have htrace : WordTrace (prefixWord ++ tailWord_5285138) baseStart_5285138 baseEnd_5285138 := by
    simpa [prefixWord, tailWord_5285138, baseEnd_5285138] using wordTrace_append hprefix tailTrace_5285138
  have hstable : (prefixWord ++ tailWord_5285138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285138).length < 2 ^ (prefixWord ++ tailWord_5285138).sum := by decide
  have hdescent : baseEnd_5285138 < baseStart_5285138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285144 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_5285144 : Nat := 118140960795 + 5285144 * 2 ^ 59
def prefixEnd_5285144 : Nat := 4983230072969 + 3 ^ 40 * 5285144 * 2
def baseEnd_5285144 : Nat := 2713819200226175083494071

theorem tailTrace_5285144 : CollatzResearch.WordTrace tailWord_5285144 prefixEnd_5285144 2713819200226175083494071 := by
  unfold tailWord_5285144
  simp only [CollatzResearch.WordTrace]
  refine ⟨96382518982416696789103243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128510025309888929052137657 96382518982416696789103243)
  ·
    refine ⟨144573778473625045183654865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96382518982416696789103243 144573778473625045183654865)
    ·
      refine ⟨108430333855218783887741149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144573778473625045183654865 108430333855218783887741149)
      ·
        refine ⟨40661375195707043957902931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108430333855218783887741149 40661375195707043957902931)
        ·
          refine ⟨60992062793560565936854397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40661375195707043957902931 60992062793560565936854397)
          ·
            refine ⟨22872023547585212226320399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60992062793560565936854397 22872023547585212226320399)
            ·
              refine ⟨34308035321377818339480599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22872023547585212226320399 34308035321377818339480599)
              ·
                refine ⟨51462052982066727509220899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34308035321377818339480599 51462052982066727509220899)
                ·
                  refine ⟨77193079473100091263831349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51462052982066727509220899 77193079473100091263831349)
                  ·
                    refine ⟨7236851200603133555984189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77193079473100091263831349 7236851200603133555984189)
                    ·
                      refine ⟨2713819200226175083494071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236851200603133555984189 2713819200226175083494071)
                      ·
                        rfl

theorem cell23_5285144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_5285144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285144 prefixEnd_5285144 := by exact prefixLift 5285144
  have htrace : WordTrace (prefixWord ++ tailWord_5285144) baseStart_5285144 baseEnd_5285144 := by
    simpa [prefixWord, tailWord_5285144, baseEnd_5285144] using wordTrace_append hprefix tailTrace_5285144
  have hstable : (prefixWord ++ tailWord_5285144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285144).length < 2 ^ (prefixWord ++ tailWord_5285144).sum := by decide
  have hdescent : baseEnd_5285144 < baseStart_5285144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285147 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 1, 7]
def baseStart_5285147 : Nat := 118140960795 + 5285147 * 2 ^ 59
def prefixEnd_5285147 : Nat := 4983230072969 + 3 ^ 40 * 5285147 * 2
def baseEnd_5285147 : Nat := 904606913556046190585519

theorem tailTrace_5285147 : CollatzResearch.WordTrace tailWord_5285147 prefixEnd_5285147 904606913556046190585519 := by
  unfold tailWord_5285147
  simp only [CollatzResearch.WordTrace]
  refine ⟨192765147383822525090565695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128510098255881683393710463 192765147383822525090565695)
  ·
    refine ⟨289147721075733787635848543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192765147383822525090565695 289147721075733787635848543)
    ·
      refine ⟨433721581613600681453772815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289147721075733787635848543 433721581613600681453772815)
      ·
        refine ⟨650582372420401022180659223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433721581613600681453772815 650582372420401022180659223)
        ·
          refine ⟨975873558630601533270988835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650582372420401022180659223 975873558630601533270988835)
          ·
            refine ⟨1463810337945902299906483253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975873558630601533270988835 1463810337945902299906483253)
            ·
              refine ⟨137232219182428340616232805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1463810337945902299906483253 137232219182428340616232805)
              ·
                refine ⟨25731041096705313865543651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137232219182428340616232805 25731041096705313865543651)
                ·
                  refine ⟨38596561645057970798315477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25731041096705313865543651 38596561645057970798315477)
                  ·
                    refine ⟨904606913556046190585519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38596561645057970798315477 904606913556046190585519)
                    ·
                      rfl

theorem cell23_5285147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_5285147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285147 prefixEnd_5285147 := by exact prefixLift 5285147
  have htrace : WordTrace (prefixWord ++ tailWord_5285147) baseStart_5285147 baseEnd_5285147 := by
    simpa [prefixWord, tailWord_5285147, baseEnd_5285147] using wordTrace_append hprefix tailTrace_5285147
  have hstable : (prefixWord ++ tailWord_5285147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285147).length < 2 ^ (prefixWord ++ tailWord_5285147).sum := by decide
  have hdescent : baseEnd_5285147 < baseStart_5285147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285184 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_5285184 : Nat := 118140960795 + 5285184 * 2 ^ 59
def prefixEnd_5285184 : Nat := 4983230072969 + 3 ^ 40 * 5285184 * 2
def baseEnd_5285184 : Nat := 2713839739452354926993887

theorem tailTrace_5285184 : CollatzResearch.WordTrace tailWord_5285184 prefixEnd_5285184 2713839739452354926993887 := by
  unfold tailWord_5285184
  simp only [CollatzResearch.WordTrace]
  refine ⟨96383248442344240204831303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128510997923125653606441737 96383248442344240204831303)
  ·
    refine ⟨144574872663516360307246955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96383248442344240204831303 144574872663516360307246955)
    ·
      refine ⟨216862308995274540460870433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144574872663516360307246955 216862308995274540460870433)
      ·
        refine ⟨162646731746455905345652825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216862308995274540460870433 162646731746455905345652825)
        ·
          refine ⟨121985048809841929009239619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162646731746455905345652825 121985048809841929009239619)
          ·
            refine ⟨182977573214762893513859429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121985048809841929009239619 182977573214762893513859429)
            ·
              refine ⟨34308294977768042533848643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 182977573214762893513859429 34308294977768042533848643)
              ·
                refine ⟨51462442466652063800772965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34308294977768042533848643 51462442466652063800772965)
                ·
                  refine ⟨9649207962497261962644931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51462442466652063800772965 9649207962497261962644931)
                  ·
                    refine ⟨14473811943745892943967397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9649207962497261962644931 14473811943745892943967397)
                    ·
                      refine ⟨2713839739452354926993887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14473811943745892943967397 2713839739452354926993887)
                      ·
                        rfl

theorem cell23_5285184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_5285184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285184 prefixEnd_5285184 := by exact prefixLift 5285184
  have htrace : WordTrace (prefixWord ++ tailWord_5285184) baseStart_5285184 baseEnd_5285184 := by
    simpa [prefixWord, tailWord_5285184, baseEnd_5285184] using wordTrace_append hprefix tailTrace_5285184
  have hstable : (prefixWord ++ tailWord_5285184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285184).length < 2 ^ (prefixWord ++ tailWord_5285184).sum := by decide
  have hdescent : baseEnd_5285184 < baseStart_5285184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285201 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 2, 4, 2]
def baseStart_5285201 : Nat := 118140960795 + 5285201 * 2 ^ 59
def prefixEnd_5285201 : Nat := 4983230072969 + 3 ^ 40 * 5285201 * 2
def baseEnd_5285201 : Nat := 2713848468623481360481309

theorem tailTrace_5285201 : CollatzResearch.WordTrace tailWord_5285201 prefixEnd_5285201 2713848468623481360481309 := by
  unfold tailWord_5285201
  simp only [CollatzResearch.WordTrace]
  refine ⟨192767116925626892313031457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128511411283751261542020971 192767116925626892313031457)
  ·
    refine ⟨144575337694220169234773593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192767116925626892313031457 144575337694220169234773593)
    ·
      refine ⟨108431503270665126926080195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144575337694220169234773593 108431503270665126926080195)
      ·
        refine ⟨162647254905997690389120293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108431503270665126926080195 162647254905997690389120293)
        ·
          refine ⟨30496360294874566947960055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162647254905997690389120293 30496360294874566947960055)
          ·
            refine ⟨45744540442311850421940083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30496360294874566947960055 45744540442311850421940083)
            ·
              refine ⟨68616810663467775632910125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45744540442311850421940083 68616810663467775632910125)
              ·
                refine ⟨25731303998800415862341297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68616810663467775632910125 25731303998800415862341297)
                ·
                  refine ⟨19298477999100311896755973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25731303998800415862341297 19298477999100311896755973)
                  ·
                    refine ⟨3618464624831308480641745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19298477999100311896755973 3618464624831308480641745)
                    ·
                      refine ⟨2713848468623481360481309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618464624831308480641745 2713848468623481360481309)
                      ·
                        rfl

theorem cell23_5285201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 4, 2].length) (baseStart_5285201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285201 prefixEnd_5285201 := by exact prefixLift 5285201
  have htrace : WordTrace (prefixWord ++ tailWord_5285201) baseStart_5285201 baseEnd_5285201 := by
    simpa [prefixWord, tailWord_5285201, baseEnd_5285201] using wordTrace_append hprefix tailTrace_5285201
  have hstable : (prefixWord ++ tailWord_5285201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285201).length < 2 ^ (prefixWord ++ tailWord_5285201).sum := by decide
  have hdescent : baseEnd_5285201 < baseStart_5285201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285221 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_5285221 : Nat := 118140960795 + 5285221 * 2 ^ 59
def prefixEnd_5285221 : Nat := 4983230072969 + 3 ^ 40 * 5285221 * 2
def baseEnd_5285221 : Nat := 2713858738236571282231217

theorem tailTrace_5285221 : CollatzResearch.WordTrace tailWord_5285221 prefixEnd_5285221 2713858738236571282231217 := by
  unfold tailWord_5285221
  simp only [CollatzResearch.WordTrace]
  refine ⟨192767846385554435728759517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128511897590369623819173011 192767846385554435728759517)
  ·
    refine ⟨72287942394582913398284819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 192767846385554435728759517 72287942394582913398284819)
    ·
      refine ⟨108431913591874370097427229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72287942394582913398284819 108431913591874370097427229)
      ·
        refine ⟨40661967596952888786535211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108431913591874370097427229 40661967596952888786535211)
        ·
          refine ⟨60992951395429333179802817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40661967596952888786535211 60992951395429333179802817)
          ·
            refine ⟨45744713546571999884852113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60992951395429333179802817 45744713546571999884852113)
            ·
              refine ⟨34308535159928999913639085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45744713546571999884852113 34308535159928999913639085)
              ·
                refine ⟨12865700684973374967614657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34308535159928999913639085 12865700684973374967614657)
                ·
                  refine ⟨9649275513730031225710993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12865700684973374967614657 9649275513730031225710993)
                  ·
                    refine ⟨7236956635297523419283245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9649275513730031225710993 7236956635297523419283245)
                    ·
                      refine ⟨2713858738236571282231217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7236956635297523419283245 2713858738236571282231217)
                      ·
                        rfl

theorem cell23_5285221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_5285221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285221 prefixEnd_5285221 := by exact prefixLift 5285221
  have htrace : WordTrace (prefixWord ++ tailWord_5285221) baseStart_5285221 baseEnd_5285221 := by
    simpa [prefixWord, tailWord_5285221, baseEnd_5285221] using wordTrace_append hprefix tailTrace_5285221
  have hstable : (prefixWord ++ tailWord_5285221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285221).length < 2 ^ (prefixWord ++ tailWord_5285221).sum := by decide
  have hdescent : baseEnd_5285221 < baseStart_5285221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285245 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_5285245 : Nat := 118140960795 + 5285245 * 2 ^ 59
def prefixEnd_5285245 : Nat := 4983230072969 + 3 ^ 40 * 5285245 * 2
def baseEnd_5285245 : Nat := 904623687257426396110369

theorem tailTrace_5285245 : CollatzResearch.WordTrace tailWord_5285245 prefixEnd_5285245 904623687257426396110369 := by
  unfold tailWord_5285245
  simp only [CollatzResearch.WordTrace]
  refine ⟨192768721737467487827633189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128512481158311658551755459 192768721737467487827633189)
  ·
    refine ⟨36144135325775153967681223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 192768721737467487827633189 36144135325775153967681223)
    ·
      refine ⟨54216202988662730951521835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36144135325775153967681223 54216202988662730951521835)
      ·
        refine ⟨81324304482994096427282753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54216202988662730951521835 81324304482994096427282753)
        ·
          refine ⟨60993228362245572320462065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81324304482994096427282753 60993228362245572320462065)
          ·
            refine ⟨45744921271684179240346549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60993228362245572320462065 45744921271684179240346549)
            ·
              refine ⟨4288586369220391803782489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45744921271684179240346549 4288586369220391803782489)
              ·
                refine ⟨3216439776915293852836867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4288586369220391803782489 3216439776915293852836867)
                ·
                  refine ⟨4824659665372940779255301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3216439776915293852836867 4824659665372940779255301)
                  ·
                    refine ⟨904623687257426396110369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4824659665372940779255301 904623687257426396110369)
                    ·
                      rfl

theorem cell23_5285245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_5285245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285245 prefixEnd_5285245 := by exact prefixLift 5285245
  have htrace : WordTrace (prefixWord ++ tailWord_5285245) baseStart_5285245 baseEnd_5285245 := by
    simpa [prefixWord, tailWord_5285245, baseEnd_5285245] using wordTrace_append hprefix tailTrace_5285245
  have hstable : (prefixWord ++ tailWord_5285245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285245).length < 2 ^ (prefixWord ++ tailWord_5285245).sum := by decide
  have hdescent : baseEnd_5285245 < baseStart_5285245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285304 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_5285304 : Nat := 118140960795 + 5285304 * 2 ^ 59
def prefixEnd_5285304 : Nat := 4983230072969 + 3 ^ 40 * 5285304 * 2
def baseEnd_5285304 : Nat := 2713901357130894457493335

theorem tailTrace_5285304 : CollatzResearch.WordTrace tailWord_5285304 prefixEnd_5285304 2713901357130894457493335 := by
  unfold tailWord_5285304
  simp only [CollatzResearch.WordTrace]
  refine ⟨96385436822126870452015483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128513915762835827269353977 96385436822126870452015483)
  ·
    refine ⟨144578155233190305678023225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96385436822126870452015483 144578155233190305678023225)
    ·
      refine ⟨108433616424892729258517419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144578155233190305678023225 108433616424892729258517419)
      ·
        refine ⟨162650424637339093887776129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108433616424892729258517419 162650424637339093887776129)
        ·
          refine ⟨121987818478004320415832097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162650424637339093887776129 121987818478004320415832097)
          ·
            refine ⟨91490863858503240311874073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121987818478004320415832097 91490863858503240311874073)
            ·
              refine ⟨68618147893877430233905555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91490863858503240311874073 68618147893877430233905555)
              ·
                refine ⟨102927221840816145350858333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68618147893877430233905555 102927221840816145350858333)
                ·
                  refine ⟨38597708190306054506571875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102927221840816145350858333 38597708190306054506571875)
                  ·
                    refine ⟨57896562285459081759857813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38597708190306054506571875 57896562285459081759857813)
                    ·
                      refine ⟨2713901357130894457493335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57896562285459081759857813 2713901357130894457493335)
                      ·
                        rfl

theorem cell23_5285304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_5285304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285304 prefixEnd_5285304 := by exact prefixLift 5285304
  have htrace : WordTrace (prefixWord ++ tailWord_5285304) baseStart_5285304 baseEnd_5285304 := by
    simpa [prefixWord, tailWord_5285304, baseEnd_5285304] using wordTrace_append hprefix tailTrace_5285304
  have hstable : (prefixWord ++ tailWord_5285304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285304).length < 2 ^ (prefixWord ++ tailWord_5285304).sum := by decide
  have hdescent : baseEnd_5285304 < baseStart_5285304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285344 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_5285344 : Nat := 118140960795 + 5285344 * 2 ^ 59
def prefixEnd_5285344 : Nat := 4983230072969 + 3 ^ 40 * 5285344 * 2
def baseEnd_5285344 : Nat := 904640632119024766997717

theorem tailTrace_5285344 : CollatzResearch.WordTrace tailWord_5285344 prefixEnd_5285344 904640632119024766997717 := by
  unfold tailWord_5285344
  simp only [CollatzResearch.WordTrace]
  refine ⟨96386166282054413867743543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128514888376072551823658057 96386166282054413867743543)
  ·
    refine ⟨144579249423081620801615315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96386166282054413867743543 144579249423081620801615315)
    ·
      refine ⟨216868874134622431202422973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144579249423081620801615315 216868874134622431202422973)
      ·
        refine ⟨81325827800483411700908615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216868874134622431202422973 81325827800483411700908615)
        ·
          refine ⟨121988741700725117551362923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81325827800483411700908615 121988741700725117551362923)
          ·
            refine ⟨182983112551087676327044385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121988741700725117551362923 182983112551087676327044385)
            ·
              refine ⟨137237334413315757245283289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182983112551087676327044385 137237334413315757245283289)
              ·
                refine ⟨102928000809986817933962467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137237334413315757245283289 102928000809986817933962467)
                ·
                  refine ⟨154392001214980226900943701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102928000809986817933962467 154392001214980226900943701)
                  ·
                    refine ⟨904640632119024766997717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 154392001214980226900943701 904640632119024766997717)
                    ·
                      rfl

theorem cell23_5285344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_5285344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285344 prefixEnd_5285344 := by exact prefixLift 5285344
  have htrace : WordTrace (prefixWord ++ tailWord_5285344) baseStart_5285344 baseEnd_5285344 := by
    simpa [prefixWord, tailWord_5285344, baseEnd_5285344] using wordTrace_append hprefix tailTrace_5285344
  have hstable : (prefixWord ++ tailWord_5285344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285344).length < 2 ^ (prefixWord ++ tailWord_5285344).sum := by decide
  have hdescent : baseEnd_5285344 < baseStart_5285344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285345 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_5285345 : Nat := 118140960795 + 5285345 * 2 ^ 59
def prefixEnd_5285345 : Nat := 4983230072969 + 3 ^ 40 * 5285345 * 2
def baseEnd_5285345 : Nat := 2713922409837728797080647

theorem tailTrace_5285345 : CollatzResearch.WordTrace tailWord_5285345 prefixEnd_5285345 2713922409837728797080647 := by
  unfold tailWord_5285345
  simp only [CollatzResearch.WordTrace]
  refine ⟨192772369037105204906273489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128514912691403469937515659 192772369037105204906273489)
  ·
    refine ⟨144579276777828903679705117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192772369037105204906273489 144579276777828903679705117)
    ·
      refine ⟨54217228791685838879889419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144579276777828903679705117 54217228791685838879889419)
      ·
        refine ⟨81325843187528758319834129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54217228791685838879889419 81325843187528758319834129)
        ·
          refine ⟨60994382390646568739875597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81325843187528758319834129 60994382390646568739875597)
          ·
            refine ⟨22872893396492463277453349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60994382390646568739875597 22872893396492463277453349)
            ·
              refine ⟨4288667511842336864522503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22872893396492463277453349 4288667511842336864522503)
              ·
                refine ⟨6433001267763505296783755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4288667511842336864522503 6433001267763505296783755)
                ·
                  refine ⟨9649501901645257945175633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433001267763505296783755 9649501901645257945175633)
                  ·
                    refine ⟨7237126426233943458881725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9649501901645257945175633 7237126426233943458881725)
                    ·
                      refine ⟨2713922409837728797080647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237126426233943458881725 2713922409837728797080647)
                      ·
                        rfl

theorem cell23_5285345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_5285345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285345 prefixEnd_5285345 := by exact prefixLift 5285345
  have htrace : WordTrace (prefixWord ++ tailWord_5285345) baseStart_5285345 baseEnd_5285345 := by
    simpa [prefixWord, tailWord_5285345, baseEnd_5285345] using wordTrace_append hprefix tailTrace_5285345
  have hstable : (prefixWord ++ tailWord_5285345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285345).length < 2 ^ (prefixWord ++ tailWord_5285345).sum := by decide
  have hdescent : baseEnd_5285345 < baseStart_5285345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285382 : List Nat := [6, 2, 1, 1, 2, 1, 1, 9]
def baseStart_5285382 : Nat := 118140960795 + 5285382 * 2 ^ 59
def prefixEnd_5285382 : Nat := 4983230072969 + 3 ^ 40 * 5285382 * 2
def baseEnd_5285382 : Nat := 100516348467479450085851

theorem tailTrace_5285382 : CollatzResearch.WordTrace tailWord_5285382 prefixEnd_5285382 100516348467479450085851 := by
  unfold tailWord_5285382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024178704311598757042825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128515812358647440150246933 6024178704311598757042825)
  ·
    refine ⟨4518134028233699067782119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6024178704311598757042825 4518134028233699067782119)
    ·
      refine ⟨6777201042350548601673179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518134028233699067782119 6777201042350548601673179)
      ·
        refine ⟨10165801563525822902509769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6777201042350548601673179 10165801563525822902509769)
        ·
          refine ⟨7624351172644367176882327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10165801563525822902509769 7624351172644367176882327)
          ·
            refine ⟨11436526758966550765323491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624351172644367176882327 11436526758966550765323491)
            ·
              refine ⟨17154790138449826147985237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11436526758966550765323491 17154790138449826147985237)
              ·
                refine ⟨100516348467479450085851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17154790138449826147985237 100516348467479450085851)
                ·
                  rfl

theorem cell23_5285382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_5285382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285382 prefixEnd_5285382 := by exact prefixLift 5285382
  have htrace : WordTrace (prefixWord ++ tailWord_5285382) baseStart_5285382 baseEnd_5285382 := by
    simpa [prefixWord, tailWord_5285382, baseEnd_5285382] using wordTrace_append hprefix tailTrace_5285382
  have hstable : (prefixWord ++ tailWord_5285382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285382).length < 2 ^ (prefixWord ++ tailWord_5285382).sum := by decide
  have hdescent : baseEnd_5285382 < baseStart_5285382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285385 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 1, 3, 2]
def baseStart_5285385 : Nat := 118140960795 + 5285385 * 2 ^ 59
def prefixEnd_5285385 : Nat := 4983230072969 + 3 ^ 40 * 5285385 * 2
def baseEnd_5285385 : Nat := 2713942949063908640580463

theorem tailTrace_5285385 : CollatzResearch.WordTrace tailWord_5285385 prefixEnd_5285385 2713942949063908640580463 := by
  unfold tailWord_5285385
  simp only [CollatzResearch.WordTrace]
  refine ⟨192773827956960291737729609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128515885304640194491819739 192773827956960291737729609)
  ·
    refine ⟨144580370967720218803297207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192773827956960291737729609 144580370967720218803297207)
    ·
      refine ⟨216870556451580328204945811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144580370967720218803297207 216870556451580328204945811)
      ·
        refine ⟨325305834677370492307418717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216870556451580328204945811 325305834677370492307418717)
        ·
          refine ⟨121989688004013934615282019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 325305834677370492307418717 121989688004013934615282019)
          ·
            refine ⟨182984532006020901922923029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121989688004013934615282019 182984532006020901922923029)
            ·
              refine ⟨8577399937782229777637017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182984532006020901922923029 8577399937782229777637017)
              ·
                refine ⟨6433049953336672333227763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8577399937782229777637017 6433049953336672333227763)
                ·
                  refine ⟨9649574930005008499841645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6433049953336672333227763 9649574930005008499841645)
                  ·
                    refine ⟨3618590598751878187440617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9649574930005008499841645 3618590598751878187440617)
                    ·
                      refine ⟨2713942949063908640580463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618590598751878187440617 2713942949063908640580463)
                      ·
                        rfl

theorem cell23_5285385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 3, 2].length) (baseStart_5285385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285385 prefixEnd_5285385 := by exact prefixLift 5285385
  have htrace : WordTrace (prefixWord ++ tailWord_5285385) baseStart_5285385 baseEnd_5285385 := by
    simpa [prefixWord, tailWord_5285385, baseEnd_5285385] using wordTrace_append hprefix tailTrace_5285385
  have hstable : (prefixWord ++ tailWord_5285385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285385).length < 2 ^ (prefixWord ++ tailWord_5285385).sum := by decide
  have hdescent : baseEnd_5285385 < baseStart_5285385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285418 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_5285418 : Nat := 118140960795 + 5285418 * 2 ^ 59
def prefixEnd_5285418 : Nat := 4983230072969 + 3 ^ 40 * 5285418 * 2
def baseEnd_5285418 : Nat := 2713959893925507011467811

theorem tailTrace_5285418 : CollatzResearch.WordTrace tailWord_5285418 prefixEnd_5285418 2713959893925507011467811 := by
  unfold tailWord_5285418
  simp only [CollatzResearch.WordTrace]
  refine ⟨48193757891460184593420227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128516687710560492249120605 48193757891460184593420227)
  ·
    refine ⟨72290636837190276890130341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48193757891460184593420227 72290636837190276890130341)
    ·
      refine ⟨13554494406973176916899439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72290636837190276890130341 13554494406973176916899439)
      ·
        refine ⟨20331741610459765375349159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13554494406973176916899439 20331741610459765375349159)
        ·
          refine ⟨30497612415689648063023739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20331741610459765375349159 30497612415689648063023739)
          ·
            refine ⟨45746418623534472094535609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30497612415689648063023739 45746418623534472094535609)
            ·
              refine ⟨34309813967650854070901707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45746418623534472094535609 34309813967650854070901707)
              ·
                refine ⟨51464720951476281106352561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34309813967650854070901707 51464720951476281106352561)
                ·
                  refine ⟨38598540713607210829764421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51464720951476281106352561 38598540713607210829764421)
                  ·
                    refine ⟨7237226383801352030580829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38598540713607210829764421 7237226383801352030580829)
                    ·
                      refine ⟨2713959893925507011467811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7237226383801352030580829 2713959893925507011467811)
                      ·
                        rfl

theorem cell23_5285418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_5285418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285418 prefixEnd_5285418 := by exact prefixLift 5285418
  have htrace : WordTrace (prefixWord ++ tailWord_5285418) baseStart_5285418 baseEnd_5285418 := by
    simpa [prefixWord, tailWord_5285418, baseEnd_5285418] using wordTrace_append hprefix tailTrace_5285418
  have hstable : (prefixWord ++ tailWord_5285418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285418).length < 2 ^ (prefixWord ++ tailWord_5285418).sum := by decide
  have hdescent : baseEnd_5285418 < baseStart_5285418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285432 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 2, 2, 2]
def baseStart_5285432 : Nat := 118140960795 + 5285432 * 2 ^ 59
def prefixEnd_5285432 : Nat := 4983230072969 + 3 ^ 40 * 5285432 * 2
def baseEnd_5285432 : Nat := 2713967082654669956692747

theorem tailTrace_5285432 : CollatzResearch.WordTrace tailWord_5285432 prefixEnd_5285432 2713967082654669956692747 := by
  unfold tailWord_5285432
  simp only [CollatzResearch.WordTrace]
  refine ⟨96387771093895009382345275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128517028125193345843127033 96387771093895009382345275)
  ·
    refine ⟨144581656640842514073517913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96387771093895009382345275 144581656640842514073517913)
    ·
      refine ⟨108436242480631885555138435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144581656640842514073517913 108436242480631885555138435)
      ·
        refine ⟨162654363720947828332707653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108436242480631885555138435 162654363720947828332707653)
        ·
          refine ⟨30497693197677717812382685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 162654363720947828332707653 30497693197677717812382685)
          ·
            refine ⟨11436634949129144179643507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30497693197677717812382685 11436634949129144179643507)
            ·
              refine ⟨17154952423693716269465261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11436634949129144179643507 17154952423693716269465261)
              ·
                refine ⟨6433107158885143601049473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17154952423693716269465261 6433107158885143601049473)
                ·
                  refine ⟨4824830369163857700787105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6433107158885143601049473 4824830369163857700787105)
                  ·
                    refine ⟨3618622776872893275590329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4824830369163857700787105 3618622776872893275590329)
                    ·
                      refine ⟨2713967082654669956692747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3618622776872893275590329 2713967082654669956692747)
                      ·
                        rfl

theorem cell23_5285432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_5285432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285432 prefixEnd_5285432 := by exact prefixLift 5285432
  have htrace : WordTrace (prefixWord ++ tailWord_5285432) baseStart_5285432 baseEnd_5285432 := by
    simpa [prefixWord, tailWord_5285432, baseEnd_5285432] using wordTrace_append hprefix tailTrace_5285432
  have hstable : (prefixWord ++ tailWord_5285432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285432).length < 2 ^ (prefixWord ++ tailWord_5285432).sum := by decide
  have hdescent : baseEnd_5285432 < baseStart_5285432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285471 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_5285471 : Nat := 118140960795 + 5285471 * 2 ^ 59
def prefixEnd_5285471 : Nat := 4983230072969 + 3 ^ 40 * 5285471 * 2
def baseEnd_5285471 : Nat := 2713987108400195304105067

theorem tailTrace_5285471 : CollatzResearch.WordTrace tailWord_5285471 prefixEnd_5285471 2713987108400195304105067 := by
  unfold tailWord_5285471
  simp only [CollatzResearch.WordTrace]
  refine ⟨192776964634648728425360267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128517976423099152283573511 192776964634648728425360267)
  ·
    refine ⟨289165446951973092638040401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 192776964634648728425360267 289165446951973092638040401)
    ·
      refine ⟨216874085213979819478530301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 289165446951973092638040401 216874085213979819478530301)
      ·
        refine ⟨81327781955242432304448863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 216874085213979819478530301 81327781955242432304448863)
        ·
          refine ⟨121991672932863648456673295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81327781955242432304448863 121991672932863648456673295)
          ·
            refine ⟨182987509399295472685009943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121991672932863648456673295 182987509399295472685009943)
            ·
              refine ⟨274481264098943209027514915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182987509399295472685009943 274481264098943209027514915)
              ·
                refine ⟨411721896148414813541272373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274481264098943209027514915 411721896148414813541272373)
                ·
                  refine ⟨38598927763913888769494285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 411721896148414813541272373 38598927763913888769494285)
                  ·
                    refine ⟨14474597911467708288560357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38598927763913888769494285 14474597911467708288560357)
                    ·
                      refine ⟨2713987108400195304105067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14474597911467708288560357 2713987108400195304105067)
                      ·
                        rfl

theorem cell23_5285471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_5285471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285471 prefixEnd_5285471 := by exact prefixLift 5285471
  have htrace : WordTrace (prefixWord ++ tailWord_5285471) baseStart_5285471 baseEnd_5285471 := by
    simpa [prefixWord, tailWord_5285471, baseEnd_5285471] using wordTrace_append hprefix tailTrace_5285471
  have hstable : (prefixWord ++ tailWord_5285471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285471).length < 2 ^ (prefixWord ++ tailWord_5285471).sum := by decide
  have hdescent : baseEnd_5285471 < baseStart_5285471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285505 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_5285505 : Nat := 118140960795 + 5285505 * 2 ^ 59
def prefixEnd_5285505 : Nat := 4983230072969 + 3 ^ 40 * 5285505 * 2
def baseEnd_5285505 : Nat := 2714004566742448171079911

theorem tailTrace_5285505 : CollatzResearch.WordTrace tailWord_5285505 prefixEnd_5285505 2714004566742448171079911 := by
  unfold tailWord_5285505
  simp only [CollatzResearch.WordTrace]
  refine ⟨192778204716525552232097969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128518803144350368154731979 192778204716525552232097969)
  ·
    refine ⟨144583653537394164174073477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192778204716525552232097969 144583653537394164174073477)
    ·
      refine ⟨27109435038261405782638777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144583653537394164174073477 27109435038261405782638777)
      ·
        refine ⟨20332076278696054336979083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27109435038261405782638777 20332076278696054336979083)
        ·
          refine ⟨30498114418044081505468625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20332076278696054336979083 30498114418044081505468625)
          ·
            refine ⟨22873585813533061129101469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30498114418044081505468625 22873585813533061129101469)
            ·
              refine ⟨8577594680074897923413051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22873585813533061129101469 8577594680074897923413051)
              ·
                refine ⟨12866392020112346885119577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577594680074897923413051 12866392020112346885119577)
                ·
                  refine ⟨9649794015084260163839683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12866392020112346885119577 9649794015084260163839683)
                  ·
                    refine ⟨14474691022626390245759525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9649794015084260163839683 14474691022626390245759525)
                    ·
                      refine ⟨2714004566742448171079911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14474691022626390245759525 2714004566742448171079911)
                      ·
                        rfl

theorem cell23_5285505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_5285505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285505 prefixEnd_5285505 := by exact prefixLift 5285505
  have htrace : WordTrace (prefixWord ++ tailWord_5285505) baseStart_5285505 baseEnd_5285505 := by
    simpa [prefixWord, tailWord_5285505, baseEnd_5285505] using wordTrace_append hprefix tailTrace_5285505
  have hstable : (prefixWord ++ tailWord_5285505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285505).length < 2 ^ (prefixWord ++ tailWord_5285505).sum := by decide
  have hdescent : baseEnd_5285505 < baseStart_5285505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285518 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_5285518 : Nat := 118140960795 + 5285518 * 2 ^ 59
def prefixEnd_5285518 : Nat := 4983230072969 + 3 ^ 40 * 5285518 * 2
def baseEnd_5285518 : Nat := 2714011241990956620217351

theorem tailTrace_5285518 : CollatzResearch.WordTrace tailWord_5285518 prefixEnd_5285518 2714011241990956620217351 := by
  unfold tailWord_5285518
  simp only [CollatzResearch.WordTrace]
  refine ⟨24097334858184806931540151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 128519119243652303634880805 24097334858184806931540151)
  ·
    refine ⟨36146002287277210397310227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24097334858184806931540151 36146002287277210397310227)
    ·
      refine ⟨54219003430915815595965341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36146002287277210397310227 54219003430915815595965341)
      ·
        refine ⟨20332126286593430848487003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54219003430915815595965341 20332126286593430848487003)
        ·
          refine ⟨30498189429890146272730505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20332126286593430848487003 30498189429890146272730505)
          ·
            refine ⟨22873642072417609704547879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30498189429890146272730505 22873642072417609704547879)
            ·
              refine ⟨34310463108626414556821819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22873642072417609704547879 34310463108626414556821819)
              ·
                refine ⟨51465694662939621835232729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34310463108626414556821819 51465694662939621835232729)
                ·
                  refine ⟨38599270997204716376424547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51465694662939621835232729 38599270997204716376424547)
                  ·
                    refine ⟨57898906495807074564636821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38599270997204716376424547 57898906495807074564636821)
                    ·
                      refine ⟨2714011241990956620217351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57898906495807074564636821 2714011241990956620217351)
                      ·
                        rfl

theorem cell23_5285518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_5285518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285518 prefixEnd_5285518 := by exact prefixLift 5285518
  have htrace : WordTrace (prefixWord ++ tailWord_5285518) baseStart_5285518 baseEnd_5285518 := by
    simpa [prefixWord, tailWord_5285518, baseEnd_5285518] using wordTrace_append hprefix tailTrace_5285518
  have hstable : (prefixWord ++ tailWord_5285518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285518).length < 2 ^ (prefixWord ++ tailWord_5285518).sum := by decide
  have hdescent : baseEnd_5285518 < baseStart_5285518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5285528 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 8]
def baseStart_5285528 : Nat := 118140960795 + 5285528 * 2 ^ 59
def prefixEnd_5285528 : Nat := 4983230072969 + 3 ^ 40 * 5285528 * 2
def baseEnd_5285528 : Nat := 301557375199722397899145

theorem tailTrace_5285528 : CollatzResearch.WordTrace tailWord_5285528 prefixEnd_5285528 301557375199722397899145 := by
  unfold tailWord_5285528
  simp only [CollatzResearch.WordTrace]
  refine ⟨96389521797721113580092619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128519362396961484773456825 96389521797721113580092619)
  ·
    refine ⟨144584282696581670370138929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96389521797721113580092619 144584282696581670370138929)
    ·
      refine ⟨108438212022436252777604197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144584282696581670370138929 108438212022436252777604197)
      ·
        refine ⟨20332164754206797395800787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108438212022436252777604197 20332164754206797395800787)
        ·
          refine ⟨30498247131310196093701181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20332164754206797395800787 30498247131310196093701181)
          ·
            refine ⟨11436842674241323535137943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30498247131310196093701181 11436842674241323535137943)
            ·
              refine ⟨17155264011361985302706915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11436842674241323535137943 17155264011361985302706915)
              ·
                refine ⟨25732896017042977954060373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17155264011361985302706915 25732896017042977954060373)
                ·
                  refine ⟨301557375199722397899145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25732896017042977954060373 301557375199722397899145)
                  ·
                    rfl

theorem cell23_5285528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_5285528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5285528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5285528 prefixEnd_5285528 := by exact prefixLift 5285528
  have htrace : WordTrace (prefixWord ++ tailWord_5285528) baseStart_5285528 baseEnd_5285528 := by
    simpa [prefixWord, tailWord_5285528, baseEnd_5285528] using wordTrace_append hprefix tailTrace_5285528
  have hstable : (prefixWord ++ tailWord_5285528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5285528).length < 2 ^ (prefixWord ++ tailWord_5285528).sum := by decide
  have hdescent : baseEnd_5285528 < baseStart_5285528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5285528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
